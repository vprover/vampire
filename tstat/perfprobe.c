/*
 * perfprobe -- can this machine read the hardware instruction counter cheaply
 * from user space, and are the counts reproducible?
 *
 * This decides whether Vampire can afford to record an instruction count on every
 * TIME_TRACE scope. Today Lib/Timer.cpp reads the counter with read(perf_fd), a
 * syscall at ~1-2us: fine for the timer thread's 1ms tick, hopeless for a scope
 * entered ~10^9 times per run. The alternative is to mmap the same fd and read the
 * counter with the rdpmc instruction, which should cost ~10ns.
 *
 * Build and run (nothing links against Vampire):
 *
 *     gcc -O2 -o perfprobe perfprobe.c -lpthread && ./perfprobe
 *
 * Reading the output:
 *   - "cap_user_rdpmc: 0" means user-space reads are unavailable; the whole design
 *     is off and we stop.
 *   - rdpmc should come out appreciably cheaper than clock_gettime. If it does not,
 *     doubling the per-scope cost is not worth it.
 *   - multiplexing (time_enabled != time_running) would make the kernel scale the
 *     count into an *estimate*, destroying the determinism that is the entire point.
 *   - the reproducibility figure is the premise of the exercise: if a fixed workload
 *     does not give a near-identical count each time, instruction counts are no
 *     better than wall clock and there is nothing to gain.
 *
 * If the machine is busy, results are still valid -- that is the point of counting
 * instructions -- but the *timing* rows will be noisy. Compare against a quiet run.
 */

#define _GNU_SOURCE
#include <errno.h>
#include <inttypes.h>
#include <linux/perf_event.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

#if !defined(__x86_64__) && !defined(__i386__)
#warning "rdpmc is x86-only; this probe will report the fallback path only"
#endif

static int perf_fd = -1;
static struct perf_event_mmap_page *perf_page = NULL;

/* ------------------------------------------------------------------ helpers */

static long perf_event_open(struct perf_event_attr *attr, pid_t pid, int cpu,
                            int group_fd, unsigned long flags)
{
  return syscall(__NR_perf_event_open, attr, pid, cpu, group_fd, flags);
}

static inline void barrier(void) { __asm__ __volatile__("" ::: "memory"); }

#if defined(__x86_64__) || defined(__i386__)
static inline uint64_t do_rdpmc(uint32_t counter)
{
  uint32_t low, high;
  __asm__ __volatile__("rdpmc" : "=a"(low), "=d"(high) : "c"(counter));
  return ((uint64_t)high << 32) | low;
}
#else
static inline uint64_t do_rdpmc(uint32_t counter) { (void)counter; return 0; }
#endif

static double now_ns(void)
{
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1e9 + ts.tv_nsec;
}

/* The syscall path Vampire uses today. */
static uint64_t read_via_syscall(void)
{
  uint64_t v = 0;
  if (read(perf_fd, &v, sizeof(v)) != sizeof(v))
    return 0;
  return v;
}

/*
 * The fast path. `pc->lock` is a seqlock the kernel bumps whenever it reschedules
 * the event (which changes `index` and `offset`), so we read the fields, do the
 * rdpmc, and retry if the lock moved underneath us.
 *
 * Returns 0 and sets *ok to 0 if the event is not currently readable this way, in
 * which case the caller must fall back to read().
 */
static inline uint64_t read_via_rdpmc(int *ok)
{
  struct perf_event_mmap_page *pc = perf_page;
  uint64_t count;
  uint32_t seq, idx;
  int64_t offset;
  uint16_t width;

  *ok = 1;
  do {
    seq = pc->lock;
    barrier();

    idx = pc->index;        /* 0 => the event is not scheduled on this CPU now */
    offset = pc->offset;    /* what it counted during previous schedulings */
    width = pc->pmc_width;

    if (!pc->cap_user_rdpmc || !idx || width == 0 || width > 64) {
      *ok = 0;
      return 0;
    }

    count = do_rdpmc(idx - 1);
    /* the hardware counter is narrower than 64 bits; sign-extend it */
    count <<= 64 - width;
    count = (uint64_t)((int64_t)count >> (64 - width));
    count += offset;

    barrier();
  } while (pc->lock != seq);

  return count;
}

static void cat_sysfile(const char *path, const char *label)
{
  FILE *f = fopen(path, "r");
  char buf[64];
  if (!f) {
    printf("  %-34s (unreadable: %s)\n", label, strerror(errno));
    return;
  }
  if (fgets(buf, sizeof buf, f)) {
    buf[strcspn(buf, "\n")] = 0;
    printf("  %-34s %s\n", label, buf);
  }
  fclose(f);
}

/* A deterministic lump of user-space work, for the reproducibility check. */
static uint64_t workload(void)
{
  volatile uint64_t acc = 0;
  for (int i = 0; i < 2000000; i++)
    acc += (uint64_t)i * 2654435761u;
  return acc;
}

/* ------------------------------------------------------------------- probes */

static void report_page(void)
{
  struct perf_event_mmap_page *pc = perf_page;
  printf("\nmmap'd metadata page\n");
  printf("  %-34s %u\n", "cap_user_rdpmc", (unsigned)pc->cap_user_rdpmc);
  printf("  %-34s %u bits\n", "pmc_width", (unsigned)pc->pmc_width);
  printf("  %-34s %u%s\n", "index", (unsigned)pc->index,
         pc->index ? "" : "   <-- event not scheduled on this CPU");
  printf("  %-34s %" PRIu64 "\n", "time_enabled", (uint64_t)pc->time_enabled);
  printf("  %-34s %" PRIu64 "%s\n", "time_running", (uint64_t)pc->time_running,
         pc->time_enabled == pc->time_running ? "   (no multiplexing)"
                                              : "   <-- MULTIPLEXED, counts get scaled");

  if (!pc->cap_user_rdpmc)
    printf("\n  VERDICT: user-space counter reads are NOT available here.\n"
           "           Per-scope instruction counting is off the table.\n");
}

static void check_agreement(void)
{
  int ok;
  uint64_t a, b;

  printf("\ncorrectness: rdpmc vs read(perf_fd)\n");
  a = read_via_rdpmc(&ok);
  b = read_via_syscall();
  if (!ok) {
    printf("  rdpmc path unavailable (fell back)\n");
    return;
  }
  /* The syscall itself runs in the kernel and we set exclude_kernel, so the two
     reads should differ only by the handful of user instructions between them. */
  printf("  rdpmc  = %" PRIu64 "\n", a);
  printf("  read() = %" PRIu64 "   (delta %+" PRId64 ")\n", b, (int64_t)(b - a));
  if (b < a || b - a > 100000)
    printf("  <-- SUSPICIOUS: these should be within a few hundred of each other\n");
}

#define BENCH(label, expr)                                                     \
  do {                                                                         \
    const int N = 200000;                                                      \
    volatile uint64_t sink = 0;                                                \
    double t0, t1;                                                             \
    for (int i = 0; i < N / 10; i++) sink += (expr); /* warm up */              \
    t0 = now_ns();                                                             \
    for (int i = 0; i < N; i++) sink += (expr);                                \
    t1 = now_ns();                                                             \
    printf("  %-34s %8.1f ns\n", label, (t1 - t0) / N - empty);                \
    (void)sink;                                                                \
  } while (0)

static void benchmark(void)
{
  int ok;
  double empty;
  {
    const int N = 200000;
    volatile uint64_t sink = 0;
    double t0 = now_ns();
    for (int i = 0; i < N; i++) sink += (uint64_t)i;
    double t1 = now_ns();
    empty = (t1 - t0) / N;
    (void)sink;
  }

  printf("\ncost per read (empty-loop baseline %.1f ns already subtracted)\n", empty);
  BENCH("rdpmc (via the seqlock loop)", read_via_rdpmc(&ok));
  BENCH("clock_gettime(CLOCK_MONOTONIC)", (uint64_t)now_ns());
  {
    /* read() is ~100x slower, so use far fewer iterations */
    const int N = 20000;
    volatile uint64_t sink = 0;
    double t0 = now_ns();
    for (int i = 0; i < N; i++) sink += read_via_syscall();
    double t1 = now_ns();
    printf("  %-34s %8.1f ns\n", "read(perf_fd)  [what we do now]",
           (t1 - t0) / N - empty);
    (void)sink;
  }
  printf("\n  A TIME_TRACE scope takes two reads (entry and exit). Adding instruction\n"
         "  counts alongside time therefore costs 2x the rdpmc figure per scope.\n");
}

static void check_reproducibility(void)
{
  const int R = 7;
  uint64_t counts[R];
  int ok;

  printf("\nreproducibility: instructions for an identical workload, %d runs\n", R);
  for (int r = 0; r < R; r++) {
    uint64_t before = read_via_rdpmc(&ok);
    if (!ok) before = read_via_syscall();
    workload();
    uint64_t after = read_via_rdpmc(&ok);
    if (!ok) after = read_via_syscall();
    counts[r] = after - before;
  }

  uint64_t lo = counts[0], hi = counts[0];
  double sum = 0;
  for (int r = 0; r < R; r++) {
    if (counts[r] < lo) lo = counts[r];
    if (counts[r] > hi) hi = counts[r];
    sum += (double)counts[r];
  }
  printf("  min %" PRIu64 "  max %" PRIu64 "  mean %.0f\n", lo, hi, sum / R);
  printf("  spread %.4f%%%s\n", 100.0 * (double)(hi - lo) / (double)lo,
         (hi - lo) * 1000 < lo ? "   (deterministic enough)"
                               : "   <-- too noisy, the premise fails");
}

/*
 * Empirical check of the constraint that shapes the design: rdpmc reads the PMU
 * register of whatever CPU the *caller* runs on, so a thread other than the one the
 * event is attached to gets a number that has nothing to do with our counter -- and
 * gets it silently, because `index` may well be non-zero. This is why the timer
 * thread must keep using read().
 */
static void *other_thread(void *arg)
{
  int ok;
  uint64_t *out = (uint64_t *)arg;
  out[0] = read_via_rdpmc(&ok);
  out[1] = ok;
  out[2] = read_via_syscall();
  return NULL;
}

static void check_cross_thread(void)
{
  pthread_t th;
  uint64_t out[3] = {0, 0, 0};
  int ok;
  uint64_t mine = read_via_rdpmc(&ok);

  printf("\ncross-thread read (expected to be wrong -- documents why timer_thread\n"
         "must keep using read())\n");
  if (pthread_create(&th, NULL, other_thread, out) != 0) {
    printf("  (could not create thread)\n");
    return;
  }
  pthread_join(th, NULL);
  printf("  this thread, rdpmc   = %" PRIu64 "\n", mine);
  printf("  other thread, rdpmc  = %" PRIu64 "  (path taken: %s)\n", out[0],
         out[1] ? "rdpmc" : "fell back");
  printf("  other thread, read() = %" PRIu64 "  (this one is always correct)\n", out[2]);
}

/* --------------------------------------------------------------------- main */

int main(void)
{
  struct perf_event_attr attr;
  long page_size = sysconf(_SC_PAGESIZE);

  printf("perfprobe: can we read the instruction counter cheaply from user space?\n");
  printf("\nkernel settings\n");
  cat_sysfile("/proc/sys/kernel/perf_event_paranoid", "perf_event_paranoid");
  cat_sysfile("/sys/devices/cpu/rdpmc", "/sys/devices/cpu/rdpmc");
  cat_sysfile("/proc/sys/kernel/perf_user_access", "perf_user_access (arm64 only)");
  printf("  %-34s %ld\n", "online CPUs", sysconf(_SC_NPROCESSORS_ONLN));

  /* exactly what Lib/Timer.cpp opens today */
  memset(&attr, 0, sizeof attr);
  attr.type = PERF_TYPE_HARDWARE;
  attr.size = sizeof attr;
  attr.config = PERF_COUNT_HW_INSTRUCTIONS;
  attr.disabled = 1;
  attr.exclude_kernel = 1;
  attr.exclude_hv = 1;

  perf_fd = perf_event_open(&attr, 0 /* this thread */, -1, -1, 0);
  if (perf_fd == -1) {
    fprintf(stderr, "\nperf_event_open failed: %s\n", strerror(errno));
    fprintf(stderr, "If this says 'Permission denied', the admin can allow it with\n"
                    "  sudo sysctl -w kernel.perf_event_paranoid=-1\n");
    return 1;
  }
  ioctl(perf_fd, PERF_EVENT_IOC_RESET, 0);
  ioctl(perf_fd, PERF_EVENT_IOC_ENABLE, 0);

  /* One page is enough: we only want the metadata page, not a sample ring buffer. */
  perf_page = mmap(NULL, page_size, PROT_READ, MAP_SHARED, perf_fd, 0);
  if (perf_page == MAP_FAILED) {
    fprintf(stderr, "\nmmap of the perf fd failed: %s\n", strerror(errno));
    fprintf(stderr, "The counter still works via read(); only the fast path is out.\n");
    return 1;
  }

  /* touch the counter once so the kernel has scheduled the event */
  workload();

  report_page();
  check_agreement();
  benchmark();
  check_reproducibility();
  check_cross_thread();

  printf("\nsummary: per-scope instruction counting is viable iff cap_user_rdpmc is 1,\n"
         "there is no multiplexing, rdpmc is clearly cheaper than clock_gettime, and\n"
         "the reproducibility spread is well under 0.1%%.\n");

  munmap(perf_page, page_size);
  close(perf_fd);
  return 0;
}
