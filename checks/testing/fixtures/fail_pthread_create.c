/* Inject timer-thread creation failures for the resource-error regression. */
#include <errno.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>

int pthread_create(pthread_t *thread, const pthread_attr_t *attr,
                   void *(*start)(void *), void *arg)
{
  const char *error = getenv("VAMPIRE_TEST_PTHREAD_ERROR");
  if (error && strcmp(error, "ENOMEM") == 0) return ENOMEM;
  if (error && strcmp(error, "EPERM") == 0) return EPERM;
  return EAGAIN;
}
