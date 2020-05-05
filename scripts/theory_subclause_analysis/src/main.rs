use benchmark_runner::*;
use itertools::*;
use std::collections::*;
use std::fmt;
// use async_std::io::*;
use async_std::prelude::*;
use async_trait::*;
use std::cmp;
use std::io::*;
use std::sync::*;

type Map<K, V> = BTreeMap<K, V>;

#[derive(Ord, PartialOrd, Hash, Eq, PartialEq, Debug, Clone)]
struct ClassType(String);

#[derive(Ord, PartialOrd, Hash, Eq, PartialEq, Debug, Clone)]
struct EqClass(String);

impl EqClass {
    fn new(s: String) -> Self { EqClass(s) }
}

#[derive(Ord, PartialOrd, Hash, Eq, PartialEq, Debug, Clone)]
struct TermResult(String);

type EqClassMap = Map<EqClass, Vec<f64>>;
struct SolverResult {
    classes: Map<ClassType, EqClassMap>,
    term_results: Map<AsBenchmark<BenchmarkResult>, TermResult>,
}

#[derive(Clone, Debug)]
struct AsBenchmark<A>(A);

impl PartialEq for AsBenchmark<BenchmarkResult> {
    fn eq(&self, other: &Self) -> bool {
        self.0.benchmark().eq(&other.0.benchmark())
    }
}

impl Eq for AsBenchmark<BenchmarkResult> {}

impl PartialOrd for AsBenchmark<BenchmarkResult> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.0.benchmark().partial_cmp(&other.0.benchmark())
    }
}

impl Ord for AsBenchmark<BenchmarkResult> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.0.benchmark().cmp(&other.0.benchmark())
    }
}

impl SolverResult {
    fn new() -> Self {
        SolverResult {
            classes: Map::new(),
            term_results: Map::new(),
        }
    }
}

struct SubclauseSummerizer {
    class_types: Mutex<Map<Solver, Arc<Mutex<SolverResult>>>>,
}

impl SubclauseSummerizer {
    fn new() -> Self {
        SubclauseSummerizer {
            class_types: Mutex::new(Map::new()),
        }
    }
}
type DynResult<A> = std::result::Result<A, Box<dyn std::error::Error>>;

#[derive(Debug)]
struct MyStringError(String);

impl std::fmt::Display for MyStringError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}", self.0)?;
        Ok(())
    }
}

impl std::error::Error for MyStringError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

#[derive(Debug)]
struct MyNoneError(Option<String>);

impl std::fmt::Display for MyNoneError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "expected something got None")?;
        if let Some(msg) = &self.0 {
            write!(fmt, ": {}", msg)?;
        }
        Ok(())
    }
}

impl std::error::Error for MyNoneError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

trait OptExt<A> {
    fn to_result(self) -> std::result::Result<A, MyNoneError>;
    fn or_err<E: std::error::Error>(self, e: E) -> std::result::Result<A, E>;
}

impl<A> OptExt<A> for Option<A> {
    fn to_result(self) -> std::result::Result<A, MyNoneError> {
        match self {
            Some(x) => Ok(x),
            None => Err(MyNoneError(None)),
        }
    }
    fn or_err<E: std::error::Error>(self, e: E) -> std::result::Result<A, E> {
        match self {
            Some(x) => Ok(x),
            None => Err(e),
        }
    }
}

const PREF_TERM_REASON: &'static str = "% Termination reason: ";

impl SubclauseSummerizer {
    fn get_solver_result(&self, res: &BenchmarkResult) -> Arc<Mutex<SolverResult>> {
        let mut lock = self.class_types.lock().unwrap();
        lock.entry(res.solver().clone())
            .or_insert_with(|| Arc::new(Mutex::new(SolverResult::new())))
            .clone()
    }
}
#[async_trait]
impl Postprocessor for SubclauseSummerizer {
    async fn process(&self, res: &BenchmarkResult) -> DynResult<()> {
        /* get right solver */
        let solver_result = self.get_solver_result(res);

        let mut cl_types = HashMap::new();
        let mut term_result = None;
        <_ as StreamExt>::try_for_each(
            &mut async_std::io::BufReader::new(res.stdout().await?).lines(),
            |l| -> DynResult<()> {
                let l = l;
                let l = l?;
                let mut split = l.split("\t");
                match split.next() {
                    Some(x) if x.starts_with(PREF_TERM_REASON) => {
                        term_result = Some(TermResult(x[PREF_TERM_REASON.len()..].to_owned()))
                    }
                    Some("[ equivalence class ]") => {
                        let class_type = ClassType(split.next().to_result()?.to_owned());
                        let class_size: usize = split.next().to_result()?.parse()?;
                        let total: usize = split.next().to_result()?.parse()?;
                        let class = EqClass::new(split.next().to_result()?.to_string());
                        let class_raw = split.next().to_result()?.to_string();

                        let tup = (class.clone(), class_type.clone());
                        if let Some(other) = cl_types.get(&tup) {
                            return Err(MyStringError(format!(
                                "duplicate entry: {:?}\n\told: {}\n\tnew: {}",
                                tup, other, class_raw
                            )))?;
                        }

                        cl_types.insert(tup, class_raw);

                        let mut solver_result = solver_result.lock().unwrap();

                        let counts: &mut Vec<f64> = solver_result
                            .classes
                            .entry(class_type)
                            .or_insert_with(|| Map::new())
                            .entry(class)
                            .or_insert_with(|| Vec::new());

                        counts.push(class_size as f64 / total as f64);
                        assert!(class_size <= total);
                    }
                    _ => (),
                }
                Ok(())
            },
        )
        .await?;

        // let mut lock = self.class_types.lock().unwrap();
        // let solver_result = lock
        //     .entry(res.solver().clone())
        //     .or_insert_with(|| SolverResult::new());

        solver_result
            .lock()
            .unwrap()
            .term_results
            .insert(AsBenchmark(res.clone()), term_result.to_result()?);

        Ok(())
    }

    fn id(&self) -> &str {
        "theory_subclause_analyser"
    }
    fn write_results(self, config: BenchmarkConfig, io: PostproIOAccess) -> DynResult<()> {
        let mut summary = io.global_out()?;
        let mut sum_line = 0;
        use std::fmt;
        let mut writeln_sum = |x: fmt::Arguments| -> std::io::Result<()> {
            std::writeln!(summary, "{:>4}| {}", sum_line, x)?;
            sum_line += 1;
            Ok(())
        };
        macro_rules! section {
            ($msg:expr) => {
                writeln_sum(format_args!(""))?;
                writeln_sum(format_args!(
                    "=================== {} ===================",
                    $msg
                ))?;
            };
        }

        let mut refutations: Map<Solver, BTreeSet<AsBenchmark<BenchmarkResult>>> = Map::new();

        /* writing first part of summary */
        section!("Termination Results");
        for (solver, s_result) in self.class_types.lock().unwrap().iter() {
            let s_result = s_result.lock().unwrap();
            /* writing to global output file */
            writeln_sum(format_args!("solver: {}", solver))?;
            writeln_sum(format_args!("\ttermination results:"))?;
            s_result
                .term_results
                .iter()
                .map(|(k, v)| (v, k))
                .into_group_map()
                .into_iter()
                .try_for_each(|(k, v)| {
                    let len = v.len();
                    if let "Refutation" = &k.0[..] {
                        refutations.insert(
                            solver.clone(),
                            v.into_iter().cloned().collect::<BTreeSet<_>>(),
                        );
                    }
                    writeln_sum(format_args!("\t\t{}: {}", k.0, len))
                })?;
        }

        {
            let ui = Ui::new(
                &"computing refutational differences",
                refutations.len() * (refutations.len() - 1) * 2,
            );

            writeln_sum(format_args!("Refutation difference:"))?;
            refutations
                .iter()
                .tuple_combinations()
                .try_for_each(|(s1, s2)| -> DynResult<()> {
                    for (s1, s2) in [(s1, s2), (s2, s1)].iter() {
                        writeln_sum(format_args!("\t{}:", s1.0))?;
                        s1.1.difference(&s2.1).try_for_each(|x| -> DynResult<()> {
                            let lns = std::io::BufReader::new(x.0.stdout_sync()?).lines();
                            let proof_lines = process_results(lns, |iter| {
                                iter.skip_while(|x| !x.starts_with("% SZS output start Proof for"))
                                    .skip(1)
                                    .take_while(|x| !x.starts_with("% SZS output end Proof for"))
                                    .count()
                            })?;

                            writeln_sum(format_args!(
                                "\t\t+ {} (lines: {})",
                                x.0.benchmark().file().to_str().to_result()?,
                                proof_lines
                            ))?;
                            Ok(())
                        })?;
                        ui.progress();
                    }
                    Ok(())
                })?;
        }

        let limit_summary = 30;
        let limit_file = 100000;
        // let limit_file = std::usize::MAX;
        assert!(limit_summary < limit_file);
        section!(format_args!("Equivalence classes (Top {})", limit_summary));

        for (solver, s_result) in self.class_types.lock().unwrap().iter() {
            let s_result = s_result.lock().unwrap();

            /* writing to per solver output file */
            let ui = Ui::new(
                &format!("processing {}", solver),
                s_result
                    .classes
                    .iter()
                    .map(|(_, classes)| classes.len().min(limit_file))
                    .sum(),
            );

            let mut sout = io.solver_out(solver)?;

            macro_rules! write_both {
                    ($( $x:tt )*) => {
                        std::writeln!(sout, $($x)*)?;
                        writeln_sum(format_args!( $($x)*))?;
                    }
                }
            let sum_class_type = |ty: &ClassType| &ty.0 == "VarsMatch_UnintVarsMatch";
            for (ty, classes) in s_result.classes.iter() {

                if sum_class_type(ty) {
                    writeln_sum(format_args!(""))?;
                    writeln_sum(format_args!("solver: {}", solver))?;
                }

                std::writeln!(sout, "")?;
                std::writeln!(sout, "class type: {}", ty.0)?;

                let cnt = config.benchmarks().len();

                ui.println("computing size...");
                let mut cont: Vec<(&EqClass, f64)> = classes
                    .iter()
                    .map(|(l, r)| (l, (r.iter().sum::<f64>() / cnt as f64)))
                    .collect();

                ui.println("integrity check...");
                let sum: f64 = cont.iter().map(|(_, perc)| perc).sum();
                ui.println(format!("summed up precentages: {}", sum));
                if (1.0f64 - sum).abs() >= 0.0001 {
                    let msg = format!("WARNING: precentages only sum up to {}", sum);
                    if sum_class_type(ty) {
                        write_both!("{}", msg);
                    } else {
                        std::writeln!(sout, "{}", msg)?;
                    }
                    ui.println(msg)
                }

                ui.println("sorting...");
                cont.sort_unstable_by(|(_, cnt_l), (_, cnt_r)| cnt_r.partial_cmp(cnt_l).unwrap());

                ui.println("writing...");
                for (i, (class, percent)) in cont.into_iter().take(limit_file).enumerate() {
                    if i < limit_summary && sum_class_type(ty) {
                        writeln_sum(format_args!("\t{:.2}\t{}", 100.0 * percent, class.0))?;
                    }
                    std::writeln!(sout, "\t{:.6}\t{}", 100.0 * percent, class.0)?;
                    ui.progress();
                }
            }
        }
        Ok(())
    }
}

fn main() -> DynResult<()> {
    benchmark_runner::main(SubclauseSummerizer::new())
}
