[![License: BSD](https://img.shields.io/badge/License-BSD%203--Clause-blue.svg)](https://opensource.org/licenses/BSD-3-Clause)
![CI](https://github.com/vprover/vampire/workflows/CI/badge.svg)

# Vampire
This is the main source repository of the [Vampire](https://vprover.github.io) project, an advanced tool for automated reasoning.
The following is for end-users of Vampire: new developers should read the [wiki](https://github.com/vprover/vampire/wiki) as well.

## Licensing
Please see LICENCE.
Note that Vampire links to some other projects with thanks:
- [MiniSat](minisat.se), a SAT solver
- [CaDiCaL](https://github.com/arminbiere/cadical), another SAT solver
- [GMP](https://gmplib.org/), for arbitrary-precision arithmetic - specifically the `mini-gmp` part
- [VIRAS](https://github.com/joe-hauns/viras/), a quantifier elimination method
- [Z3](https://github.com/Z3Prover/z3/), an SMT solver (optional)

## Download
See [releases](https://github.com/vprover/vampire/releases) - we likely have a pre-built binary for your platform.
If not, you will need to [build Vampire from source](https://github.com/vprover/vampire/wiki/Source-Build-for-Users), but this is not too onerous.

## Basic Usage
The basic usage of Vampire is to save your problem in [TPTP](https://tptp.org) format and run
```shellsession
$ vampire problem.p
```
which will run Vampire in its default mode with a 60 second time-limit.

However, consider running Vampire in _portfolio_ mode:
```shellsession
$ vampire --mode casc problem.p
```
which will try lots of different _strategies_.
This often performs better than the default mode.

If you think the problem is satisfiable then you can also run
```shellsession
$ vampire --mode casc_sat problem.p
```
which will use a set of strategies suited to satisfiable problems.

Note that all of these modes are really shortcuts for other combinations e.g. `--mode casc` is a shortcut for
```shellsession
$ vampire --mode portfolio --schedule casc --proof tptp
```

## Advanced Usage
To see a full list of options, run
```shellsession
$ vampire --show_options on
```
