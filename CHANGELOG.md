# Changelog

## 0.1.0 — 2026-10-15

First public release. Property-based testing for Nim: generate random
inputs, shrink failures to minimal counterexamples, reproduce everything
from a printed seed. Single module (`src/falsify.nim`), zero dependencies
beyond the Nim stdlib, Nim >= 2.0.0.

**Core**
- Seeded xorshift-style RNG (`Rng`, `initRng`, `next`, `below`); the failure
  line prints `seed`, case index, and minimal input, and re-running with the
  printed seed reproduces the identical stream and counterexample.
- `forAll` driver: runs `n` cases, reports `FAIL` with the minimal shrunk
  input, returns `bool` so suites continue past failures. Assertion failures
  (`Defect`) in the property or the code under test are reported as
  property failures, not unhandled crashes.

**Generators**
- Edge-biased primitives: `genBool`, `genInt`, `genFloat` (with opt-in
  NaN/Inf and subnormal edge cases), `genChar`, `genString`, `genSeq`.
- Choice: `genFrequency`, `genOneOf`, `genElements`.
- Collection sampling: `genPermutation`, `genShuffle`, `genSubseq`,
  `genUniqueInts`.
- Constrained: `genSuchThat` (rejection sampling) and `shrinkSuchThat`
  (shrinking that stays inside the constraint).
- Combinators: `genMap`, `genBind`, `genPair`, `genTriple` (with
  elementwise tuple shrinking).
- Sized/recursive: `genSized`, `genRecursive`.
- Enums: `genEnum[T]` with `shrinkEnum`.

**Shrinkers**
- `shrinkInt`, `shrinkFloat`, `shrinkChar`, `shrinkString`, `shrinkSeq`,
  `shrinkPair`, `shrinkTriple`, `shrinkSuchThat`, `shrinkEnum`,
  `shrinkCmdSeq` (for command sequences).

**Runner options** (via `FalsifySettings`, with named profiles through
`defineProfile`/`withProfile`)
- Regression corpus: saved failing seeds replayed before the random sweep.
- Explicit examples: literal always-run cases alongside generated ones.
- Preconditions: `assume` with a `maxDiscards` budget.
- Per-case deadline (`deadlineMs`) and shrink-phase budget (`maxShrinks`).
- Coverage: `classify` + `cover` with `CoverReq` minimums, so a passing
  sweep reports what it exercised.
- Health checks: warn (or fail) on slow, oversized, or degenerate sweeps.
- Targeted generation: `target` steers mutation toward higher-scoring
  inputs, Hypothesis-style.
- Verbosity levels: quiet / normal / verbose output.

**Stateful testing**
- `runCommands`: model-based testing of stateful systems, with command
  generation, model/system step functions, `replayCmds` for manual
  sequence replay, and `shrinkCmdSeq`.
