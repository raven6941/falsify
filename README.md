# falsify — property-based testing for Nim

Falsify your properties: generate random inputs, shrink failures to minimal
counterexamples, reproduce everything from a seed.

```nim
import falsify

const Seed = 424242'u64  # fixed in CI; vary locally when hunting flakes

var r = initRng(Seed)
let ok = forAll("reverse-twice", r, 200,
  proc(r: var Rng): seq[int] =
    r.genSeq(20, proc(r: var Rng): int = r.genInt(-100, 100)),
  proc(s: seq[int]): bool =
    s.reversed.reversed == s,
  proc(s: seq[int]): seq[seq[int]] = s.shrinkSeq(shrinkInt))
if not ok: quit(1)
```

On failure you get the case index and the shrunk minimal input:

```
FAIL [reverse-twice]: seed: 424242, case 37, minimal input: @[3, -1]
```

The printed seed is the replay recipe: re-run the property with
`initRng(424242)` (same case count, generator, property, shrinker) and you
get the identical stream and the identical minimal counterexample.

An `assert` (or any defect) in the property or the code under test is a
failure, not a crash: it is reported with the seed + minimal input like
any other failure, and `forAll` returns `false` so the suite continues.

## Edge-biased generation

Uniform random generation is boring: `genInt(-1000, 1000)` almost never
produces 0 or the boundaries, and those are where bugs live. So the
generators are biased toward edge cases (Hypothesis and QuickCheck do the
same):

- `genInt(lo, hi)`: with probability 1/4, drawn uniformly from the
  interesting values in range — `lo`, `hi`, and 0, −1, 1 when in range;
  otherwise uniform over `[lo, hi]`.
- `genFloat(lo, hi)`: with probability 1/4, returns `lo` or 0.0 (when 0.0
  lies in `[lo, hi)`); otherwise uniform over `[lo, hi)`.
- `genString` / `genSeq`: with probability 1/4, the length is 0 or 1
  (empty and single-element cases get their turn); otherwise uniform over
  `[0, maxLen]`.

The bias is part of the stream, not a coin flipped outside it: same seed
still means same sequence, bit for bit. But note the distributions changed
in 0.2.0 — a seed that produced one stream under 0.1.0 produces a different
stream now.

## Weighted and categorical choice

`genFrequency` picks among generator *expressions* with probability
proportional to their weights — "mostly normal cases, sometimes the weird
one":

```nim
let v = r.genFrequency([(9, r.genInt(0, 100)),    # the common case
                        (1, r.genInt(-100, 100))]) # the weird one
```

`genOneOf([g0, g1, g2])` is uniform choice among generator expressions;
`genElements(xs)` picks a value from `xs`.

`genOneOf` and `genFrequency` are macros, not procs, and this is
deliberate: a proc taking a *collection* of generator procs cannot accept
inline lambdas in Nim. The compiler infers `{.noSideEffect, gcsafe.}` on a
lambda (mutating a `var` parameter doesn't count as a side effect for this
analysis), so it never matches a plain `proc` parameter — and a lambda that
captures a local infers `{.closure.}`, matching nothing at all. Taking
expressions keeps the natural call syntax, evaluates exactly one branch per
draw (laziness: unchosen generators never run, never advance the RNG), and
lets generators close over locals. `genElements` takes values, so it stays
a plain proc.

Empty inputs are usage errors: `genOneOf([])` / `genFrequency([])` fail at
compile time; `genElements([])` and non-positive weights fail at run time
(`doAssert`).

## Constrained generation

`genSuchThat(gen, pred)` draws from `gen` until `pred` holds — even numbers,
strings matching a shape, pairs in order:

```nim
let even = r.genSuchThat(proc(r: var Rng): int = r.genInt(0, 99),
                         proc(x: int): bool = x mod 2 == 0)
```

After `maxRetries` draws (default 100) without success it raises `ValueError`
— and that error is advice, not a knob: a predicate that exhausts the cap
means the generator is too narrow for the predicate, or the predicate too
strict for the generator. Prefer narrowing the generator — building the
constraint into generation (e.g. `2 * r.genInt(0, 49)` for evens) — over
heavy filtering. Filtering a wide generator is the retry-hunt equivalent of
an unseeded stream: it works until it silently doesn't.

## Composing generators

Generators compose like QuickCheck's `Gen`: `genMap` is `fmap`, `genBind`
is `>>=`.

```nim
let even = r.genMap(proc(r: var Rng): int = r.genInt(0, 49),
                    proc(x: int): int = 2 * x)

let payload = r.genBind(proc(r: var Rng): int = r.genInt(1, 8),
                        proc(r: var Rng, n: int): seq[bool] =
                          r.genSeq(n, genBool))
```

`genMap(r, gen, f)` draws once from `gen` and applies `f` — the draws are
exactly `gen`'s draws, so mapping never perturbs the stream. `genBind(r,
gen, k)` draws `x` from `gen` and then runs the continuation generator
`k(x)`: the size-then-payload pattern above draws a length, then a payload
of exactly that length.

The threading is the point: instead of *capturing* a local in a lambda
(which infers `{.closure.}` and won't match a plain `proc` parameter —
the same rule as every other `proc` parameter in this library), you
*generate* the value and thread it as an argument. `f` and `k` must not
capture locals; named top-level procs and non-capturing lambdas work.

## Sized and recursive generation

Recursive data (trees, ASTs, terms) needs a generator that terminates and
grows across a run. Two pieces:

- `genSized(r, f)` runs `f` with the ambient size (`r.size`). `forAll`
  grows the ambient size linearly from 0 to ~100 across its cases
  (QuickCheck semantics: early cases are small, late cases explore deep
  structures). Outside `forAll` the size is 0 unless you set `r.size`
  yourself.
- `genRecursive(r, leaf, branch)` builds a recursive generator from a leaf
  generator and a branch generator. With probability `size/(size+1)` the
  branch is taken, else the leaf — small sizes stay shallow, large sizes
  grow. Each recursion halves the size and size 0 always takes the leaf,
  so generation provably terminates; `branch` receives `sub`, a generator
  for one child subtree at the halved size (call it once per child).

```nim
type Tree = ref object
  kids: seq[Tree]  # empty = leaf

proc genTree(r: var Rng): Tree =
  r.genRecursive(
    proc(r: var Rng): Tree = Tree(kids: @[]),
    proc(r: var Rng, sub: proc(r: var Rng): Tree): Tree =
      Tree(kids: @[sub(r), sub(r)]))
```

One typing note: `sub` is a closure (it captures the recursion context),
so its parameter type carries `{.closure.}` — your `branch` lambda still
declares it as a plain `proc` and everything typechecks, since Nim converts
non-capturing procs to closure type implicitly.

## Multi-input properties

`forAll` takes a single generator of a single value — but a pair (or
triple) *is* that value for multi-input properties: algebraic laws,
relations between generated values, sorted-pair checks.

```nim
let ok = forAll("add-commutes", r, 200,
  proc(r: var Rng): (int, int) =
    r.genPair(proc(r: var Rng): int = r.genInt(-100, 100),
              proc(r: var Rng): int = r.genInt(-100, 100)),
  proc(p: (int, int)): bool = p[0] + p[1] == p[1] + p[0],
  proc(p: (int, int)): seq[(int, int)] =
    p.shrinkPair(shrinkInt, shrinkInt))
```

`genPair` / `genTriple` build the tuples; `shrinkPair` / `shrinkTriple`
shrink them elementwise (QuickCheck-tuple semantics: one component at a
time, left first, each holding the others fixed, most-aggressive first),
so a failing pair shrinks to a minimal failing pair. Greedy shrinking
minimizes every component it can while the property still fails — e.g.
the broken property `p[0] + p[1] <= 7` shrinks to `(8, 0)`.

## The seed discipline

- Check in a **fixed seed** so CI is reproducible.
- When hunting a flaky property locally, loop seeds until one fails, then
  hard-code that seed as a regression case.
- A failing `forAll` prints its seed (also available as `r.seed` after
  `initRng`); copy it into a regression case to replay the exact failure.
- `initRng(0)` maps to a fixed nonzero default (never accidentally unseeded);
  `r.seed` records the effective seed after that mapping.

The replay is a first-class part of the property, not a manual re-run:
`forAll` takes an optional `regressions` list of seeds, replayed *before*
the random sweep. Each replay runs the identical stream (same seed → same
cases → same failure, same minimal counterexample), shrinking and
reporting exactly like a fresh failure. A regression failure aborts the
`forAll` and returns false, like a sweep failure; the sweep only runs
after every replay passes. The list is explicit and checked in — no
hidden on-disk database (Hypothesis's example database, minus the magic
directory):

```nim
let ok = forAll("reverse-twice", r, 200, gen, prop, shrink,
  regressions = @[424242'u64, 987654321'u64])
```

## Preconditions

Sometimes the property only makes sense on part of the input space —
"for all *positive* x". Pass `assume` and `forAll` discards the rest,
QuickCheck-`==>` style:

```nim
let ok = forAll("div-roundtrip", r, 200,
  proc(r: var Rng): (int, int) =
    r.genPair(proc(r: var Rng): int = r.genInt(-100, 100),
              proc(r: var Rng): int = r.genInt(-100, 100)),
  proc(p: (int, int)): bool =
    (p[0] div p[1]) * p[1] + p[0] mod p[1] == p[0],
  proc(p: (int, int)): seq[(int, int)] =
    p.shrinkPair(shrinkInt, shrinkInt),
  assume = proc(p: (int, int)): bool = p[1] != 0)
```

```
ok [div-roundtrip]: 200 cases, 3 discarded
```

A discarded case is counted and reported, never a failure, and never
classified. If discards exceed `maxDiscards` (default 500) the run aborts
with a gave-up line instead of spinning on an unsatisfiable precondition:

```
FAIL [div-roundtrip]: gave up: discarded 501 > maxDiscards 500 cases
```

An exception or defect *inside* `assume` is a programming error and fails
the run like a property failure. Discarded draws still consume RNG, so the
case stream is identical with or without `assume` — only which cases get
evaluated changes (the FAIL line's case number is the draw index in that
stream). `assume` applies to regression replays too: a replayed seed whose
case now fails `assume` is discarded, not failed — the property changed,
not the stream.

The standing advice applies: prefer narrowing the generator over heavy
filtering. A precondition that discards most cases is usually a generator
that should have produced satisfying cases directly (same guidance as
`genSuchThat`).

## Per-case deadline

A property whose single case takes minutes turns the run into a hanging
CI job with no output and no seed recipe. Pass `deadlineMs` (Hypothesis
`deadline` style) and a case that runs longer aborts the sweep:

```nim
let ok = forAll("solver-prop", r, 200, gen, prop, shrink, deadlineMs = 500)
```

```
DEADLINE [solver-prop]: case 7 took 2312.0ms > 500ms deadline, seed: 424242
```

The abort returns false — the same failure protocol as a property
failure, so the suite continues with later properties. The seed on the
line makes the run replayable, like the FAIL line's recipe. Generation
time is excluded from the measurement: the timer starts after `gen`
returns, the same convention as the `hcTooSlow` health check.

This is *cooperative*: the deadline is checked at the case boundary, so
it cannot interrupt a truly infinite loop inside the property — true
preemption needs threads, which are out of scope. What the deadline buys
is fail-fast feedback for the common slow case instead of a silent hang.
The abort skips the shrink phase on purpose: shrinking would re-run the
slow property once per candidate, which is the hang the deadline just
avoided. `deadlineMs = 0` (the default) disables it and reproduces
current behavior exactly — same seed, byte-identical output.

## Coverage

A green run says "200 cases passed" — but what *were* those cases? Pass an
optional `classify` and `forAll` prints the observed distribution after the
sweep, QuickCheck style. Here it checks that `genInt`'s edge bias is really
surfacing boundary values at the advertised rate:

```nim
let ok = forAll("int-edges", r, 200,
  proc(r: var Rng): int = r.genInt(-100, 100),
  proc(x: int): bool = x != 424242,  # the property
  classify = proc(x: int): seq[string] =
    if x in [-100, 100, 0, -1, 1]: @["edge"] else: @["bulk"])
```

```
cover [int-edges]: "bulk": 69.0% (138/200)
cover [int-edges]: "edge": 31.0% (62/200)
ok [int-edges]: 200 cases
```

The numbers are seed-deterministic like everything else — same seed, same
table, bit for bit. Classification covers the random sweep only (regression
replays are fixed cases; counting them would distort the distribution), and
each tag counts at most once per case. Classifying never perturbs the
stream: `classify` receives only the generated value, never the RNG, so the
case stream is identical with or without it.

For a hard guarantee instead of a printed table, add `cover`:

```nim
  cover = @[("edge", 15.0)])  # at least 15% of cases must be edges
```

A missed requirement fails the run with the evidence attached:

```
FAIL [int-edges]: coverage shortfall: "edge": 31.0% < required 50.0%
```

`cover` without `classify` is a usage error (fails loud). This is the
analogue of QuickCheck's `cover` / Hypothesis's `target`: it turns "we
exercised the edge cases" from a hope into a checked claim.

## Health checks

A green sweep can still be degenerate: every case finishing in a
microsecond means the generator found a trivial corner; every case taking
seconds means CI can't afford the suite; a precondition discarding 95% of
draws means the property is barely being tested. Pass `health` (default
`defaultHealth()`) and `forAll` watches for these shapes — Hypothesis
`HealthCheck` style — and prints a line per tripped check:

```
HEALTH [slow-prop]: too-slow: mean case time 63.2ms > 50.0ms
HEALTH [tiny]: few-examples: only 5 cases evaluated < 10 minimum
```

The four checks:

- `hcTooSlow` — mean per-case property time (generation excluded) above
  `maxMeanCaseMs` (default 50.0ms). Millisecond resolution, coarse by
  design: a CI-shape heuristic, not a profiler.
- `hcDataTooLarge` — mean generated input size above `maxMeanInputBytes`
  (default 1 MiB). Size is `approxSize`: the value plus one level of
  element payload — order of magnitude, not exact.
- `hcDiscardHeavy` — discards per evaluated case above `maxDiscardRatio`
  (default 0.5). The soft warning before `maxDiscards`' hard abort.
- `hcFewExamples` — fewer than `minExamples` (default 10) cases evaluated.

Warnings by default — a green run stays green. List checks in `failOn` to
make them fail the run instead:

```nim
  health = HealthChecks(maxMeanCaseMs: 10.0, maxMeanInputBytes: 1 shl 20,
                        maxDiscardRatio: 0.5, minExamples: 10,
                        failOn: {hcTooSlow})
```

Health covers the random sweep only (like classification), and like
classification it never perturbs the stream: timing and measuring are
read-only on the RNG, so the same seed gives the identical cases with or
without `health`. Set any threshold to 0 to disable that check.

## Writing a shrinker

A shrinker is `proc(x: T): seq[T]` returning candidates ordered
most-aggressive first. The pattern (see `shrinkInt`):

1. Try the "zero" of the type (0, `""`, `@[]`).
2. Try small steps toward zero (neighbor, single-element drops).
3. Try halving / structural simplifications.

`shrinkFloat` follows the same pattern with 0.0 as zero; `shrinkChar` uses
`' '` (also `genChar`'s lower bound); `shrinkString` is the `shrinkSeq`
algorithm specialized to strings, composing `shrinkChar` per character.

`forAll` greedily follows the first candidate that still fails, so ordering
matters more than exhaustiveness.

## API

- **RNG**: `Rng`, `initRng(seed)`, `next()`, `below(n)`
- **Generators**: `genBool`, `genInt(lo, hi)`, `genFloat(lo, hi)`,
  `genChar`, `genString(maxLen)`, `genSeq[T](maxLen, gen)`,
  `genFrequency[T](choices)`, `genOneOf[T](gens)`, `genElements[T](xs)`,
  `genSuchThat[T](gen, pred, maxRetries = 100)`,
  `genMap[T, U](r, gen, f)`, `genBind[T, U](r, gen, k)`,
  `genPair[T, U]`, `genTriple[T, U, V]`,
  `genSized[T](r, f)`, `genRecursive[T](r, leaf, branch)`
- **Shrinkers**: `shrinkInt`, `shrinkFloat`, `shrinkChar`, `shrinkString`,
  `shrinkSeq[T](s, shrinkElem)`, `shrinkPair[T, U]`, `shrinkTriple[T, U, V]`
- **Driver**: `forAll[T](name, r, n, gen, prop, shrink = nil, regressions = @[],
  classify = nil, cover = @[], assume = nil, maxDiscards = 500,
  health = defaultHealth(), deadlineMs = 0)`; coverage requirements are `CoverReq`
  = `tuple[tag: string, minPct: float]`

Zero dependencies beyond the stdlib. Single module.

## Prior art

QuickCheck (Haskell), Hypothesis (Python), proptest (Rust),
test.check (Clojure). The name is the Popperian point: a property test
doesn't prove your code correct, it tries to falsify it.
