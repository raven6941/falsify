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

## The seed discipline

- Check in a **fixed seed** so CI is reproducible.
- When hunting a flaky property locally, loop seeds until one fails, then
  hard-code that seed as a regression case.
- A failing `forAll` prints its seed (also available as `r.seed` after
  `initRng`); copy it into a regression case to replay the exact failure.
- `initRng(0)` maps to a fixed nonzero default (never accidentally unseeded);
  `r.seed` records the effective seed after that mapping.

## Writing a shrinker

A shrinker is `proc(x: T): seq[T]` returning candidates ordered
most-aggressive first. The pattern (see `shrinkInt`):

1. Try the "zero" of the type (0, `""`, `@[]`).
2. Try small steps toward zero (neighbor, single-element drops).
3. Try halving / structural simplifications.

`forAll` greedily follows the first candidate that still fails, so ordering
matters more than exhaustiveness.

## API

- **RNG**: `Rng`, `initRng(seed)`, `next()`, `below(n)`
- **Generators**: `genBool`, `genInt(lo, hi)`, `genFloat(lo, hi)`,
  `genChar`, `genString(maxLen)`, `genSeq[T](maxLen, gen)`,
  `genFrequency[T](choices)`, `genOneOf[T](gens)`, `genElements[T](xs)`,
  `genSuchThat[T](gen, pred, maxRetries = 100)`,
  `genSized[T](r, f)`, `genRecursive[T](r, leaf, branch)`
- **Shrinkers**: `shrinkInt`, `shrinkSeq[T](s, shrinkElem)`
- **Driver**: `forAll[T](name, r, n, gen, prop, shrink = nil)`

Zero dependencies beyond the stdlib. Single module.

## Prior art

QuickCheck (Haskell), Hypothesis (Python), proptest (Rust),
test.check (Clojure). The name is the Popperian point: a property test
doesn't prove your code correct, it tries to falsify it.
