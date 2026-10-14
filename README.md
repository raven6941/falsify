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
FAIL [reverse-twice]: case 37, minimal input: @[3, -1]
```

## The seed discipline

- Check in a **fixed seed** so CI is reproducible.
- When hunting a flaky property locally, loop seeds until one fails, then
  hard-code that seed as a regression case.
- `initRng(0)` maps to a fixed nonzero default (never accidentally unseeded).

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
  `genChar`, `genString(maxLen)`, `genSeq[T](maxLen, gen)`
- **Shrinkers**: `shrinkInt`, `shrinkSeq[T](s, shrinkElem)`
- **Driver**: `forAll[T](name, r, n, gen, prop, shrink = nil)`

Zero dependencies beyond the stdlib. Single module.

## Prior art

QuickCheck (Haskell), Hypothesis (Python), proptest (Rust),
test.check (Clojure). The name is the Popperian point: a property test
doesn't prove your code correct, it tries to falsify it.
