## falsify — property-based testing for Nim.
##
## Falsify your properties: generate random inputs, shrink failures to
## minimal counterexamples, reproduce everything from a seed.
##
## Why this exists: the only previous Nim PBT library (nim-quicktest) is an
## unmaintained 2017 alpha that doesn't compile on the current toolchain.
## This is a small, dependency-free harness: a seeded xorshift64* RNG
## (deterministic across platforms), generator combinators, shrinking,
## a `forAll` driver with failure reporting, and a `runCommands` driver
## for stateful/model-based testing.
##
## Quickstart:
##   import falsify
##   const Seed = 424242'u64  # fixed seed in CI; vary locally
##   var r = initRng(Seed)
##   let ok = forAll("reverse-twice", r, 200,
##     proc(r: var Rng): seq[int] = r.genSeq(20, proc(r: var Rng): int = r.genInt(-100, 100)),
##     proc(s: seq[int]): bool = s.reversed.reversed == s,
##     shrinkSeq[int])
##   if not ok: quit(1)
##
## The seed discipline: check in a fixed seed so CI is reproducible; when
## hunting a flaky property locally, loop over seeds until one fails, then
## hard-code that seed as a regression case.

import std/macros
import std/math
import std/tables
import std/algorithm
import std/enumutils
import std/strutils
import std/monotimes
import std/times


type
  Rng* = object
    s: uint64
    size*: int
      ## Ambient generation size (see `genSized`). `forAll` grows this
      ## linearly from 0 to ~100 across the run; outside `forAll` it stays
      ## whatever you set it to (0 after `initRng`).
    seed*: uint64
      ## The effective seed this RNG was initialized with (after the
      ## 0 -> default mapping in `initRng`). `forAll` prints it on failure
      ## so the failing run is replayable: re-running `initRng(seed)` with
      ## the same `n`/gen/prop/shrink reproduces the identical stream and
      ## the identical minimal counterexample.

proc initRng*(seed: uint64): Rng =
  ## Seed the generator. Seed 0 maps to a fixed nonzero default.
  ## The effective seed is recorded on the returned `Rng` (see `Rng.seed`).
  var s = seed
  if s == 0: s = 0x9E3779B97F4A7C15'u64
  Rng(s: s, size: 0, seed: s)

proc next*(r: var Rng): uint64 =
  ## Next uint64. xorshift64*: deterministic across platforms.
  var x = r.s
  x = x xor (x shr 12)
  x = x xor (x shl 25)
  x = x xor (x shr 27)
  r.s = x
  x * 0x2545F4914F6CDD1D'u64

proc below*(r: var Rng, n: int): int =
  ## Int in [0, n). Modulo bias is irrelevant for property testing.
  doAssert n > 0, "below: n must be positive"
  (r.next() mod n.uint64).int

proc genBool*(r: var Rng): bool =
  r.next() mod 2 == 0

proc genInt*(r: var Rng, lo, hi: int): int =
  ## Int in [lo, hi] inclusive.
  ##
  ## Bug-finding bias: with probability 1/4, the result is drawn uniformly
  ## from the "interesting" values in range — the boundaries `lo` and `hi`,
  ## plus 0, -1, 1 when they lie in range. Otherwise uniform over [lo, hi].
  ## Uniform generation almost never hits edges, and edges are where bugs
  ## live (Hypothesis and QuickCheck bias the same way).
  doAssert lo <= hi, "genInt: lo > hi"
  if r.below(4) == 0:
    var cands: array[5, int]
    var m = 0
    for v in [lo, hi, 0, -1, 1]:
      if v >= lo and v <= hi:
        var seen = false
        for j in 0 ..< m:
          if cands[j] == v: seen = true; break
        if not seen:
          cands[m] = v
          inc m
    return cands[r.below(m)]
  lo + r.below(hi - lo + 1)

proc genFloat*(r: var Rng, lo, hi: float, allowNaN = false,
               allowInf = false): float =
  ## Float in [lo, hi).
  ##
  ## Bug-finding bias: with probability 1/4, returns `lo`, or a signed
  ## zero / subnormal pick when 0.0 lies in [lo, hi) — 0.0 and -0.0 are
  ## equally likely there (they differ under division), with small
  ## probability each of ±5e-324 (the minimum subnormal magnitude; the
  ## negative one only when `lo < 0.0`, so the result stays in range);
  ## otherwise uniform over [lo, hi).
  ##
  ## Float specials: NaN and ±Inf are *not* in `[lo, hi)` and are never
  ## generated unless you opt in — `allowNaN` / `allowInf`, both default
  ## false. The opt-in exists because these are where float code breaks,
  ## but the default keeps the documented range contract: a generator that
  ## silently hands you NaN when it promised `[lo, hi)` is a generator
  ## bug, not a found bug. With either flag set, probability 1/16 draws a
  ## special instead of the usual distribution: NaN when `allowNaN` (half
  ## the specials when both flags are set), otherwise ±Inf. `shrinkFloat`
  ## already shrinks NaN/±Inf to 0.0, so a special-triggered failure still
  ## shrinks and reports sanely.
  doAssert lo <= hi, "genFloat: lo > hi"
  if (allowNaN or allowInf) and r.below(16) == 0:
    if allowNaN and (not allowInf or r.genBool()):
      return NaN
    return if r.genBool(): Inf else: -Inf
  if r.below(4) == 0:
    if lo <= 0.0 and 0.0 < hi and r.below(2) == 0:
      case r.below(8)
      of 0: return -0.0          # == 0.0, always in range here
      of 1: return 5e-324        # smallest positive double < any hi > 0.0
      of 2:
        if lo < 0.0: return -5e-324  # needs lo strictly below zero
        return 5e-324
      else: return 0.0
    return lo
  lo + (hi - lo) * (r.next().float / high(uint64).float)

proc genChar*(r: var Rng): char =
  ## Printable ASCII char.
  chr(r.genInt(32, 126))

proc biasedLen(r: var Rng, maxLen: int): int =
  ## Length in [0, maxLen]. Empty and single-element lengths get elevated
  ## probability: with probability 1/4 the length is 0 or 1 (uniformly,
  ## clamped by maxLen); otherwise uniform over [0, maxLen].
  doAssert maxLen >= 0, "biasedLen: negative maxLen"
  if r.below(4) == 0:
    return r.below(min(maxLen, 1) + 1)
  r.below(maxLen + 1)

proc genString*(r: var Rng, maxLen: int): string =
  ## String of printable ASCII, length in [0, maxLen], with elevated
  ## probability of empty and single-char strings (see `biasedLen`).
  let n = r.biasedLen(maxLen)
  result = newString(n)
  for i in 0 ..< n:
    result[i] = r.genChar()

proc genSeq*[T](r: var Rng, maxLen: int, gen: proc(r: var Rng): T): seq[T] =
  ## Seq of length in [0, maxLen] with elevated probability of empty and
  ## single-element seqs (see `biasedLen`); elements from `gen`.
  let n = r.biasedLen(maxLen)
  result = newSeq[T](n)
  for i in 0 ..< n:
    result[i] = gen(r)

macro genOneOf*(r: var Rng, gens: untyped): untyped =
  ## Uniform choice among generator *expressions*; exactly one is evaluated.
  ##
  ##   r.genOneOf([r.genInt(0, 9), r.genInt(10, 99), 42])
  ##
  ## A macro rather than a proc, deliberately: Nim infers
  ## `{.noSideEffect, gcsafe.}` on generator lambdas, so a `proc` parameter
  ## nested in a collection never matches an inline lambda — and a lambda
  ## that captures a local infers `{.closure.}`, matching nothing at all.
  ## Taking expressions keeps the natural call syntax, full laziness (the
  ## unchosen generators never run), and closures working.
  ##
  ## `gens` must be a literal `[...]`. An empty array is a compile-time error.
  if gens.kind != nnkBracket or gens.len == 0:
    error("genOneOf expects a non-empty literal [gen, ...] array", gens)
  let idx = genSym(nskLet, "oneOfIdx")
  result = newStmtList(
    newLetStmt(idx, newCall(newDotExpr(r, ident"below"), newLit(gens.len))))
  var ifStmt = newNimNode(nnkIfStmt)
  for i in 0 ..< gens.len:
    ifStmt.add(newTree(nnkElifBranch,
      newCall(ident"==", idx, newLit(i)), gens[i]))
  # `idx < gens.len` always holds, so else is unreachable; it keeps the
  # if exhaustive so the macro can be used as an expression.
  ifStmt.add(newTree(nnkElse, gens[^1]))
  result.add(ifStmt)

macro genFrequency*(r: var Rng, choices: untyped): untyped =
  ## Weighted choice among `(weight, generator-expression)` pairs; exactly
  ## one generator is evaluated, with probability proportional to its weight.
  ##
  ##   r.genFrequency([(9, r.genInt(0, 100)),   # the common case
  ##                   (1, r.genInt(-100, 100))]) # the weird one
  ##
  ## A macro for the same reason as `genOneOf` (see its docstring): lambdas
  ## in collections cannot match `proc` parameters in Nim. `choices` must be
  ## a literal `[(weight, gen), ...]` array; an empty array is a compile-time
  ## error, and each weight is checked positive at run time (each weight
  ## expression is evaluated exactly once, in order).
  if choices.kind != nnkBracket or choices.len == 0:
    error("genFrequency expects a non-empty literal [(weight, gen), ...] array",
      choices)
  var wSyms: seq[NimNode] = @[]
  var genExprs: seq[NimNode] = @[]
  result = newNimNode(nnkBlockStmt).add(newEmptyNode(), newStmtList())
  let body = result[1]
  for c in choices:
    if c.kind != nnkTupleConstr or c.len != 2:
      error("genFrequency expects (weight, gen) pairs", c)
    let w = genSym(nskLet, "freqW")
    wSyms.add(w)
    genExprs.add(c[1])
    # Each weight expression is evaluated exactly once, in order.
    body.add(newLetStmt(w, c[0]))
    body.add(newCall(ident"doAssert",
      newCall(ident">", w, newLit(0)),
      newLit("genFrequency: weights must be positive")))
  var sumExpr: NimNode = wSyms[0]
  for s in wSyms[1 .. ^1]:
    sumExpr = newCall(ident"+", sumExpr, s)
  let pick = genSym(nskVar, "freqPick")
  body.add(newVarStmt(pick, newCall(newDotExpr(r, ident"below"), sumExpr)))
  var ifStmt = newNimNode(nnkIfStmt)
  var cumul: NimNode = wSyms[0]
  ifStmt.add(newTree(nnkElifBranch,
    newCall(ident"<", pick, cumul), genExprs[0]))
  for i in 1 ..< genExprs.len:
    cumul = newCall(ident"+", cumul, wSyms[i])
    ifStmt.add(newTree(nnkElifBranch,
      newCall(ident"<", pick, cumul), genExprs[i]))
  # `pick < total` always holds; else keeps the if exhaustive as an expression.
  ifStmt.add(newTree(nnkElse, genExprs[^1]))
  body.add(ifStmt)

proc genElements*[T](r: var Rng, xs: openArray[T]): T =
  ## Uniform pick of a value from `xs`. An empty `xs` is a usage error.
  ## (A plain proc: values have no laziness or lambda-typing concerns.)
  doAssert xs.len > 0, "genElements: empty xs"
  xs[r.below(xs.len)]

proc enumValuesOf[T: enum](): seq[T] =
  ## All declared values of enum `T`, in declaration order, built once
  ## and cached per type instantiation. Contiguous enums enumerate their
  ## ordinal range directly; holey enums (explicit ordinals with gaps)
  ## probe each ordinal and keep only the ones `symbolRank` accepts —
  ## it raises `IndexDefect` exactly on hole ordinals, so a hole can
  ## never leak into the value list (a bare `T(o)` cast would silently
  ## produce an invalid value). The `HoleEnumConv` warning on the probe
  ## cast is intentional: the probe *is* the validity check.
  var cached {.global.}: seq[T]
  if cached.len == 0:
    when T is Ordinal:
      for o in ord(low(T))..ord(high(T)):
        cached.add T(o)
    else:
      {.push warning[HoleEnumConv]: off.}
      for o in ord(low(T))..ord(high(T)):
        let v = T(o)
        try:
          discard symbolRank(v)
          cached.add v
        except IndexDefect:
          discard
      {.pop.}
  cached

proc genEnum*[T: enum](r: var Rng, t: typedesc[T]): T =
  ## Uniform pick of a value of enum type `T` — every declared variant
  ## gets its turn, including variants added later (no hand-written value
  ## list to drift). Holey enums are safe (see `enumValuesOf`).
  ##
  ## The type travels as a `typedesc` argument — `r.genEnum(Color)` —
  ## rather than an explicit type parameter, because explicit type
  ## arguments do not work in UFCS position in Nim 2.2 (`r.genEnum[Color]()`
  ## fails to instantiate); the `typedesc` form keeps the `r.` method-call
  ## style every other generator uses.
  ##
  ## Each draw consumes exactly one `below` call, so the stream stays
  ## seed-deterministic: same seed gives the same values, bit for bit.
  let vals = enumValuesOf[T]()
  vals[r.below(vals.len)]

proc shrinkEnum*[T: enum](x: T): seq[T] =
  ## Shrink an enum value toward `low(T)`, most-aggressive first (the
  ## `low(T)` candidate comes first), so minimal counterexamples prefer
  ## the earliest-declared variant. Holes are skipped: only declared
  ## values appear in the candidate list.
  for v in enumValuesOf[T]():
    if ord(v) < ord(x): result.add v
  # enumValuesOf is in ascending ordinal order, so low(T) — the most
  # aggressive candidate — is already first. No reversal.

proc genPermutation*(r: var Rng, n: int): seq[int] =
  ## Random permutation of `0 ..< n` (Fisher-Yates). The index form of
  ## `genShuffle`: use it when the permutation itself is the value —
  ## random orderings as data, permuting indices into several parallel
  ## arrays, drawing derangements-by-filtering.
  ##
  ## The draws are exactly the Fisher-Yates swaps (`below(i+1)` for
  ## `i` from `n-1` down to 1), so the stream is deterministic per seed
  ## and identical in shape to `genShuffle`'s. `n <= 1` draws nothing:
  ## the trivial permutation costs zero RNG.
  doAssert n >= 0, "genPermutation: negative n"
  result = newSeq[int](n)
  for i in 0 ..< n: result[i] = i
  for i in countdown(n - 1, 1):
    let j = r.below(i + 1)
    swap(result[i], result[j])

proc genShuffle*[T](r: var Rng, xs: seq[T]): seq[T] =
  ## Random permutation of `xs` (Fisher-Yates), QuickCheck `shuffle`
  ## style. Returns a new seq; the input is untouched. The canonical
  ## generator for ordering properties: `sorted(r.genShuffle(xs)) ==
  ## sorted(xs)` always holds, so a sorting property over a shuffled
  ## input tests exactly the ordering claim, not the generator.
  ##
  ## The draws are exactly the Fisher-Yates swaps (`below(i+1)` for `i`
  ## from `len-1` down to 1), deterministic per seed. Empty and
  ## single-element inputs return unchanged and draw nothing — the
  ## trivial loop is free.
  result = xs
  for i in countdown(result.len - 1, 1):
    let j = r.below(i + 1)
    swap(result[i], result[j])
proc genSubseq*[T](r: var Rng, xs: openArray[T]): seq[T] =
  ## Binomial subsequence: each element of `xs` is kept with probability
  ## 1/2 (QuickCheck `sublistOf`); order is preserved and `xs` is untouched.
  ##
  ## The sibling that *reorders* is `genShuffle` (#34); the sibling that
  ## samples *distinct indices* without order guarantees is `genUniqueInts`.
  ## The draws are exactly one Bernoulli per element, so the seed
  ## discipline is unchanged: same seed, same subsequence.
  result = newSeq[T](0)
  for x in xs:
    if r.genBool(): result.add(x)

proc genUniqueInts*(r: var Rng, lo, hi, n: int): seq[int] =
  ## `n` distinct ints from `lo..hi` via partial Fisher-Yates over the
  ## index range — no duplicates by construction (Hypothesis
  ## `st.sets(st.integers(lo, hi), min_size=n, max_size=n)` without the
  ## rejection sampling: this draws exactly `n` times).
  ##
  ## `n > hi - lo + 1` and negative `n` are usage errors (a filter can't
  ## conjure distinct values out of a range that's too small); `n == 0`
  ## returns empty without drawing.
  let size = hi - lo + 1
  doAssert lo <= hi, "genUniqueInts: lo > hi"
  doAssert n >= 0, "genUniqueInts: negative n"
  doAssert n <= size, "genUniqueInts: n exceeds range size"
  var idx = newSeq[int](size)
  for i in 0 ..< size: idx[i] = i
  for i in 0 ..< n:
    let j = i + r.below(size - i)
    swap(idx[i], idx[j])
  result = newSeq[int](n)
  for i in 0 ..< n: result[i] = lo + idx[i]

proc genSuchThat*[T](r: var Rng, gen: proc(r: var Rng): T,
                     pred: proc(x: T): bool, maxRetries = 100): T =
  ## Draw from `gen` until `pred` holds; raise `ValueError` after
  ## `maxRetries` draws without success.
  ##
  ## Filtering is a blunt instrument: each retry advances the RNG stream
  ## and a too-strict predicate silently turns generation into a hunt.
  ## Prefer narrowing the generator — building the constraint into
  ## generation — over heavy filtering (Hypothesis's guidance: narrow the
  ## generator, don't just filter). A predicate that exhausts the cap is
  ## therefore a usage error, not a wider retry loop: the `ValueError`
  ## tells you the generator is too narrow for the predicate (or the
  ## predicate too strict for the generator), and the fix is on one of
  ## those two, not on the cap.
  ##
  ## Pair every `genSuchThat(gen, pred)` with `shrinkSuchThat(x, shrinkElem,
  ## pred)` using the same predicate: the shrink phase evaluates `prop`
  ## on raw shrink candidates, so a predicate-blind shrinker lets the
  ## reported minimal counterexample wander outside the generated input
  ## space (see `shrinkSuchThat`).
  doAssert maxRetries > 0, "genSuchThat: maxRetries must be positive"
  for _ in 0 ..< maxRetries:
    let x = gen(r)
    if pred(x): return x
  raise newException(ValueError,
    "genSuchThat: predicate not satisfied after " & $maxRetries &
    " draws; narrow the generator (build the constraint into generation)" &
    " rather than filtering a wide one")

proc shrinkSuchThat*[T](x: T, shrinkElem: proc(x: T): seq[T],
                       pred: proc(x: T): bool): seq[T] =
  ## Shrink candidates for a `genSuchThat`-constrained value: the
  ## candidates of `shrinkElem(x)` filtered to those satisfying `pred`,
  ## order preserved (filtering keeps most-aggressive-first).
  ##
  ## Without this, a constrained property's shrink phase evaluates `prop`
  ## on candidates outside the generated input space. A candidate that
  ## violates the predicate can *fail* the property and become the
  ## reported "minimal input" even though the generator could never
  ## produce it — or *pass* it vacuously and stall the shrink at a
  ## non-minimal point. Concrete: generator = even ints, prop =
  ## `x mod 4 == 0`. `shrinkInt(10)` proposes 9, and `prop(9)` is false,
  ## so a predicate-blind shrink reports 9 (or 1, or 3) as the minimal
  ## counterexample — none of them in the input space. With
  ## `shrinkSuchThat(10, shrinkInt, isEven)` the candidates are `[0, 2]`
  ## and the counterexample shrinks to 2, the minimal *even* failure.
  ##
  ## If filtering empties the list, `x` is minimal *within the constraint*:
  ## the result is `@[]`, with no fallback to unfiltered candidates (a
  ## fallback would reintroduce the off-space shrink this exists to
  ## prevent).
  result = @[]
  for c in shrinkElem(x):
    if pred(c): result.add(c)

proc genMap*[T, U](r: var Rng, gen: proc(r: var Rng): T,
                   f: proc(x: T): U): U =
  ## Draw one value from `gen` and apply `f` — the functor map for
  ## generators (QuickCheck `fmap`).
  ##
  ## `f` takes only the drawn value, never the RNG, so mapping never
  ## perturbs the stream: the draws are exactly `gen`'s draws. Like every
  ## other `proc` parameter in this library, `f` must not capture locals
  ## (a capturing lambda infers `{.closure.}` and won't match); to use a
  ## captured value, thread it through generation with `genBind` instead.
  f(gen(r))

proc genBind*[T, U](r: var Rng, gen: proc(r: var Rng): T,
                    k: proc(r: var Rng, x: T): U): U =
  ## Draw `x` from `gen`, then run the continuation generator `k(x)` —
  ## the monadic bind for generators (QuickCheck `>>=`).
  ##
  ## This is the size-then-payload pattern: `genBind(r.genInt(1, 8),
  ## proc(r: var Rng, n: int): seq[bool] = r.genSeq(n, genBool))` draws a
  ## length, then a payload of exactly that length — no capture needed,
  ## the drawn value is threaded as an argument. Sequencing is literal:
  ## `genBind(gen, k)` draws exactly what `gen` draws followed by what
  ## `k(x)` draws, so the seed discipline is unchanged.
  let x = gen(r)
  k(r, x)

proc genPair*[T, U](r: var Rng, genT: proc(r: var Rng): T,
                    genU: proc(r: var Rng): U): (T, U) =
  ## Pair from two element generators — the multi-input building block.
  ##
  ## `forAll` takes a single generator of a single value; a pair (or
  ## triple) *is* that value for multi-input properties — algebraic laws,
  ## relations between generated values, sorted-pair checks. Shrinking is
  ## elementwise (see `shrinkPair`), so a failing pair shrinks to a minimal
  ## failing pair just as an int shrinks to the minimal failing int.
  ##
  ##   forAll("add-commutes", r, 200,
  ##     proc(r: var Rng): (int, int) =
  ##       r.genPair(proc(r: var Rng): int = r.genInt(-100, 100),
  ##                 proc(r: var Rng): int = r.genInt(-100, 100)),
  ##     proc(p: (int, int)): bool = p[0] + p[1] == p[1] + p[0],
  ##     proc(p: (int, int)): seq[(int, int)] =
  ##       p.shrinkPair(shrinkInt, shrinkInt))
  (genT(r), genU(r))

proc genTriple*[T, U, V](r: var Rng, genT: proc(r: var Rng): T,
                         genU: proc(r: var Rng): U,
                         genV: proc(r: var Rng): V): (T, U, V) =
  ## Triple from three element generators; the three-input version of
  ## `genPair` (e.g. associativity `(a+b)+c == a+(b+c)`). Shrink with
  ## `shrinkTriple`.
  (genT(r), genU(r), genV(r))

proc genSized*[T](r: var Rng, f: proc(r: var Rng, size: int): T): T =  ## Run `f` with the ambient size (`r.size`).
  ##
  ## The ambient size is the one knob recursive generators read: `forAll`
  ## grows it linearly from 0 to ~100 across the run (QuickCheck semantics —
  ## early cases are small, late cases explore deeper structures). Outside
  ## `forAll` it is 0 unless you set `r.size` yourself.
  f(r, r.size)

proc genRecursive*[T](r: var Rng,
    leaf: proc(r: var Rng): T,
    branch: proc(r: var Rng, sub: proc(r: var Rng): T {.closure.}): T): T =
  ## Generate a recursive structure (tree, AST, term) from a leaf generator
  ## and a branch generator.
  ##
  ## With probability `size/(size+1)` the branch is taken and with
  ## probability `1/(size+1)` the leaf is — so small sizes stay shallow and
  ## large sizes grow. Each recursion halves the ambient size, and size 0
  ## always takes the leaf, so generation terminates (no fuel parameter to
  ## thread, no runaway recursion).
  ##
  ## `branch` receives `sub`, a generator for one child subtree at the
  ## halved size; call it once per child. The branch runs at the parent
  ## size, the children at half — `genSized` inside `branch` sees the
  ## parent's size.
  ##
  ## `sub` is a closure (it captures the recursion context), which is why
  ## its parameter type carries `{.closure.}` — your `branch` lambda still
  ## declares it as a plain `proc` and everything typechecks (Nim converts
  ## implicitly).
  ##
  ##   type Tree = ref object
  ##     kids: seq[Tree]  # empty = leaf
  ##   proc genTree(r: var Rng): Tree =
  ##     r.genRecursive(
  ##       proc(r: var Rng): Tree = Tree(kids: @[]),
  ##       proc(r: var Rng, sub: proc(r: var Rng): Tree): Tree =
  ##         Tree(kids: @[sub(r), sub(r)]))
  if r.size <= 0 or r.below(r.size + 1) == 0:
    return leaf(r)
  let childSize = r.size div 2
  result = branch(r, proc(rr: var Rng): T {.closure.} =
    let outer = rr.size
    rr.size = childSize
    try:
      genRecursive(rr, leaf, branch)
    finally:
      rr.size = outer)

proc shrinkInt*(x: int): seq[int] =
  ## Shrink candidates for an int, most-aggressive first: 0, then the
  ## immediate neighbor toward 0, then halving toward 0. The neighbor
  ## step gives true minimality for threshold properties (e.g. x <= 7
  ## shrinks to exactly 8); halving covers the large-magnitude jumps.
  result = @[]
  if x != 0: result.add(0)
  if x > 0: result.add(x - 1)
  elif x < 0: result.add(x + 1)
  var v = x div 2
  while v != 0 and v != x:
    if v notin result: result.add(v)
    v = v div 2

proc shrinkFloat*(x: float): seq[float] =
  ## Shrink candidates for a float: 0.0 first, then halving toward zero.
  ## Most-aggressive first. NaN shrinks to 0.0 only; infinities shrink to
  ## 0.0 as well (halving cannot leave infinity, so there is nothing
  ## between). Halving always terminates: each step strictly reduces the
  ## magnitude until it underflows to 0.0.
  result = @[]
  if x != x:  # NaN
    return @[0.0]
  if x != 0.0: result.add(0.0)
  var v = x / 2.0
  while v != 0.0 and v != x:
    if v notin result: result.add(v)
    v = v / 2.0

proc shrinkChar*(x: char): seq[char] =
  ## Shrink candidates for a char: ' ' first, then the neighbor toward
  ## ' ', then halving the ordinal distance toward ' '. Most-aggressive
  ## first. ' ' is the char zero — the `shrinkInt` pattern with 0 replaced
  ## by ' ', which is also `genChar`'s lower bound, so shrinking a
  ## generated char stays inside the generator's range.
  result = @[]
  if x != ' ': result.add(' ')
  if x > ' ': result.add(chr(ord(x) - 1))
  elif x < ' ': result.add(chr(ord(x) + 1))
  var v = ord(' ') + (ord(x) - ord(' ')) div 2
  while v != ord(' ') and v != ord(x):
    let c = chr(v)
    if c notin result: result.add(c)
    v = ord(' ') + (v - ord(' ')) div 2

proc shrinkString*(s: string): seq[string] =
  ## Shrink candidates for a string: empty, halves, single-char drops,
  ## then per-character shrinks via `shrinkChar`. Most-aggressive first.
  ## The `shrinkSeq` algorithm specialized to strings: no `seq[char]`
  ## roundtrip, and the ordering contract is owned here.
  result = @[]
  if s.len == 0: return
  result.add("")
  let h = s.len div 2
  if h > 0:
    result.add(s[h .. ^1])
    result.add(s[0 ..< h])
  for i in 0 ..< s.len:
    var t = s
    t.delete(i .. i)
    if t notin result: result.add(t)
  for i in 0 ..< s.len:
    for c in shrinkChar(s[i]):
      var t = s
      t[i] = c
      if t notin result: result.add(t)

proc shrinkSeq*[T](s: seq[T], shrinkElem: proc(x: T): seq[T]): seq[seq[T]] =
  ## Shrink candidates for a seq: empty, halves, single-element drops,
  ## then element-wise shrinks. Most-aggressive first.
  result = @[]
  if s.len == 0: return
  result.add(newSeq[T]())
  let h = s.len div 2
  if h > 0:
    result.add(s[h .. ^1])
    result.add(s[0 ..< h])
  for i in 0 ..< s.len:
    var t = s
    t.delete(i)
    if t notin result: result.add(t)
  for i in 0 ..< s.len:
    for c in shrinkElem(s[i]):
      var t = s
      t[i] = c
      if t notin result: result.add(t)

proc shrinkPair*[T, U](p: (T, U), shrinkT: proc(x: T): seq[T],
                       shrinkU: proc(x: U): seq[U]): seq[(T, U)] =
  ## Shrink candidates for a pair, QuickCheck-tuple semantics: shrink each
  ## component while holding the other fixed — the left component's full
  ## candidate list first (most-aggressive first), then the right's.
  ## Greedy `forAll` shrinking follows the first still-failing candidate
  ## and re-shrinks the new minimal pair, so a failing pair converges to a
  ## minimal failing pair elementwise: a threshold on either component
  ## shrinks exactly, like `shrinkInt` does. Usage:
  ##   `proc(p: (int, int)): seq[(int, int)] = p.shrinkPair(shrinkInt, shrinkInt)`
  result = @[]
  for c in shrinkT(p[0]): result.add((c, p[1]))
  for c in shrinkU(p[1]): result.add((p[0], c))

proc shrinkTriple*[T, U, V](t: (T, U, V), shrinkT: proc(x: T): seq[T],
                            shrinkU: proc(x: U): seq[U],
                            shrinkV: proc(x: V): seq[V]): seq[(T, U, V)] =
  ## Shrink candidates for a triple; the three-component version of
  ## `shrinkPair`: left, then middle, then right, each holding the others
  ## fixed.
  result = @[]
  for c in shrinkT(t[0]): result.add((c, t[1], t[2]))
  for c in shrinkU(t[1]): result.add((t[0], c, t[2]))
  for c in shrinkV(t[2]): result.add((t[0], t[1], c))

type CoverReq* = tuple[tag: string, minPct: float]
  ## A coverage requirement for `forAll`: at least `minPct` percent of the
  ## sweep's cases must carry `tag` (as assigned by `classify`). Failing a
  ## requirement fails the run — it is the hard version of `classify`'s
  ## printed table, turning "we exercised the edge cases" from a hope
  ## into a checked claim.

proc reportCoverage(name: string, counts: Table[string, int], total: int,
                    cover: seq[CoverReq], quiet: bool = false): bool =
  ## Print the observed class distribution and check `cover` requirements.
  ## Returns true iff every requirement is met. The table prints first so
  ## a shortfall verdict always arrives with the evidence. `quiet`
  ## suppresses the distribution table, never the shortfall FAIL lines.
  var rows: seq[(string, int)] = @[]
  for k, v in counts: rows.add((k, v))
  rows.sort(proc(a, b: (string, int)): int = cmp(b[1], a[1]))
  if not quiet:
    for (tag, cnt) in rows:
      let pct = if total > 0: cnt.float * 100.0 / total.float else: 0.0
      echo "cover [", name, "]: \"", tag, "\": ",
        formatFloat(pct, ffDecimal, 1), "% (", cnt, "/", total, ")"
  for req in cover:
    let cnt = counts.getOrDefault(req.tag, 0)
    let pct = if total > 0: cnt.float * 100.0 / total.float else: 0.0
    if pct < req.minPct:
      echo "FAIL [", name, "]: coverage shortfall: \"", req.tag, "\": ",
        formatFloat(pct, ffDecimal, 1), "% < required ",
        formatFloat(req.minPct, ffDecimal, 1), "%"
      return false
  return true

type HealthCheck* = enum
  hcTooSlow
    ## Mean per-case property time above `maxMeanCaseMs`.
  hcDataTooLarge
    ## Mean generated input size above `maxMeanInputBytes`.
  hcDiscardHeavy
    ## Discard ratio above `maxDiscardRatio` — the soft warning ahead of
    ## #22's hard `maxDiscards` abort.
  hcFewExamples
    ## Fewer than `minExamples` cases actually evaluated.

type HealthChecks* = object
  maxMeanCaseMs*: float
    ## Warn when the mean per-case property time (generation excluded)
    ## exceeds this many milliseconds. 0 disables the check.
  maxMeanInputBytes*: int
    ## Warn when the mean generated input size (see `approxSize`) exceeds
    ## this many bytes. 0 disables the check.
  maxDiscardRatio*: float
    ## Warn when discards per evaluated case exceed this ratio. 0 disables.
  minExamples*: int
    ## Warn when fewer than this many cases were evaluated. 0 disables.
  failOn*: set[HealthCheck]
    ## Tripped checks that fail the run instead of just warning. Empty by
    ## default: a green run stays green, with `HEALTH` lines in the report.

proc defaultHealth*(): HealthChecks =
  ## Zero-configuration health: sane thresholds, warnings only.
  result = HealthChecks(maxMeanCaseMs: 50.0, maxMeanInputBytes: 1 shl 20,
                        maxDiscardRatio: 0.5, minExamples: 10, failOn: {})

type Verbosity* = enum
  vQuiet
    ## Print only failures (FAIL/DEADLINE lines): no ok lines, no HEALTH
    ## warnings, no coverage tables. For CI logs that should stay silent
    ## on green.
  vNormal
    ## Today's reporting: ok lines, warnings, tables, failure lines.
  vVerbose
    ## Everything in `vNormal`, plus the shrink trajectory (each accepted
    ## shrink step) and a settings summary in the ok line. Deterministic
    ## per seed.

type FalsifySettings* = object
  ## The tuning knobs of a `forAll` sweep, bundled so a project can name a
  ## convention once (CI runs deep, local runs fast) instead of repeating
  ## sixteen parameters at every call site. The case count `n` stays a
  ## positional `forAll` parameter — it is the most-set knob and reads
  ## naturally there. Everything per-property (`gen`, `prop`, `shrink`,
  ## `regressions`, `examples`, `classify`, `cover`, `assume`, `target`)
  ## stays a `forAll` parameter: settings hold only tuning.
  maxDiscards*: int
    ## Abort with a gave-up line once this many cases are discarded
    ## (default 500). 0 tolerates no discards.
  deadlineMs*: int
    ## Per-case deadline in milliseconds, 0 = disabled (default 0).
  maxShrinks*: int
    ## Shrink-phase candidate budget, 0 = unbounded (default 0).
  health*: HealthChecks
    ## Health-check thresholds (default `defaultHealth()`).
  verbosity*: Verbosity
    ## Reporting level (default `vNormal`).

proc defaultSettings*(): FalsifySettings =
  ## The knob values `forAll` used before settings existed: a run with
  ## `settings = defaultSettings()` is byte-identical to the old
  ## parameter defaults.
  FalsifySettings(maxDiscards: 500, deadlineMs: 0, maxShrinks: 0,
                  health: defaultHealth(), verbosity: vNormal)

var settingsProfiles = initTable[string, FalsifySettings]()
  ## Named-settings registry backing `defineProfile` / `withProfile`.

proc defineProfile*(name: string, s: FalsifySettings) =
  ## Register `s` under `name` so every property in the suite can share
  ## one tuning convention: `settings = withProfile("ci")`. Re-defining a
  ## name replaces the previous profile.
  settingsProfiles[name] = s

proc withProfile*(name: string): FalsifySettings =
  ## Return the settings registered under `name`. An unknown name fails
  ## loud — a typo in a profile name must not silently become defaults.
  doAssert name in settingsProfiles,
    "falsify: unknown settings profile: " & name
  settingsProfiles[name]

proc approxSize*[T](x: T): int =
  ## Order-of-magnitude byte size of `x`: the value itself plus, for
  ## anything with `len`, one level of element payload. Not exact — a
  ## 1MB-vs-10B distinction is what `hcDataTooLarge` needs.
  when compiles(x.len) and compiles(x[0]):
    result = sizeof(x) + x.len * sizeof(x[0])
  elif compiles(x.len):
    result = sizeof(x) + x.len
  else:
    result = sizeof(x)

proc trippedChecks*(totalMs: float, totalBytes: int, evaluated, discards: int,
                    h: HealthChecks): set[HealthCheck] =
  ## Pure tripping logic for the health checks, exported so tests can check
  ## it directly without running a sweep.
  result = {}
  if evaluated > 0:
    if h.maxMeanCaseMs > 0 and totalMs / evaluated.float > h.maxMeanCaseMs:
      result.incl(hcTooSlow)
    if h.maxMeanInputBytes > 0 and totalBytes div evaluated > h.maxMeanInputBytes:
      result.incl(hcDataTooLarge)
    if h.maxDiscardRatio > 0 and discards.float / evaluated.float > h.maxDiscardRatio:
      result.incl(hcDiscardHeavy)
  if h.minExamples > 0 and evaluated < h.minExamples:
    result.incl(hcFewExamples)

proc reportHealth(name: string, totalMs: float, totalBytes: int,
                  evaluated, discards: int, h: HealthChecks,
                  quiet: bool = false): bool =
  ## Print a `HEALTH [name]` line per tripped check (or `FAIL` when the
  ## check is in `h.failOn`). Returns true iff no check in `h.failOn`
  ## tripped. `quiet` suppresses warnings, never `FAIL` lines.
  let tripped = trippedChecks(totalMs, totalBytes, evaluated, discards, h)
  if tripped == {}: return true
  let meanMs = if evaluated > 0: totalMs / evaluated.float else: 0.0
  let meanBytes = if evaluated > 0: totalBytes div evaluated else: 0
  for c in tripped:
    let (label, detail) = case c
      of hcTooSlow:
        ("too-slow", "mean case time " & formatFloat(meanMs, ffDecimal, 1) &
          "ms > " & formatFloat(h.maxMeanCaseMs, ffDecimal, 1) & "ms")
      of hcDataTooLarge:
        ("data-too-large", "mean input " & $meanBytes & " bytes > " &
          $h.maxMeanInputBytes & " bytes")
      of hcDiscardHeavy:
        ("discard-heavy", "discards " & $discards & "/" & $evaluated & " = " &
          formatFloat(100.0 * discards.float / evaluated.float, ffDecimal, 1) &
          "% > " & formatFloat(100.0 * h.maxDiscardRatio, ffDecimal, 1) & "%")
      of hcFewExamples:
        ("few-examples", "only " & $evaluated & " cases evaluated < " &
          $h.minExamples & " minimum")
    let verdict = if c in h.failOn: "FAIL" else: "HEALTH"
    if verdict == "FAIL" or not quiet:
      echo verdict, " [", name, "]: ", label, ": ", detail
  return tripped * h.failOn == {}

proc mutateTarget*[T](r: var Rng, best: T,
                     shrink: proc(x: T): seq[T]): tuple[ok: bool, val: T] =
  ## One targeted-generation mutation step: pick uniformly among the first
  ## few least-aggressive shrink candidates of the best-scoring input seen
  ## so far. Shrink lists are most-aggressive first, so the reversed head
  ## is small perturbations, not jumps back to the shrink fixed point.
  ## Returns `ok = false` when the shrinker yields no candidates (e.g. the
  ## best input is already minimal) — the caller then draws fresh instead.
  let cands = shrink(best)
  if cands.len == 0: return (false, best)
  let k = min(4, cands.len)
  (true, cands[cands.len - 1 - r.below(k)])

proc forAll*[T](name: string, r: var Rng, n: int,
                gen: proc(r: var Rng): T,
                prop: proc(x: T): bool,
                shrink: proc(x: T): seq[T] = nil,
                regressions: seq[uint64] = @[],
                examples: seq[T] = @[],
                classify: proc(x: T): seq[string] = nil,
                cover: seq[CoverReq] = @[],
                assume: proc(x: T): bool = nil,
                settings: FalsifySettings = defaultSettings(),
                target: proc(x: T): float = nil): bool =
  ## Run `prop` on `n` generated inputs. On the first failure, shrink
  ## (if a shrinker is given) and print the seed + case index + minimal
  ## case, then return false. Returns true iff all cases pass.
  ##
  ## The failure line is the replay recipe: it prints `r.seed` (see
  ## `Rng.seed`), so re-running with `initRng(seed)` and the same
  ## arguments reproduces the identical minimal counterexample.
  ##
  ## Defects (e.g. `AssertionDefect` from an `assert` in the property or
  ## the code under test) are failures, not crashes: they are reported
  ## with the seed + minimal input like any other failure, and `forAll`
  ## returns false so the suite continues. This is catch-and-report, not
  ## report-and-reraise — a harness that aborts mid-suite loses every
  ## later property and, worse, the counterexample report. Defects raised
  ## by the *generator* itself (harness misuse, e.g. empty `genElements`)
  ## still propagate: those are programming errors, fail loud.
  ##
  ## A custom shrinker has type `proc(x: T): seq[T]` returning candidates
  ## ordered most-aggressive first; see `shrinkInt` for the pattern.
  ## For seqs, `shrinkSeq[T]` needs an element shrinker:
  ##   `proc(s: seq[int]): seq[seq[int]] = s.shrinkSeq(shrinkInt)`.
  ##
  ## The ambient generation size (`r.size`, see `genSized`) grows linearly
  ## from 0 to ~100 across the run, so recursive generators (`genRecursive`)
  ## start shallow and explore deeper structures in later cases.
  ##
  ## Tuning knobs: `settings` (default `defaultSettings()`) bundles the
  ## sweep tuning — `maxDiscards`, `deadlineMs`, `maxShrinks`, `health`,
  ## `verbosity` — into one object instead of sixteen parameters at every
  ## call site.
  ## The case count `n` stays positional: it is the most-set knob and
  ## reads naturally there. `defineProfile` names a project-wide
  ## convention once (CI runs deep, local runs fast) and `withProfile`
  ## recalls it at each call site; an unknown profile name fails loud
  ## rather than silently becoming defaults. Default settings give
  ## byte-identical sweep streams to the old parameter defaults.
  ##
  ## Per-case deadline: `settings.deadlineMs` (default 0 = disabled, Hypothesis
  ## `deadline` style) bounds how long one property evaluation may take.
  ## When a case exceeds the deadline, the sweep aborts immediately with a
  ## `DEADLINE [name]` line (case index, elapsed ms, and the seed so the
  ## run is replayable) and `forAll` returns false — the same failure
  ## protocol as a property failure, so the suite continues with later
  ## properties. Generation time is excluded from the measurement: the
  ## timer starts after `gen` returns, the same convention as
  ## `hcTooSlow`'s mean case time.
  ##
  ## This is *cooperative*, not preemptive: it detects a slow case at the
  ## case boundary and aborts the sweep, but it cannot interrupt a truly
  ## infinite loop inside the property. True preemption needs threads and
  ## is out of scope — a hanging property still hangs `forAll`. What the
  ## deadline buys is fail-fast feedback for the common case: a property
  ## whose single case takes minutes turns a silent hanging CI job into a
  ## loud, seed-attributed abort.
  ##
  ## The abort skips the shrink phase on purpose: shrinking would re-run
  ## the slow property once per candidate, which is exactly the hang the
  ## deadline aborts. The DEADLINE line therefore reports the raw
  ## (unshrunk) case via the seed, not a minimal input.
  ##
  ## Shrink budget: `settings.maxShrinks` (default 0 = unbounded, today's behavior)
  ## caps the number of shrink candidates evaluated after a failure.
  ## `settings.deadlineMs` bounds the per-case *check*; the budget bounds the
  ## *shrink phase* — a pathological shrinker emitting enormous candidate
  ## lists (deep or cyclic structures) can't spin the loop for minutes
  ## while the user waits for the counterexample shrinking already found.
  ## Budget accounting is one counter, deterministic per seed. When the
  ## budget exhausts, `forAll` stops with the best counterexample found so
  ## far and says so: the FAIL line reads "... (shrink budget N
  ## exhausted, may not be minimal)"; a shrink that finishes inside the
  ## budget reads "... (shrunk to minimum, budget N)". With the default 0
  ## the line is byte-identical to today, so existing suites see no
  ## change in shrink quality or report text.
  ##
  ## Targeted generation: `target` (default nil = off, Hypothesis
  ## `target()` style) is a pure function of the generated input reporting
  ## a float score per evaluated case — higher is better. `forAll` keeps
  ## the best-scoring input seen; with probability 1/4 the next case is a
  ## small mutation of the best input instead of a fresh draw (fresh draws
  ## still happen, so coverage never collapses to a point). Mutations reuse
  ## the shrinker as the mutator — the least-aggressive shrink candidates
  ## are small perturbations — so targeting needs `shrink` to steer at all:
  ## with no shrinker, scores are still recorded and reported, but every
  ## case is a fresh draw. Scores steer generation only, never the shrink
  ## phase: a failing case still shrinks to the minimal failing input
  ## exactly as in a blind run. The best score is reported in the ok line
  ## when targeting is on. Targeting applies to the random sweep only, not
  ## to regression replays (replays are fixed failing cases, like
  ## `classify` and the health checks).
  ##
  ## Unlike Hypothesis's `target()`, which the test body calls
  ## mid-execution, falsify's score is a pure function of the generated
  ## input — a capturing lambda cannot reach it through falsify's
  ## proc-typed callbacks, so the score you can report is whatever you can
  ## compute from `x`. In practice this covers the motivating uses (push a
  ## computed magnitude toward a threshold, grow a structure toward a
  ## size): compute the magnitude from the input and score it.
  ##
  ## The score function never touches the RNG (the same read-only
  ## discipline as `classify` and the health checks): same seed gives the identical
  ## score stream and the identical best-input trajectory, so the seed
  ## discipline holds. With `target` unset the case stream is byte-identical
  ## to today — targeting changes the stream by construction (mutation
  ## replaces some draws), but deterministically per seed. NaN scores never
  ## become the best.
  ##
  ## Coverage: `classify` bins each generated case into named classes and
  ## `forAll` prints the observed distribution after the sweep, QuickCheck
  ## style — a green run then says *what* it exercised, not just how many
  ## cases it ran. `cover` makes the claim hard: each `(tag, minPct)`
  ## requirement must be met or the run fails with a shortfall line. `cover`
  ## without `classify` is a usage error (fails loud via doAssert).
  ##
  ## Classification covers the random sweep only, not the regression
  ## replays: replays are fixed failing cases, and counting them would
  ## distort the distribution the sweep actually produced. Each tag counts
  ## at most once per case (duplicate tags in one `classify` result are
  ## deduplicated). A `classify` that raises is a failure, reported with
  ## the seed like a property failure.
  ##
  ## Classifying never perturbs the stream: `classify` receives only the
  ## generated value, not the RNG, so the same seed produces the identical
  ## case stream whether or not `classify` is given.
  ##
  ## Preconditions: `assume` is the property-level precondition
  ## (QuickCheck `==>`). A case failing `assume` is *discarded* — counted
  ## and reported in the ok line (`ok [name]: 200 cases, 37 discarded`),
  ## never a failure, and never classified. If discards exceed
  ## `settings.maxDiscards` (default 500) the run aborts with a gave-up line and
  ## returns false: an unsatisfiable precondition fails loud instead of
  ## spinning. An exception or defect *inside* `assume` is a programming
  ## error and fails the run like a property failure.
  ##
  ## Discarded draws still consume RNG, so the case stream is identical
  ## with or without `assume` — only which cases get evaluated changes,
  ## and the FAIL line's case number is the draw index in that stream.
  ## `assume` applies to regression replays too: a replayed seed whose
  ## case now fails `assume` is discarded, not failed — the property
  ## changed, not the stream.
  ##
  ## Prefer narrowing the generator over heavy filtering — same advice as
  ## `genSuchThat`: a precondition that discards most cases is usually a
  ## generator that should have produced satisfying cases directly.
  ##
  ## Health checks: `settings.health` (default `defaultHealth()`) watches the sweep
  ## for degenerate shapes a green run would otherwise hide — Hypothesis
  ## `HealthCheck` style. `hcTooSlow` (mean per-case property time, in ms,
  ## generation excluded), `hcDataTooLarge` (mean `approxSize` of the
  ## generated input, in bytes), `hcDiscardHeavy` (discards per evaluated
  ## case — the soft warning before `settings.maxDiscards`' hard abort), and
  ## `hcFewExamples` (fewer than `minExamples` cases evaluated). Tripped
  ## checks print `HEALTH [name]` lines and warn by default; listing a
  ## check in `failOn` makes it fail the run instead. Health covers the
  ## random sweep only, like classification — and like classification it
  ## never perturbs the stream: timing and measuring are read-only on the
  ## RNG, so the same seed gives the identical cases with or without
  ## `settings.health`. Timing is per-case wall clock at millisecond resolution —
  ## coarse by design; it is a CI-shape heuristic, not a profiler.
  ##
  ## Regression corpus: `regressions` is a list of seeds replayed *before*
  ## the random sweep. Copy the seed from a failing run's FAIL line into
  ## the list — each replay runs the identical stream (same seed → same
  ## cases → same failure, same minimal counterexample), shrinking and
  ## reporting exactly like a fresh failure, with no manual stream
  ## bookkeeping. A regression failure aborts the whole `forAll` and
  ## returns false, just like a sweep failure; the random sweep only runs
  ## after every replay passes. The list is explicit and checked in —
  ## no hidden on-disk database, no state the next reader can't see
  ## (Hypothesis's example database, minus the magic directory).
  ##
  ## Explicit examples: `examples` is a list of literal values evaluated
  ## *before* the regression replays and the sweep — the known-interesting
  ## inputs you already have (the boundary you reasoned about by hand,
  ## the regression case from a bug report), Hypothesis `@example` style.
  ## A failing example fails the run immediately with
  ## `FAIL [name]: example <i>, minimal input: <value>` — the value *is*
  ## the recipe, no seed needed — and the failing example shrinks with
  ## the same shrinker for a consistent minimal-input line. Examples
  ## consume no RNG: the case stream is byte-identical with and without
  ## `examples`, so the same seed gives the same sweep cases either way.
  ## An example failing `assume` is a programming error, not a discard —
  ## it fails the run (a hand-written input that violates the
  ## precondition is a bug in the test, not in the generator). Examples
  ## are outside classification, coverage, the health checks, targeting, and the
  ## per-case deadline: they are deliberate, not sampled, and measuring
  ## them would distort the sweep's statistics.
  proc shrinkMinimal(x: T): tuple[val: T, budgetExhausted: bool] =
    ## Greedy-shrink `x` to a minimal still-failing input (candidates
    ## most-aggressive first), honoring the `settings.maxShrinks` budget.
    ## `prop` exceptions/defects count as failures, same as in the sweep.
    result = (x, false)
    if shrink == nil: return result
    var shrinksUsed = 0
    var cands = shrink(result[0])
    while cands.len > 0:
      var progressed = false
      for c in cands:
        if settings.maxShrinks > 0 and shrinksUsed >= settings.maxShrinks:
          return (result[0], true)
        inc shrinksUsed
        var cf = false
        try: cf = not prop(c)
        except CatchableError: cf = true
        except Defect: cf = true
        if cf:
          if settings.verbosity == vVerbose:
            echo "shrink [", name, "]: ", $c
          result[0] = c
          cands = shrink(result[0])
          progressed = true
          break
      if not progressed: break

  proc runExamples(): bool =
    ## Evaluate the explicit `examples` before everything else. No RNG is
    ## touched here, so the sweep stream is byte-identical with and without
    ## `examples` — same seed gives the same sweep cases either way.
    result = true
    for ei in 0 ..< examples.len:
      let x = examples[ei]
      if assume != nil:
        var holds = false
        try:
          holds = assume(x)
        except CatchableError as ae:
          echo "FAIL [", name, "]: exception in assume on example ", ei,
            ": ", ae.msg
          return false
        except Defect as ad:
          echo "FAIL [", name, "]: defect in assume on example ", ei, ": ",
            ad.name, ": ", ad.msg
          return false
        if not holds:
          # A hand-written input failing `assume` is a programming error —
          # the author chose this value deliberately — not a discard.
          echo "FAIL [", name, "]: example ", ei, " failed assume: ", $x
          return false
      var failed = false
      try:
        failed = not prop(x)
      except CatchableError as pe:
        echo "FAIL [", name, "]: exception on example ", ei, ": ", pe.msg
        failed = true
      except Defect as pd:
        echo "FAIL [", name, "]: defect on example ", ei, ": ", pd.name,
          ": ", pd.msg
        failed = true
      if failed:
        # The value *is* the replay recipe: no seed needed. Shrink with
        # the same shrinker for a consistent minimal-input line.
        let (minimal, budgetExhausted) = shrinkMinimal(x)
        var failLine = "FAIL [" & name & "]: example " & $ei & ": " & $x &
          ", minimal input: " & $minimal
        if settings.maxShrinks > 0:
          if budgetExhausted:
            failLine &= " (shrink budget " & $settings.maxShrinks &
              " exhausted, may not be minimal)"
          else:
            failLine &= " (shrunk to minimum, budget " & $settings.maxShrinks & ")"
        echo failLine
        return false

  proc runSweep(rr: var Rng, isReplay: bool): bool =
    result = true
    var counts = initTable[string, int]()
    var discards = 0
    var evaluated = 0
    var totalMs = 0.0
    var totalBytes = 0
    var haveBest = false
    var best: T
    var bestScore = 0.0
    let targeting = not isReplay and target != nil and shrink != nil
    for i in 0 ..< n:
      rr.size = min(100, i * 100 div max(n, 1))
      let x =
        if targeting and haveBest and rr.below(4) == 0:
          let (ok, m) = mutateTarget(rr, best, shrink)
          if ok: m else: gen(rr)
        else:
          gen(rr)
      if not isReplay:
        totalBytes += approxSize(x)
      if assume != nil:
        var holds = false
        try:
          holds = assume(x)
        except CatchableError as e:
          echo "FAIL [", name, "]: exception in assume: ", e.msg
          return false
        except Defect as d:
          echo "FAIL [", name, "]: defect in assume: ", d.name, ": ", d.msg
          return false
        if not holds:
          inc discards
          if discards > settings.maxDiscards:
            echo "FAIL [", name, "]: gave up: discarded ", discards,
              " > maxDiscards ", settings.maxDiscards, " cases"
            return false
          continue
      if not isReplay and target != nil:
        # Scoring is read-only on the RNG (like classify): it sees only
        # the generated value, so scoring never perturbs the stream.
        let s = target(x)
        if s == s and (not haveBest or s > bestScore):  # NaN never wins
          haveBest = true
          bestScore = s
          best = x
      if not isReplay and classify != nil:
        var tags: seq[string] = @[]
        try:
          tags = classify(x)
        except CatchableError as e:
          echo "FAIL [", name, "]: exception in classify: ", e.msg
          return false
        except Defect as d:
          echo "FAIL [", name, "]: defect in classify: ", d.name, ": ", d.msg
          return false
        var seen: seq[string] = @[]
        for t in tags:
          if t notin seen:
            seen.add(t)
            counts.mgetOrPut(t, 0) += 1
      var failed = false
      let t0 = getMonoTime()
      try:
        failed = not prop(x)
      except CatchableError as e:
        echo "FAIL [", name, "]: exception on input: ", e.msg
        failed = true
      except Defect as d:
        echo "FAIL [", name, "]: defect on input: ", d.name, ": ", d.msg
        failed = true
      let caseMs = inMilliseconds(getMonoTime() - t0).float
      if settings.deadlineMs > 0 and caseMs > settings.deadlineMs.float:
        echo "DEADLINE [", name, "]: case ", i, " took ",
          formatFloat(caseMs, ffDecimal, 1), "ms > ", settings.deadlineMs,
          "ms deadline, seed: ", rr.seed
        return false
      if not isReplay:
        inc evaluated
        totalMs += caseMs
      if failed:
        result = false
        let (minimal, budgetExhausted) = shrinkMinimal(x)
        var failLine = "FAIL [" & name & "]: seed: " & $rr.seed & ", case " & $i &
          ", minimal input: " & $minimal
        if settings.maxShrinks > 0:
          if budgetExhausted:
            failLine &= " (shrink budget " & $settings.maxShrinks &
              " exhausted, may not be minimal)"
          else:
            failLine &= " (shrunk to minimum, budget " & $settings.maxShrinks & ")"
        echo failLine
        return false
    if isReplay:
      if settings.verbosity != vQuiet:
        echo "ok [", name, "]: replay seed ", rr.seed, ", ", n, " cases"
    else:
      let quiet = settings.verbosity == vQuiet
      if classify != nil:
        if not reportCoverage(name, counts, n, cover, quiet): return false
      if not reportHealth(name, totalMs, totalBytes, evaluated, discards,
                          settings.health, quiet): return false
      if not quiet:
        var line = "ok [" & name & "]: " & $n & " cases"
        if examples.len > 0:
          line = "ok [" & name & "]: " & $examples.len & " examples, " & $n &
            " cases"
        if discards > 0: line &= ", " & $discards & " discarded"
        if target != nil and haveBest:
          line &= ", best target score: " &
            formatFloat(bestScore, ffDecimal, 1)
        if settings.verbosity == vVerbose:
          line &= ", settings(maxDiscards=" & $settings.maxDiscards &
            " deadlineMs=" & $settings.deadlineMs &
            " maxShrinks=" & $settings.maxShrinks & ")"
        echo line
  doAssert classify != nil or cover.len == 0,
    "forAll: `cover` requires `classify`"
  doAssert settings.deadlineMs >= 0, "forAll: `settings.deadlineMs` must be non-negative"
  doAssert settings.maxShrinks >= 0, "forAll: `settings.maxShrinks` must be non-negative"
  result = true
  if not runExamples(): return false
  for seed in regressions:
    var rr = initRng(seed)
    if not runSweep(rr, isReplay = true): return false
  if not runSweep(r, isReplay = false): return false

proc replayCmds*[C, M, Sys](cmds: seq[C],
    newModel: proc(): M,
    newSys: proc(): Sys,
    run: proc(sys: var Sys, m: var M, c: C): bool): bool =
  ## Replay a command sequence against a fresh model and system, stepwise.
  ## Returns true iff every step agrees (no divergence). An exception or
  ## defect raised by `run` counts as divergence — a crashing step is a
  ## failing step, the same rule `forAll` applies to properties.
  var sys = newSys()
  var m = newModel()
  for c in cmds:
    var stepOk = false
    try:
      stepOk = run(sys, m, c)
    except CatchableError:
      return false
    except Defect:
      return false
    if not stepOk: return false
  return true

proc shrinkCmdSeq*[C, M, Sys](cmds: seq[C],
    newModel: proc(): M,
    newSys: proc(): Sys,
    run: proc(sys: var Sys, m: var M, c: C): bool,
    shrinkCmd: proc(c: C): seq[C] = nil): seq[C] =
  ## Greedy-shrink a diverging command sequence to a minimal still-diverging
  ## one. Candidates follow the `shrinkSeq` order — empty, halves,
  ## single-command drops, then per-command shrinks via `shrinkCmd` (skipped
  ## when nil) — and a candidate is kept only if replaying it against a fresh
  ## model+system still diverges. The loop stops at a 1-minimal sequence: no
  ## single drop or command shrink still fails.
  ##
  ## Shrinking replays, never regenerates: candidates are checked with
  ## `replayCmds`, so the generator's preconditions don't restrict the
  ## shrinker — a dropped command that the generator would never emit in
  ## that model state is still a legitimate smaller failing sequence.
  result = cmds
  let elemShrink: proc(c: C): seq[C] =
    if shrinkCmd != nil: shrinkCmd
    else: (proc(c: C): seq[C] = @[])
  var cands = shrinkSeq(result, elemShrink)
  while cands.len > 0:
    var progressed = false
    for c in cands:
      if not replayCmds(c, newModel, newSys, run):
        result = c
        cands = shrinkSeq(result, elemShrink)
        progressed = true
        break
    if not progressed: break

proc runCommands*[C, M, Sys](name: string, r: var Rng, n: int, maxLen: int,
    genCmd: proc(r: var Rng, m: M): C,
    newModel: proc(): M,
    newSys: proc(): Sys,
    run: proc(sys: var Sys, m: var M, c: C): bool,
    shrinkCmd: proc(c: C): seq[C] = nil,
    regressions: seq[uint64] = @[]): bool =
  ## Stateful/model-based testing, QuickCheck/Hypothesis style: generate
  ## random command sequences, run each against both the real system and a
  ## model, and fail on divergence. Returns true iff all `n` cases agree.
  ##
  ## The three types: `C` is the command type, `M` the model type, `Sys`
  ## the system-under-test type. `genCmd` generates one command and may read
  ## the model — precondition-style, so it only emits commands that are
  ## valid in the current model state (e.g. never `pop` an empty model
  ## stack). `newModel`/`newSys` build fresh instances per case. `run`
  ## applies one command to *both*: it advances the model per its own
  ## semantics, drives the real system, and returns false on divergence.
  ## `shrinkCmd` shrinks individual commands (nil skips command-level
  ## shrinking; sequence drops always apply).
  ##
  ## Generation and execution are interleaved: each command is generated from
  ## the current model state, then run immediately against the live
  ## `(sys, m)` pair, so `genCmd` always sees the model exactly as the
  ## previous commands left it. Sequence lengths use the `genSeq`-style
  ## length bias (empty and single-command sequences get elevated
  ## probability), capped at `maxLen`.
  ##
  ## On the first divergence the driver aborts that case, shrinks the
  ## command sequence with `shrinkCmdSeq`, and prints the seed, the case
  ## index, the divergence step, and the minimal still-diverging command
  ## sequence, then returns false. Shrinking replays candidates on fresh
  ## model+system pairs and never touches the RNG.
  ##
  ## The seed discipline holds exactly as in `forAll`: the same seed, `n`,
  ## `maxLen`, and callbacks reproduce the identical command sequences and
  ## the identical minimal failing sequence, byte-identically. Copy the seed
  ## from a FAIL line into `regressions` to replay it before the random
  ## sweep, checked in like any other regression seed.
  ##
  ## Exceptions and defects raised by `run` count as divergence (reported
  ## with the step index, like `forAll`'s property failures). Exceptions
  ## from `genCmd`, `newModel`, or `newSys` propagate — those are harness
  ## misuse, fail loud.
  ##
  ## Example: a counter whose `dec` misbehaves after a `reset`.
  ##   type CounterCmd = enum ccInc, ccDec, ccReset
  ##   var r = initRng(424242)
  ##   let ok = runCommands("counter", r, 200, 10,
  ##     proc(r: var Rng, m: int): CounterCmd =
  ##       if m > 0 and r.genBool(): ccDec
  ##       else: r.genElements([ccInc, ccReset]),
  ##     proc(): int = 0,                       # model: expected count
  ##     proc(): int = 0,                       # system: real counter
  ##     proc(sys: var int, m: var int, c: CounterCmd): bool =
  ##       case c
  ##       of ccInc: inc m; inc sys
  ##       of ccDec: dec m; dec sys
  ##       of ccReset: m = 0; sys = 0
  ##       sys == m)
  ##   if not ok: quit(1)
  proc runCase(rr: var Rng, isReplay: bool): bool =
    result = true
    for i in 0 ..< n:
      rr.size = min(100, i * 100 div max(n, 1))
      var sys = newSys()
      var m = newModel()
      let len = biasedLen(rr, maxLen)
      var cmds: seq[C] = @[]
      var failedAt = -1
      for k in 0 ..< len:
        let c = genCmd(rr, m)
        cmds.add(c)
        var stepOk = false
        try:
          stepOk = run(sys, m, c)
        except CatchableError as e:
          echo "FAIL [", name, "]: exception in run at step ", k, ": ", e.msg
        except Defect as d:
          echo "FAIL [", name, "]: defect in run at step ", k, ": ",
            d.name, ": ", d.msg
        if not stepOk:
          failedAt = k
          break
      if failedAt >= 0:
        let minimal = shrinkCmdSeq(cmds, newModel, newSys, run, shrinkCmd)
        echo "FAIL [", name, "]: seed: ", rr.seed, ", case ", i,
          ", diverged at step ", failedAt, ", minimal commands: ", $minimal
        return false
    if isReplay:
      echo "ok [", name, "]: replay seed ", rr.seed, ", ", n, " cases"
    else:
      echo "ok [", name, "]: ", n, " cases"
  result = true
  for seed in regressions:
    var rr = initRng(seed)
    if not runCase(rr, isReplay = true): return false
  if not runCase(r, isReplay = false): return false
