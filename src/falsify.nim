## falsify — property-based testing for Nim.
##
## Falsify your properties: generate random inputs, shrink failures to
## minimal counterexamples, reproduce everything from a seed.
##
## Why this exists: the only previous Nim PBT library (nim-quicktest) is an
## unmaintained 2017 alpha that doesn't compile on the current toolchain.
## This is a small, dependency-free harness: a seeded xorshift64* RNG
## (deterministic across platforms), generator combinators, shrinking,
## and a `forAll` driver with failure reporting.
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

proc genFloat*(r: var Rng, lo, hi: float): float =
  ## Float in [lo, hi).
  ##
  ## Bug-finding bias: with probability 1/4, returns `lo`, or 0.0 when it
  ## lies in [lo, hi); otherwise uniform over [lo, hi).
  doAssert lo <= hi, "genFloat: lo > hi"
  if r.below(4) == 0:
    if lo <= 0.0 and 0.0 < hi and r.below(2) == 0:
      return 0.0
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
  doAssert maxRetries > 0, "genSuchThat: maxRetries must be positive"
  for _ in 0 ..< maxRetries:
    let x = gen(r)
    if pred(x): return x
  raise newException(ValueError,
    "genSuchThat: predicate not satisfied after " & $maxRetries &
    " draws; narrow the generator (build the constraint into generation)" &
    " rather than filtering a wide one")

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

proc forAll*[T](name: string, r: var Rng, n: int,
                gen: proc(r: var Rng): T,
                prop: proc(x: T): bool,
                shrink: proc(x: T): seq[T] = nil): bool =
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
  result = true
  for i in 0 ..< n:
    r.size = min(100, i * 100 div max(n, 1))
    let x = gen(r)
    var failed = false
    try:
      failed = not prop(x)
    except CatchableError as e:
      echo "FAIL [", name, "]: exception on input: ", e.msg
      failed = true
    except Defect as d:
      echo "FAIL [", name, "]: defect on input: ", d.name, ": ", d.msg
      failed = true
    if failed:
      result = false
      var minimal = x
      if shrink != nil:
        var cands = shrink(minimal)
        while cands.len > 0:
          var progressed = false
          for c in cands:
            var cf = false
            try: cf = not prop(c)
            except CatchableError: cf = true
            except Defect: cf = true
            if cf:
              minimal = c
              cands = shrink(minimal)
              progressed = true
              break
          if not progressed: break
      echo "FAIL [", name, "]: seed: ", r.seed, ", case ", i,
        ", minimal input: ", $minimal
      return false
  echo "ok [", name, "]: ", n, " cases"
