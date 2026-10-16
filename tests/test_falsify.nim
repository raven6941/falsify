## Self-tests for falsify: the harness must catch known-broken properties,
## shrink to minimal counterexamples, and stay deterministic per seed.

import falsify
import std/math
import std/algorithm

var failures = 0
template check(name: string, cond: bool) =
  if cond: echo "ok: ", name
  else:
    echo "FAIL: ", name
    inc failures

# Determinism: same seed -> same stream.
var r1 = initRng(42)
var r2 = initRng(42)
var same = true
for _ in 0 ..< 100:
  if r1.next() != r2.next(): same = false
check("rng deterministic per seed", same)

# Different seeds -> different streams (overwhelmingly likely).
var r3 = initRng(1)
var r4 = initRng(2)
var diff = false
for _ in 0 ..< 10:
  if r3.next() != r4.next(): diff = true
check("rng differs across seeds", diff)

# Bounds.
var r = initRng(7)
var okBounds = true
for _ in 0 ..< 1000:
  if r.below(10) notin 0 ..< 10: okBounds = false
  if r.genInt(-5, 5) notin -5 .. 5: okBounds = false
  let f = r.genFloat(0.0, 1.0)
  if f < 0.0 or f >= 1.0: okBounds = false
  let c = r.genChar()
  if c < ' ' or c > '~': okBounds = false
  if r.genString(20).len > 20: okBounds = false
  if r.genSeq(15, proc(r: var Rng): int = r.genInt(0, 9)).len > 15: okBounds = false
check("generators respect bounds", okBounds)

# forAll passes a true property.
var r5 = initRng(99)
check("forAll passes true property",
  forAll("true-prop", r5, 100,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(x: int): bool = x - x == 0,
    shrinkInt))

# forAll falsifies a broken property.
var r6 = initRng(99)
check("forAll falsifies broken property",
  not forAll("broken-prop", r6, 100,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(x: int): bool = x <= 7,
    shrinkInt))

# shrinkInt minimality: the greedy shrink loop must reach the true boundary.
proc shrinkLoop(x: int, fails: proc(c: int): bool): int =
  var m = x
  var cands = shrinkInt(m)
  while cands.len > 0:
    var progressed = false
    for c in cands:
      if fails(c):
        m = c
        cands = shrinkInt(m)
        progressed = true
        break
    if not progressed: break
  m
check("shrinkInt reaches minimal 8 for x <= 7",
  shrinkLoop(42, proc(c: int): bool = not (c <= 7)) == 8)
check("shrinkInt reaches minimal -8 for x >= -7",
  shrinkLoop(-42, proc(c: int): bool = not (c >= -7)) == -8)

# shrinkSeq: candidates include empty and single drops.
let s = @[1, 2, 3]
let sc = shrinkSeq(s, shrinkInt)
check("shrinkSeq proposes empty", newSeq[int]() in sc)
check("shrinkSeq proposes single drops",
  @[2, 3] in sc and @[1, 3] in sc and @[1, 2] in sc)

# Exceptions in the property count as failures.
var r7 = initRng(5)
check("forAll treats exceptions as failures",
  not forAll("raises", r7, 10,
    proc(r: var Rng): int = 0,
    proc(x: int): bool = raise newException(ValueError, "boom")))

# Edge bias (issue #1): interesting values appear with the designed probability.
#
# genInt(-100, 100): interesting set is {-100, 100, 0, -1, 1}, 5 of 201 values.
# P(draw is interesting) = 1/4 + 3/4 * 5/201 ~ 0.269. Over 4000 draws the
# observed fraction must sit near the design point (band is ~+-9 sigma).
var rb = initRng(424242)
var edgeHits = 0
const EdgeDraws = 4000
for _ in 0 ..< EdgeDraws:
  if rb.genInt(-100, 100) in [-100, 100, 0, -1, 1]: inc edgeHits
let edgeFrac = edgeHits.float / EdgeDraws.float
check("genInt edge bias near designed 1/4+", edgeFrac > 0.20 and edgeFrac < 0.35)

# The headline case from the issue: 0 must show up fast.
# P(miss in 200 draws) ~ 1.7e-5 per seed; checked across seeds, fixed => deterministic.
for seed in [11'u64, 424242'u64, 999999'u64]:
  var r0 = initRng(seed)
  var sawZero = false
  for _ in 0 ..< 200:
    if r0.genInt(-100, 100) == 0: sawZero = true
  check("genInt(-100,100): 0 appears in 200 draws (seed " & $seed & ")", sawZero)

# Degenerate and lopsided ranges: bias must respect bounds, never invent values.
var rd = initRng(31337)
var degOk = true
for _ in 0 ..< 500:
  if rd.genInt(5, 5) != 5: degOk = false
  if rd.genInt(7, 9) notin 7 .. 9: degOk = false
  if rd.genInt(-3, -1) notin -3 .. -1: degOk = false
check("genInt bias respects degenerate/lopsided ranges", degOk)

# genString / genSeq: empty and single-element with elevated probability.
# P(len 0) = 1/4*1/2 + 3/4*1/51 ~ 0.14; missing it in 200 draws ~ 1e-13.
var rs = initRng(777)
var sawEmpty = false
var sawSingle = false
for _ in 0 ..< 200:
  let n = rs.genString(50).len
  if n == 0: sawEmpty = true
  if n == 1: sawSingle = true
check("genString: empty appears in 200 draws", sawEmpty)
check("genString: single-char appears in 200 draws", sawSingle)

var rq = initRng(778)
var sawEmptySeq = false
for _ in 0 ..< 200:
  if rq.genSeq(30, proc(r: var Rng): int = r.genInt(0, 9)).len == 0:
    sawEmptySeq = true
check("genSeq: empty appears in 200 draws", sawEmptySeq)

# genFloat: 0.0 and lo appear fast; bounds contract ([lo, hi)) still holds.
var rf = initRng(31337)
var sawFZero = false
var sawFLo = false
var fBoundsOk = true
for _ in 0 ..< 200:
  let f = rf.genFloat(-1.0, 1.0)
  if f == 0.0: sawFZero = true
  if f == -1.0: sawFLo = true
  if f < -1.0 or f >= 1.0: fBoundsOk = false
check("genFloat: 0.0 appears in 200 draws", sawFZero)
check("genFloat: lo appears in 200 draws", sawFLo)
check("genFloat bias keeps [lo, hi) contract", fBoundsOk)

# The bias is part of the stream: same seed -> same biased sequence.
var rg1 = initRng(424242)
var rg2 = initRng(424242)
var biasDet = true
for _ in 0 ..< 200:
  if rg1.genInt(-100, 100) != rg2.genInt(-100, 100): biasDet = false
  if rg1.genString(20) != rg2.genString(20): biasDet = false
  if rg1.genFloat(-1.0, 1.0) != rg2.genFloat(-1.0, 1.0): biasDet = false
  if rg1.genSeq(10, proc(r: var Rng): int = r.genInt(0, 9)) !=
     rg2.genSeq(10, proc(r: var Rng): int = r.genInt(0, 9)): biasDet = false
check("biased generators deterministic per seed", biasDet)

# Combinators (issue #2): weighted/categorical choice.
#
# genFrequency with weights 1:2:3 over 6000 draws: expected 1000/2000/3000,
# sigma ~29; bands are ~+-10 sigma. The "generators" here are constant
# expressions — the macros take expressions, not procs.
var rw = initRng(2024)
var wCounts = [0, 0, 0]
for _ in 0 ..< 6000:
  let v = rw.genFrequency([(1, 0), (2, 1), (3, 2)])
  inc wCounts[v]
check("genFrequency weights ~1:2:3",
  wCounts[0] in 700 .. 1300 and wCounts[1] in 1700 .. 2300 and
  wCounts[2] in 2700 .. 3300)

# genOneOf: covers all, roughly uniform (expected 1000 each, sigma ~26).
var ro = initRng(55)
var oSeen = [false, false, false]
var oCounts = [0, 0, 0]
for _ in 0 ..< 3000:
  let v = ro.genOneOf([0, 1, 2])
  oSeen[v] = true
  inc oCounts[v]
check("genOneOf covers all", oSeen[0] and oSeen[1] and oSeen[2])
check("genOneOf roughly uniform",
  oCounts[0] in 850 .. 1150 and oCounts[1] in 850 .. 1150 and
  oCounts[2] in 850 .. 1150)

# Real generator expressions, including one capturing a local — the case a
# proc-based design cannot express (capturing lambdas infer {.closure.}).
let lo = -50
var rcap = initRng(31)
var capOk = true
var capSawConst = false
for _ in 0 ..< 300:
  let v = rcap.genOneOf([rcap.genInt(lo, lo + 10), 999])
  if v == 999: capSawConst = true
  elif v notin lo .. lo + 10: capOk = false
check("genOneOf with capturing generator", capOk and capSawConst)

# Laziness: exactly one branch is evaluated per draw.
var evalCount = 0
var rl = initRng(7)
for _ in 0 ..< 100:
  discard rl.genOneOf([block: inc evalCount; 1, block: inc evalCount; 2])
check("genOneOf evaluates exactly one branch", evalCount == 100)

# genElements: only ever picks from xs, and covers all of them.
var re = initRng(66)
var eSeen = [false, false, false, false]
var eOnly = true
for _ in 0 ..< 200:
  case re.genElements(["a", "b", "c", "d"])
  of "a": eSeen[0] = true
  of "b": eSeen[1] = true
  of "c": eSeen[2] = true
  of "d": eSeen[3] = true
  else: eOnly = false
check("genElements only picks from xs", eOnly)
check("genElements covers all", eSeen[0] and eSeen[1] and eSeen[2] and eSeen[3])

# Empty inputs are usage errors: compile-time for the macros (literal `[]`),
# runtime for genElements.
static:
  var rsc = initRng(1)
  assert not compiles(rsc.genOneOf([])), "genOneOf([]) must not compile"
  assert not compiles(rsc.genFrequency([])), "genFrequency([]) must not compile"
check("empty genOneOf/genFrequency are compile-time errors", true)

var emptyErrs = 0
try:
  var rz = initRng(1)
  discard rz.genElements(newSeq[int]())
except AssertionDefect:
  inc emptyErrs
try:
  var rz = initRng(1)
  discard rz.genFrequency([(1, 10), (0, 20)])
except AssertionDefect:
  inc emptyErrs
check("empty genElements / non-positive weight raise", emptyErrs == 2)

# genShuffle: output is a permutation of the input; input is untouched.
var shuffleR = initRng(424242)
var shIsPerm = true
var shInputUntouched = true
for _ in 0 ..< 300:
  let n = shuffleR.below(15)
  var xs = newSeq[int](n)
  for i in 0 ..< n: xs[i] = shuffleR.genInt(-50, 50)
  let copy = xs
  let shuffled = shuffleR.genShuffle(xs)
  if sorted(shuffled) != sorted(copy): shIsPerm = false
  if xs != copy: shInputUntouched = false
check("genShuffle output is a permutation of the input", shIsPerm)
check("genShuffle leaves the input untouched", shInputUntouched)

# genShuffle with duplicates: multiset preserved, not just the set.
var dupR = initRng(99)
var dupOk = true
for _ in 0 ..< 100:
  let shuffled = dupR.genShuffle(@[1, 1, 2, 3, 3, 3])
  if sorted(shuffled) != @[1, 1, 2, 3, 3, 3]: dupOk = false
check("genShuffle preserves duplicates", dupOk)

# genPermutation: a permutation of 0 ..< n.
var pmR = initRng(424242)
var pmIsPerm = true
for _ in 0 ..< 200:
  let n = pmR.below(20)
  let p = pmR.genPermutation(n)
  var seen = newSeq[bool](n)
  for v in p:
    if v < 0 or v >= n: pmIsPerm = false
    elif seen[v]: pmIsPerm = false
    else: seen[v] = true
  if p.len != n: pmIsPerm = false
check("genPermutation yields a permutation of 0..<n", pmIsPerm)

# Determinism: same seed -> identical permutation; different seeds differ.
var d1 = initRng(12345)
var d2 = initRng(12345)
var d3 = initRng(54321)
let pA = d1.genShuffle(@[1, 2, 3, 4, 5, 6, 7, 8])
let pB = d2.genShuffle(@[1, 2, 3, 4, 5, 6, 7, 8])
let pC = d3.genShuffle(@[1, 2, 3, 4, 5, 6, 7, 8])
check("genShuffle deterministic per seed", pA == pB)
check("genShuffle varies across seeds", pA != pC)

# Empty / single-element: returned unchanged, and no RNG is consumed
# (the trivial loop draws nothing).
var z1 = initRng(777)
let zEmpty = z1.genShuffle(newSeq[int]())
let zOne = z1.genShuffle(@[42])
var z2 = initRng(777)
check("genShuffle empty and singleton return unchanged",
  zEmpty.len == 0 and zOne == @[42] and z1.next() == z2.next())
var q1 = initRng(888)
let qp = q1.genPermutation(1)
var q2 = initRng(888)
check("genPermutation(1) draws nothing and is [0]",
  qp == @[0] and q1.next() == q2.next())

# Negative n is a usage error.
var negErrs = 0
try:
  var nr = initRng(1)
  discard nr.genPermutation(-1)
except AssertionDefect:
  inc negErrs
check("genPermutation with negative n raises", negErrs == 1)

# Combinators are part of the stream: same seed -> same sequence.
var rc1 = initRng(424242)
var rc2 = initRng(424242)
var combDet = true
for _ in 0 ..< 100:
  if rc1.genElements([1, 2, 3]) != rc2.genElements([1, 2, 3]): combDet = false
  if rc1.genOneOf([rc1.genInt(0, 9), rc1.genInt(10, 19)]) !=
     rc2.genOneOf([rc2.genInt(0, 9), rc2.genInt(10, 19)]): combDet = false
  if rc1.genFrequency([(3, rc1.genInt(0, 9)), (1, rc1.genInt(10, 19))]) !=
     rc2.genFrequency([(3, rc2.genInt(0, 9)), (1, rc2.genInt(10, 19))]): combDet = false
check("combinators deterministic per seed", combDet)

# genSuchThat: even numbers from a plain genInt stream.
var rse = initRng(424242)
var allEven = true
for _ in 0 ..< 200:
  let x = rse.genSuchThat(proc(r: var Rng): int = r.genInt(0, 99),
                          proc(x: int): bool = x mod 2 == 0)
  if x mod 2 != 0: allEven = false
check("genSuchThat generates even numbers", allEven)

# genSuchThat: an impossible predicate raises ValueError at the cap.
var raised = false
try:
  var rst = initRng(1)
  discard rst.genSuchThat(proc(r: var Rng): int = r.genInt(0, 9),
                          proc(x: int): bool = false)
except ValueError:
  raised = true
check("genSuchThat raises ValueError on impossible predicate", raised)

# genSuchThat: non-positive maxRetries is a usage error.
var capErrs = 0
try:
  var rsc2 = initRng(1)
  discard rsc2.genSuchThat(proc(r: var Rng): int = r.genInt(0, 9),
                           proc(x: int): bool = true, maxRetries = 0)
except AssertionDefect:
  inc capErrs
check("genSuchThat rejects non-positive maxRetries", capErrs == 1)

# genSuchThat is part of the stream: same seed -> same result.
var rsu1 = initRng(777)
var rsu2 = initRng(777)
var suchDet = true
for _ in 0 ..< 50:
  if rsu1.genSuchThat(proc(r: var Rng): int = r.genInt(0, 99),
                      proc(x: int): bool = x mod 2 == 0) !=
     rsu2.genSuchThat(proc(r: var Rng): int = r.genInt(0, 99),
                      proc(x: int): bool = x mod 2 == 0): suchDet = false
check("genSuchThat deterministic per seed", suchDet)

# --- Sized and recursive generation ---

type Tree = ref object
  kids: seq[Tree]  # empty = leaf

proc genTree(r: var Rng): Tree =
  r.genRecursive(
    proc(r: var Rng): Tree = Tree(kids: @[]),
    proc(r: var Rng, sub: proc(r: var Rng): Tree): Tree =
      Tree(kids: @[sub(r), sub(r)]))

proc treeDepth(t: Tree): int =
  if t.kids.len == 0: 0
  else:
    var m = 0
    for k in t.kids: m = max(m, treeDepth(k))
    1 + m

# genRecursive terminates and stays bounded: 500 trees at size 100.
var rbig = initRng(424242)
rbig.size = 100
var maxDepth = 0
for _ in 0 ..< 500:
  maxDepth = max(maxDepth, treeDepth(genTree(rbig)))
check("genRecursive terminates with bounded depth", maxDepth > 0 and maxDepth < 40)

# Depth distribution shifts with size: size 0 is all leaves...
var rzero = initRng(7)
rzero.size = 0
var allLeaves = true
for _ in 0 ..< 200:
  if treeDepth(genTree(rzero)) != 0: allLeaves = false
check("genRecursive at size 0 generates only leaves", allLeaves)

# ...while larger sizes grow deeper trees.
var rmid = initRng(7)
rmid.size = 50
var deepSeen = false
for _ in 0 ..< 200:
  if treeDepth(genTree(rmid)) >= 2: deepSeen = true
check("genRecursive grows deeper trees at larger size", deepSeen)

# genSized passes the ambient size through.
var rsz = initRng(1)
rsz.size = 42
check("genSized exposes the ambient size",
  rsz.genSized(proc(r: var Rng, s: int): int = s) == 42)

# forAll grows the ambient size across cases: 0 first, ~100 last, monotone.
var rfa = initRng(1)
var seenSizes: seq[int] = @[]
discard forAll("size-growth", rfa, 50,
  proc(r: var Rng): int =
    seenSizes.add(r.size)
    r.size,
  proc(x: int): bool = true)
var mono = seenSizes.len == 50 and seenSizes[0] == 0 and seenSizes[^1] >= 90
for i in 1 ..< seenSizes.len:
  if seenSizes[i] < seenSizes[i-1]: mono = false
check("forAll grows ambient size 0..~100 across cases", mono)

# --- Seed reporting (issue #9) ---

import std/os
import std/strutils

# initRng records the effective seed (after the 0 -> default mapping).
check("initRng records the seed",
  initRng(424242).seed == 424242'u64 and initRng(0).seed != 0)

# Capture stdout while running body (for asserting on forAll's report).
template captureOutput(body: untyped): string =
  let capPath = getTempDir() / "falsify_capture.txt"
  let savedOut = stdout
  stdout = open(capPath, fmWrite)
  try:
    body
  finally:
    close(stdout)
    stdout = savedOut
  readFile(capPath)

proc failingPropRun(seed: uint64) =
  var r = initRng(seed)
  discard forAll("replay-me", r, 100,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(x: int): bool = x <= 7,
    shrinkInt)

let outA = captureOutput(failingPropRun(424242))
let outB = captureOutput(failingPropRun(424242))
check("same seed replays identical forAll failure output", outA == outB)
check("FAIL line prints the seed", "seed: 424242" in outA)
let outC = captureOutput(failingPropRun(99))
check("FAIL line prints the actual seed used", "seed: 99" in outC)

# --- Defects are failures, not crashes (issue #10) ---

proc failingAssertRun(seed: uint64) =
  var r = initRng(seed)
  discard forAll("assert-replay", r, 100,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(x: int): bool =
      assert x <= 7
      true,
    shrinkInt)

# An assertion failure in the property is reported and returns false;
# the suite binary continues (this check itself runs after it).
var rd10 = initRng(424242)
check("forAll treats AssertionDefect as a failure",
  not forAll("assert-fails", rd10, 100,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(x: int): bool =
      assert x <= 7
      true,
    shrinkInt))

let outD = captureOutput(failingAssertRun(424242))
check("AssertionDefect failure prints seed and minimal input",
  "defect on input" in outD and "seed: 424242" in outD and
  "minimal input: 8" in outD)

# --- Multi-input properties (issue #13) ---

# genPair: components come from the element generators, and the stream
# is deterministic per seed (bias included).
var rp1 = initRng(424242)
var rp2 = initRng(424242)
var pairOk = true
var pairDet = true
for _ in 0 ..< 200:
  let p1 = rp1.genPair(proc(r: var Rng): int = r.genInt(0, 9),
                       proc(r: var Rng): char = r.genChar())
  let p2 = rp2.genPair(proc(r: var Rng): int = r.genInt(0, 9),
                       proc(r: var Rng): char = r.genChar())
  if p1[0] notin 0 .. 9 or p1[1] < ' ' or p1[1] > '~': pairOk = false
  if p1 != p2: pairDet = false
check("genPair components respect bounds", pairOk)
check("genPair deterministic per seed", pairDet)

# genTriple: same smoke test.
var rt = initRng(3)
let tp = rt.genTriple(proc(r: var Rng): int = r.genInt(-5, 5),
                      proc(r: var Rng): bool = r.genBool(),
                      proc(r: var Rng): int = r.genInt(10, 20))
check("genTriple components respect bounds",
  tp[0] in -5 .. 5 and tp[2] in 10 .. 20)

# shrinkPair: left component's candidates first (most-aggressive first),
# each holding the other component fixed.
let psc = shrinkPair((4, 5), shrinkInt, shrinkInt)
check("shrinkPair shrinks left first, most-aggressive",
  psc.len > 0 and psc[0] == (0, 5))
check("shrinkPair then shrinks right holding left fixed",
  (4, 0) in psc)
var pairShared = true
for c in psc:
  if c[0] != 4 and c[1] != 5: pairShared = false
check("shrinkPair holds one component fixed", pairShared)

# shrinkTriple: all three components shrink, each holding the others.
let tsc = shrinkTriple((4, 5, 6), shrinkInt, shrinkInt, shrinkInt)
check("shrinkTriple shrinks each component holding the others",
  (0, 5, 6) in tsc and (4, 0, 6) in tsc and (4, 5, 0) in tsc)

# Minimality: greedy elementwise shrinking reaches the true boundary on
# whichever component the property constrains.
proc shrinkLoopPair(p: (int, int), fails: proc(c: (int, int)): bool): (int, int) =
  var m = p
  var cands = m.shrinkPair(shrinkInt, shrinkInt)
  while cands.len > 0:
    var progressed = false
    for c in cands:
      if fails(c):
        m = c
        cands = m.shrinkPair(shrinkInt, shrinkInt)
        progressed = true
        break
    if not progressed: break
  m
# Minimality: greedy elementwise shrinking minimizes *every* component it
# can while the property still fails — a pair whose first component alone
# is constrained still shrinks the second down to 0 if that stays failing
# (smaller still-failing pair = better minimal counterexample).
# QuickCheck-tuple semantics: one component at a time, left first, greedy.
check("shrinkPair reaches minimal (8, 0) for a <= 7",
  shrinkLoopPair((42, 50), proc(c: (int, int)): bool = not (c[0] <= 7)) == (8, 0))
check("shrinkPair reaches minimal (0, -8) for b >= -7",
  shrinkLoopPair((42, -50), proc(c: (int, int)): bool = not (c[1] >= -7)) == (0, -8))

# End to end: a broken two-input property (a + b <= 7) falsifies and
# shrinks to the minimal failing pair. Seed is fixed, so pin it exactly.
proc failingPairRun(seed: uint64) =
  var r = initRng(seed)
  discard forAll("pair-sum", r, 200,
    proc(r: var Rng): (int, int) =
      r.genPair(proc(r: var Rng): int = r.genInt(0, 100),
                proc(r: var Rng): int = r.genInt(0, 100)),
    proc(p: (int, int)): bool = p[0] + p[1] <= 7,
    proc(p: (int, int)): seq[(int, int)] =
      p.shrinkPair(shrinkInt, shrinkInt))

var rmp = initRng(424242)
check("forAll falsifies broken two-input property",
  not forAll("pair-sum", rmp, 200,
    proc(r: var Rng): (int, int) =
      r.genPair(proc(r: var Rng): int = r.genInt(0, 100),
                proc(r: var Rng): int = r.genInt(0, 100)),
    proc(p: (int, int)): bool = p[0] + p[1] <= 7,
    proc(p: (int, int)): seq[(int, int)] =
      p.shrinkPair(shrinkInt, shrinkInt)))
let outP = captureOutput(failingPairRun(424242))
check("two-input property shrinks to minimal failing pair",
  "minimal input: (8, 0)" in outP)

# --- Regression corpus (issue #14) ---

# A regression seed replays the identical failure: copy the seed from a
# failing run into the list and the same failure comes back, same seed,
# same minimal input, no manual stream bookkeeping.
proc replayFailRun() =
  var r = initRng(999)  # sweep seed is irrelevant; the replay fails first
  discard forAll("replay-int", r, 100,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(x: int): bool = x <= 7,
    shrinkInt, @[424242'u64])

let outReg = captureOutput(replayFailRun())
check("regression replay reproduces the identical failure",
  "seed: 424242" in outReg and "minimal input: 8" in outReg)

# A regression failure aborts before the random sweep runs: exactly one
# FAIL line (the replay's), no sweep output, returns false.
proc countSub(s, sub: string): int =
  var i = 0
  while true:
    let j = s.find(sub, i)
    if j < 0: break
    inc result
    i = j + 1
check("regression failure aborts before the sweep",
  countSub(outReg, "FAIL [replay-int]") == 1)
var rreg = initRng(999)
check("regression failure returns false",
  not forAll("replay-int", rreg, 100,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(x: int): bool = x <= 7,
    shrinkInt, @[424242'u64]))

# All regressions pass + sweep passes -> true; replays report their seeds.
proc replayOkRun() =
  var r = initRng(123)
  discard forAll("replay-ok", r, 50,
    proc(r: var Rng): int = r.genInt(0, 9),
    proc(x: int): bool = x >= 0,
    shrinkInt, @[11'u64, 22'u64])
let outOk = captureOutput(replayOkRun())
check("passing replays report their seeds",
  "replay seed 11" in outOk and "replay seed 22" in outOk and
  "ok [replay-ok]: 50 cases" in outOk)
var rrok = initRng(123)
check("all replays pass + sweep passes -> true",
  forAll("replay-ok", rrok, 50,
    proc(r: var Rng): int = r.genInt(0, 9),
    proc(x: int): bool = x >= 0,
    shrinkInt, @[11'u64, 22'u64]))

# Empty list is the old behavior, bit for bit: existing calls compile
# unchanged (exercised by every test above) and print the same lines.
proc noRegressRun() =
  var r = initRng(5)
  discard forAll("replay-empty", r, 10,
    proc(r: var Rng): int = r.genInt(0, 9),
    proc(x: int): bool = x >= 0,
    shrinkInt)
check("empty regression list behaves like before",
  "replay seed" notin captureOutput(noRegressRun()))

# --- Coverage reporting: classify/collect + cover (issue #17) ---

proc covRun(seed: uint64, coverReqs: seq[CoverReq] = @[]) =
  var r = initRng(seed)
  discard forAll("cov-int", r, 200,
    proc(r: var Rng): int = r.genInt(-100, 100),
    proc(x: int): bool = true,
    classify = proc(x: int): seq[string] =
      if x in [-100, 100, 0, -1, 1]: @["edge"] else: @["bulk"],
    cover = coverReqs)

let covA = captureOutput(covRun(424242))
let covB = captureOutput(covRun(424242))
check("coverage table deterministic per seed", covA == covB)
check("coverage table reports both classes",
  "cover [cov-int]: \"bulk\": 69.0% (138/200)" in covA and
  "cover [cov-int]: \"edge\": 31.0% (62/200)" in covA)
check("coverage table sorts by count desc",
  covA.find("\"bulk\"") < covA.find("\"edge\""))

# cover met -> true; unmet -> false (fixed seed, deterministic).
var rcm = initRng(424242)
check("cover met returns true",
  forAll("cov-met", rcm, 200,
    proc(r: var Rng): int = r.genInt(-100, 100),
    proc(x: int): bool = true,
    classify = proc(x: int): seq[string] =
      if x in [-100, 100, 0, -1, 1]: @["edge"] else: @["bulk"],
    cover = @[("edge", 30.0)]))
var rcu = initRng(424242)
check("cover unmet returns false",
  not forAll("cov-unmet", rcu, 200,
    proc(r: var Rng): int = r.genInt(-100, 100),
    proc(x: int): bool = true,
    classify = proc(x: int): seq[string] =
      if x in [-100, 100, 0, -1, 1]: @["edge"] else: @["bulk"],
    cover = @[("edge", 50.0)]))
let covFail = captureOutput(covRun(424242, @[("edge", 50.0)]))
check("coverage shortfall prints evidence then verdict",
  "coverage shortfall" in covFail and
  "\"edge\": 31.0% < required 50.0%" in covFail)

# cover without classify is a usage error: fails loud.
var raisedCover = false
try:
  var rnc = initRng(7)
  discard forAll("cov-noclass", rnc, 10,
    proc(r: var Rng): int = 1,
    proc(x: int): bool = true,
    cover = @[("x", 1.0)])
except AssertionDefect:
  raisedCover = true
check("cover without classify raises AssertionDefect", raisedCover)

# A raising classify is a failure, reported with the property name.
var rrc = initRng(7)
check("raising classify fails the run",
  not forAll("cov-raise", rrc, 10,
    proc(r: var Rng): int = r.genInt(0, 9),
    proc(x: int): bool = true,
    classify = proc(x: int): seq[string] =
      raise newException(ValueError, "boom")))
let covRaiseOut = captureOutput(block:
  var rrr = initRng(7)
  discard forAll("cov-raise2", rrr, 10,
    proc(r: var Rng): int = r.genInt(0, 9),
    proc(x: int): bool = true,
    classify = proc(x: int): seq[string] =
      raise newException(ValueError, "boom")))
check("raising classify reported like a failure",
  "FAIL [cov-raise2]: exception in classify: boom" in covRaiseOut)

# Classifying never perturbs the stream: same seed, same failure report.
proc failingClassifyRun(seed: uint64) =
  var r = initRng(seed)
  discard forAll("replay-me", r, 100,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(x: int): bool = x <= 7,
    shrinkInt,
    classify = proc(x: int): seq[string] = @["any"])
check("classify does not perturb the failure stream",
  captureOutput(failingClassifyRun(424242)) == captureOutput(failingPropRun(424242)))

# Duplicate tags in one classify result count once per case.
let dupOut = captureOutput(block:
  var rdup = initRng(11)
  discard forAll("cov-dup", rdup, 100,
    proc(r: var Rng): int = r.genInt(0, 9),
    proc(x: int): bool = true,
    classify = proc(x: int): seq[string] = @["a", "a", "b"]))
check("duplicate tags counted once per case",
  "\"a\": 100.0% (100/100)" in dupOut and "\"b\": 100.0% (100/100)" in dupOut)

# --- Shrinker completeness: shrinkFloat, shrinkChar, shrinkString (#18) ---

# shrinkFloat: 0.0 first, then halving toward zero.
let sf8 = shrinkFloat(8.0)
check("shrinkFloat most aggressive first",
  sf8.len > 2 and sf8[0] == 0.0 and sf8[1] == 4.0 and sf8[2] == 2.0)
check("shrinkFloat converges toward zero",
  sf8[^1] == 0.0 or abs(sf8[^1]) < 1e-300)
check("shrinkFloat NaN shrinks to 0.0 only",
  shrinkFloat(NaN) == @[0.0])
check("shrinkFloat infinities shrink to 0.0",
  shrinkFloat(Inf) == @[0.0] and shrinkFloat(-Inf) == @[0.0])
check("shrinkFloat of 0.0 has no candidates", shrinkFloat(0.0) == @[])

# End-to-end: a float threshold property shrinks to 0.0.
proc floatThreshuffleRun(seed: uint64) =
  var r = initRng(seed)
  discard forAll("float-thresh", r, 500,
    proc(r: var Rng): float = r.genFloat(0.0, 10.0),
    proc(x: float): bool = x >= 5.0,
    shrinkFloat)
let floatOut = captureOutput(floatThreshuffleRun(424242))
check("float threshold shrinks to minimal 0.0",
  "FAIL [float-thresh]" in floatOut and "minimal input: 0.0" in floatOut)

# shrinkChar: ' ' first, then neighbor toward ' ', then halving.
let scd = shrinkChar('d')
check("shrinkChar most aggressive first",
  scd.len > 2 and scd[0] == ' ' and scd[1] == 'c')
check("shrinkChar of space has no candidates", shrinkChar(' ') == @[])
check("shrinkChar stays in printable range for generated chars",
  block:
    var okc = true
    for o in 32 .. 126:
      for c in shrinkChar(chr(o)):
        if ord(c) < 32 or ord(c) > 126: okc = false
    okc)

# shrinkString: "", halves, single drops, per-char shrinks.
let ssabc = shrinkString("abc")
check("shrinkString most aggressive first",
  ssabc.len > 3 and ssabc[0] == "" and "bc" in ssabc and "ab" in ssabc)
check("shrinkString composes shrinkChar",
  " z" in shrinkString("zz") and "z " in shrinkString("zz"))
check("shrinkString of empty has no candidates", shrinkString("") == @[])

# End-to-end: a short-string property shrinks to "".
proc stringLenRun(seed: uint64) =
  var r = initRng(seed)
  discard forAll("string-len", r, 200,
    proc(r: var Rng): string = r.genString(5),
    proc(s: string): bool = s.len >= 2,
    shrinkString)
let stringOut = captureOutput(stringLenRun(424242))
check("short-string property shrinks to empty",
  "FAIL [string-len]" in stringOut and "minimal input: " in stringOut and
  stringOut.find("minimal input: \n") >= 0)

# genMap: draws exactly gen's draws, transformed.
var rMap = initRng(99)
var mapOk = true
for _ in 0 ..< 200:
  let v = rMap.genMap(proc(r: var Rng): int = r.genInt(0, 9),
                      proc(x: int): int = 2 * x)
  if v mod 2 != 0 or v < 0 or v > 18: mapOk = false
check("genMap transforms drawn values", mapOk)

# genMap: same seed -> same stream as the underlying generator's draws.
var rMapA = initRng(1234)
var rMapB = initRng(1234)
var mapDet = true
for _ in 0 ..< 50:
  let a = rMapA.genMap(proc(r: var Rng): int = r.genInt(-100, 100),
                       proc(x: int): int = x + 1)
  let b = rMapB.genInt(-100, 100) + 1
  if a != b: mapDet = false
check("genMap draws equal underlying generator draws", mapDet)

# genBind: sequencing is literal — genBind(gen, k) == let x = gen(r) in k(r, x).
var rBindA = initRng(777)
var rBindB = initRng(777)
var bindSeq = true
for _ in 0 ..< 50:
  let a = rBindA.genBind(proc(r: var Rng): int = r.genInt(1, 8),
                         proc(r: var Rng, n: int): seq[bool] =
                           r.genSeq(n, genBool))
  let n = rBindB.genInt(1, 8)
  let b = rBindB.genSeq(n, genBool)
  if a != b: bindSeq = false
check("genBind sequences gen then continuation", bindSeq)

# genBind: the drawn value reaches the continuation — encode it in the output
# and compare against the manual sequence.
var rBindTh = initRng(31337)
var rBindThM = initRng(31337)
var bindThread = true
for _ in 0 ..< 50:
  let a = rBindTh.genBind(proc(r: var Rng): int = r.genInt(1, 8),
                          proc(r: var Rng, n: int): int =
                            n * 1000 + r.genInt(0, 9))
  let n = rBindThM.genInt(1, 8)
  let b = n * 1000 + rBindThM.genInt(0, 9)
  if a != b: bindThread = false
check("genBind threads the drawn value", bindThread)

# End-to-end: genMap inside a forAll property.
var rMapProp = initRng(424242)
check("forAll with genMap generator passes",
  forAll("map-double", rMapProp, 100,
    proc(r: var Rng): int =
      r.genMap(proc(r: var Rng): int = r.genInt(-50, 50),
                proc(x: int): int = 2 * x),
    proc(x: int): bool = x mod 2 == 0,
    shrinkInt))

# assume: precondition discards non-satisfying cases; property checked on the rest.
var rAssume1 = initRng(424242)
var assumeOk = false
let assumeOut = captureOutput:
  assumeOk = forAll("assume-pos", rAssume1, 200,
    proc(r: var Rng): int = r.genInt(-10, 10),
    proc(x: int): bool = x >= 1,
    shrinkInt,
    assume = proc(x: int): bool = x > 0)
check("assume discards non-satisfying cases and passes", assumeOk)
check("assume reports discard count in ok line",
  "ok [assume-pos]" in assumeOut and "discarded" in assumeOut)

# assume: same seed -> identical output, so the discard count is deterministic.
var rAssume2 = initRng(424242)
let assumeOut2 = captureOutput:
  discard forAll("assume-pos", rAssume2, 200,
    proc(r: var Rng): int = r.genInt(-10, 10),
    proc(x: int): bool = x >= 1,
    shrinkInt,
    assume = proc(x: int): bool = x > 0)
check("assume discard count deterministic per seed", assumeOut == assumeOut2)

# assume: unsatisfiable precondition hits the discard cap and fails loud.
var rAssume3 = initRng(7)
var gaveUpOk = true
let gaveUpOut = captureOutput:
  gaveUpOk = forAll("assume-impossible", rAssume3, 200,
    proc(r: var Rng): int = r.genInt(0, 10),
    proc(x: int): bool = true,
    assume = proc(x: int): bool = x == 424242,
    maxDiscards = 20)
check("unsatisfiable assume fails the run", not gaveUpOk)
check("unsatisfiable assume prints gave-up line with counts",
  "FAIL [assume-impossible]" in gaveUpOut and
  "gave up: discarded 21 > maxDiscards 20" in gaveUpOut)

# assume: maxDiscards = 0 tolerates no discards.
var rAssume4 = initRng(7)
var zeroOk = true
let zeroOut = captureOutput:
  zeroOk = forAll("assume-zero", rAssume4, 200,
    proc(r: var Rng): int = r.genInt(-10, -1),
    proc(x: int): bool = true,
    assume = proc(x: int): bool = x > 0,
    maxDiscards = 0)
check("maxDiscards = 0 gives up on first discard", not zeroOk)
check("maxDiscards = 0 prints gave-up line", "gave up" in zeroOut)

# assume: an exception inside assume is a programming error — fails loud.
var rAssume5 = initRng(7)
var assumeExOk = true
let assumeExOut = captureOutput:
  assumeExOk = forAll("assume-ex", rAssume5, 50,
    proc(r: var Rng): int = r.genInt(5, 5),
    proc(x: int): bool = true,
    assume = proc(x: int): bool =
      if x == 5: raise newException(ValueError, "boom")
      else: x >= 0)
check("exception in assume fails the run", not assumeExOk)
check("exception in assume reported like a failure",
  "FAIL [assume-ex]: exception in assume: boom" in assumeExOut)

# --- Health checks (issue #25) ---

# approxSize: order-of-magnitude byte sizes.
check("approxSize scalar", approxSize(5) == sizeof(int))
check("approxSize string", approxSize("abc") == sizeof("") + 3)
check("approxSize seq", approxSize(@[1, 2, 3]) == sizeof(@[1]) + 3 * sizeof(1))

# trippedChecks logic, direct.
let h0 = defaultHealth()
check("default health trips on nothing",
  trippedChecks(0.0, 100, 100, 0, h0) == {})
check("too-slow trips", hcTooSlow in trippedChecks(10000.0, 100, 100, 0, h0))
check("data-too-large trips",
  hcDataTooLarge in trippedChecks(0.0, 100 * 2 * (1 shl 20), 100, 0, h0))
check("discard-heavy trips",
  hcDiscardHeavy in trippedChecks(0.0, 100, 100, 90, h0))
check("few-examples trips",
  hcFewExamples in trippedChecks(0.0, 100, 5, 0, h0))
check("zero evaluated trips only few-examples",
  trippedChecks(0.0, 0, 0, 0, h0) == {hcFewExamples})
check("disabled thresholds never trip",
  trippedChecks(1e18, high(int), 100, 100,
    HealthChecks(maxMeanCaseMs: 0.0, maxMeanInputBytes: 0,
                 maxDiscardRatio: 0.0, minExamples: 0, failOn: {})) == {})

# Health warns by default: a slow property passes, with a HEALTH line.
proc slowRun(fail: bool): tuple[ok: bool, outp: string] =
  var r = initRng(7)
  let h = HealthChecks(maxMeanCaseMs: 1.0, maxMeanInputBytes: 0,
                       maxDiscardRatio: 0.0, minExamples: 0,
                       failOn: (if fail: {hcTooSlow} else: {}))
  var ok = false
  let o = captureOutput:
    ok = forAll("slow-prop", r, 20,
      proc(r: var Rng): int = r.genInt(0, 100),
      proc(x: int): bool = (os.sleep(5); x >= 0),
      shrinkInt, health = h)
  (ok, o)

let (slowOk, slowOut) = slowRun(false)
check("slow property still passes by default", slowOk)
check("slow property prints HEALTH too-slow line",
  "HEALTH [slow-prop]: too-slow" in slowOut)
let (slowFailOk, slowFailOut) = slowRun(true)
check("failOn turns too-slow into a failure", not slowFailOk)
check("failed health check prints FAIL line",
  "FAIL [slow-prop]: too-slow" in slowFailOut)

# data-too-large: fixed 5000-char inputs against a 1000-byte threshold.
var rBigH = initRng(11)
var bigOk = true
let bigOut = captureOutput:
  bigOk = forAll("big-prop", rBigH, 30,
    proc(r: var Rng): string = "x".repeat(5000),
    proc(s: string): bool = s.len == 5000,
    shrinkString,
    health = HealthChecks(maxMeanCaseMs: 0.0, maxMeanInputBytes: 1000,
                          maxDiscardRatio: 0.0, minExamples: 0,
                          failOn: {hcDataTooLarge}))
check("data-too-large fails the run when in failOn", not bigOk)
check("data-too-large line reports mean bytes",
  "HEALTH" notin bigOut and "FAIL [big-prop]: data-too-large" in bigOut)

# discard-heavy: an assume discarding ~90% trips the soft warning.
var rDisH = initRng(424242)
var disOk = true
let disOut = captureOutput:
  disOk = forAll("discardy", rDisH, 100,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(x: int): bool = true,
    shrinkInt,
    assume = proc(x: int): bool = x > 90,
    health = HealthChecks(maxMeanCaseMs: 0.0, maxMeanInputBytes: 0,
                          maxDiscardRatio: 0.5, minExamples: 0,
                          failOn: {hcDiscardHeavy}))
check("discard-heavy fails the run when in failOn", not disOk)
check("discard-heavy line reports the ratio",
  "FAIL [discardy]: discard-heavy" in disOut)

# few-examples: a 5-case sweep against a 10-case minimum warns but passes.
var rFewH = initRng(3)
var fewOk = false
let fewOut = captureOutput:
  fewOk = forAll("tiny", rFewH, 5,
    proc(r: var Rng): int = r.genInt(0, 10),
    proc(x: int): bool = x >= 0,
    shrinkInt,
    health = HealthChecks(maxMeanCaseMs: 0.0, maxMeanInputBytes: 0,
                          maxDiscardRatio: 0.0, minExamples: 10, failOn: {}))
check("few-examples warns but the sweep still passes", fewOk)
check("few-examples line printed",
  "HEALTH [tiny]: few-examples" in fewOut)

# Health never perturbs the stream: a failing run reports identically with
# health enabled or fully disabled.
proc failingHealthRun(seed: uint64, withHealth: bool): string =
  var r = initRng(seed)
  captureOutput:
    discard forAll("replay-health", r, 100,
      proc(r: var Rng): int = r.genInt(0, 100),
      proc(x: int): bool = x <= 7,
      shrinkInt,
      health = (if withHealth: defaultHealth() else: HealthChecks()))
check("health on/off: identical failure output",
  failingHealthRun(424242, true) == failingHealthRun(424242, false))

# --- Per-case deadline (issue #26) ---

# A deliberately slow property aborts the sweep with a DEADLINE line.
proc slowCaseRun(deadline: int): tuple[ok: bool, outp: string] =
  var r = initRng(13)
  var ok = false
  let o = captureOutput:
    ok = forAll("hangy", r, 50,
      proc(r: var Rng): int = r.genInt(0, 100),
      proc(x: int): bool = (os.sleep(500); x >= 0),
      shrinkInt,
      deadlineMs = deadline)
  (ok, o)

let (deadOk, deadOut) = slowCaseRun(50)
check("slow case aborts the sweep", not deadOk)
check("DEADLINE line names the property and case",
  "DEADLINE [hangy]: case " in deadOut)
check("DEADLINE line reports elapsed vs deadline",
  " took " in deadOut and "ms > 50ms deadline" in deadOut)
check("DEADLINE line carries the replay seed", "seed: 13" in deadOut)
check("deadline abort skips the shrink phase",
  "minimal input" notin deadOut)

# A fast property under a generous deadline passes untouched.
var rFastD = initRng(21)
var fastDOk = false
let fastDOut = captureOutput:
  fastDOk = forAll("snappy", rFastD, 100,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(x: int): bool = x >= 0,
    shrinkInt,
    deadlineMs = 10_000)
check("fast property passes under a generous deadline", fastDOk)
check("no DEADLINE line when no case is slow", "DEADLINE" notin fastDOut)

# deadlineMs=0 is the default: same seed -> byte-identical failure output.
proc failingPropDeadlineRun(seed: uint64, deadline: int): string =
  var r = initRng(seed)
  captureOutput:
    discard forAll("replay-me", r, 100,
      proc(r: var Rng): int = r.genInt(0, 100),
      proc(x: int): bool = x <= 7,
      shrinkInt,
      deadlineMs = deadline)
check("deadlineMs=0 reproduces current behavior byte-for-byte",
  failingPropDeadlineRun(424242, 0) == outA)

# --- Stateful/model-based testing (#29) ---

type
  CounterCmd = enum ccInc, ccDec, ccReset
  CounterModel = object
    val: int
  CounterSys = object
    val: int
    seenReset: bool

proc newCounterModel(): CounterModel = CounterModel(val: 0)
proc newCounterSys(): CounterSys = CounterSys(val: 0)

proc runCounter(sys: var CounterSys, m: var CounterModel,
                c: CounterCmd): bool =
  ## The system under test has a bug: after any reset, `dec` subtracts 2
  ## instead of 1 (a stale-flag underflow). The model is the spec.
  case c
  of ccInc:
    inc m.val
    inc sys.val
  of ccDec:
    dec m.val
    if sys.seenReset: sys.val -= 2
    else: dec sys.val
  of ccReset:
    m.val = 0
    sys.val = 0
    sys.seenReset = true
  sys.val == m.val

proc runCounterFixed(sys: var CounterSys, m: var CounterModel,
                     c: CounterCmd): bool =
  ## The same system with the bug fixed: `dec` always subtracts 1.
  case c
  of ccInc: inc m.val; inc sys.val
  of ccDec: dec m.val; dec sys.val
  of ccReset:
    m.val = 0
    sys.val = 0
    sys.seenReset = true
  sys.val == m.val

proc genCounterCmd(r: var Rng, m: CounterModel): CounterCmd =
  ## Precondition-style: only generate `dec` when the model says it's valid.
  if m.val > 0 and r.genBool(): ccDec
  else: r.genElements([ccInc, ccReset])

# replayCmds: the primitive the shrinker builds on.
check("replayCmds: agreeing sequence replays true",
  replayCmds(@[ccInc, ccInc, ccReset], newCounterModel, newCounterSys,
    runCounter))
check("replayCmds: diverging sequence replays false",
  not replayCmds(@[ccReset, ccDec], newCounterModel, newCounterSys,
    runCounter))
check("replayCmds: empty sequence replays true",
  replayCmds(newSeq[CounterCmd](), newCounterModel, newCounterSys,
    runCounter))

# shrinkCmdSeq: a padded failing sequence shrinks to the minimal one.
let padded = @[ccInc, ccInc, ccReset, ccInc, ccInc, ccDec]
check("shrinkCmdSeq: padded sequence shrinks to [reset, dec]",
  shrinkCmdSeq(padded, newCounterModel, newCounterSys, runCounter) ==
    @[ccReset, ccDec])

# shrinkCmdSeq honors per-command shrinkers: int "add" commands where the
# system adds one extra on odd inputs; 7 must shrink to the minimal odd 1.
proc newIntAcc(): int = 0
proc runOdd(sys: var int, m: var int, c: int): bool =
  m += c
  if c mod 2 == 1: sys += c + 1
  else: sys += c
  sys == m
proc genIntCmd(r: var Rng, m: int): int = r.genInt(1, 20)
check("shrinkCmdSeq: command payloads shrink via shrinkCmd",
  shrinkCmdSeq(@[7], newIntAcc, newIntAcc, runOdd, shrinkInt) == @[1])

# runCommands end-to-end: the buggy counter is caught, with the replay seed
# and the minimal command sequence in the report.
proc counterRun(seed: uint64) =
  var r = initRng(seed)
  discard runCommands("buggy-counter", r, 200, 8, genCounterCmd,
    newCounterModel, newCounterSys, runCounter)

let outS1 = captureOutput(counterRun(42))
let outS2 = captureOutput(counterRun(42))
check("runCommands: catches the reset/dec bug",
  "FAIL [buggy-counter]" in outS1)
check("runCommands: failure output carries the replay seed",
  "seed: 42" in outS1)
check("runCommands: failure output shows the minimal command sequence",
  "minimal commands: @[ccReset, ccDec]" in outS1)
check("runCommands: same seed replays byte-identical output",
  outS1 == outS2)

# A correct system passes.
var rGood = initRng(7)
check("runCommands: passes a correct system",
  runCommands("good-counter", rGood, 200, 8, genCounterCmd,
    newCounterModel, newCounterSys, runCounterFixed))

# regressions: a known-bad seed replays the failure before the sweep.
var rCmdReg = initRng(999)
check("runCommands: regression seed replays the failure",
  not runCommands("counter-regress", rCmdReg, 200, 8, genCounterCmd,
    newCounterModel, newCounterSys, runCounter,
    regressions = @[42'u64]))

# --- Targeted generation (issue #30) ---

# The score pushes x toward 0 (the shrink direction). The generator is the
# bias-free `below`, not `genInt`, so blind draws cannot lean on genInt's
# edge bias — this isolates the targeting mechanism in the comparison.
proc negScore(x: int): float = -x.float

proc doTargetRun(seed: uint64, useShrink: bool) =
  var r = initRng(seed)
  let sh: proc(x: int): seq[int] =
    if useShrink: shrinkInt else: nil
  discard forAll("target-demo", r, 200,
    proc(r: var Rng): int = r.below(100_000),
    proc(x: int): bool = true,
    sh, target = negScore)

proc targetRun(seed: uint64, useShrink: bool): string =
  captureOutput(doTargetRun(seed, useShrink))

proc bestScoreOf(captured: string): float =
  let tag = "best target score: "
  let i = captured.find(tag)
  doAssert i >= 0, "no best target score in output"
  parseFloat(captured[i + tag.len .. ^1].splitLines()[0])

let tOut1 = targetRun(424242, true)
let tOut2 = targetRun(424242, true)
check("targeting: same seed replays byte-identical output", tOut1 == tOut2)
check("targeting: ok line reports the best score",
  "best target score: " in tOut1)

# Efficiency claim, measured not asserted: with the same generator, budget,
# and seeds, targeting reaches a strictly higher best score than blind
# draws. Seeds recorded (2026-10-15): on every one of these the targeted
# run hill-climbs to exactly 0.0 while blind stops far short.
for tSeed in [1'u64, 42, 424242, 12345]:
  let tb = bestScoreOf(targetRun(tSeed, true))
  let bb = bestScoreOf(targetRun(tSeed, false))
  check("targeting beats blind on seed " & $tSeed, tb > bb)
check("targeting: reaches the exact optimum (0.0) on seed 424242",
  bestScoreOf(targetRun(424242, true)) == 0.0)

# Blind runs are unaffected: with target unset there is no score line and
# the ok line is exactly the old format (no extra RNG draws on that path).
proc doBlindRun() =
  var rBlind = initRng(424242)
  discard forAll("target-demo", rBlind, 200,
    proc(r: var Rng): int = r.below(100_000),
    proc(x: int): bool = true,
    shrinkInt)
let blindOut = captureOutput(doBlindRun())
check("target unset: no score line, old ok-line format",
  "best target score" notin blindOut and
  "ok [target-demo]: 200 cases" in blindOut)

# NaN scores never become the best: no crash, no score line.
proc doNanRun() =
  var rNan = initRng(424242)
  discard forAll("target-nan", rNan, 50,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(x: int): bool = true,
    shrinkInt, target = proc(x: int): float = NaN)
let nanOut = captureOutput(doNanRun())
check("targeting: NaN scores are ignored, no crash",
  "best target score" notin nanOut and "ok [target-nan]: 50 cases" in nanOut)

# --- Float specials (issue #33) ---

# A property that fails only on NaN is found with allowNaN=true.
# Recorded seeds (2026-10-15); P(missing NaN) per seed is (15/16)^200.
proc doNanHunt(seed: uint64) =
  var r = initRng(seed)
  discard forAll("nan-hunt", r, 200,
    proc(r: var Rng): float = r.genFloat(0.0, 100.0, allowNaN = true),
    proc(x: float): bool = x == x,
    shrinkFloat)
proc nanHuntOut(seed: uint64): string = captureOutput(doNanHunt(seed))

for nSeed in [1'u64, 42, 424242]:
  let nOut = nanHuntOut(nSeed)
  check("float specials: NaN-only failure found on seed " & $nSeed,
    "FAIL [nan-hunt]" in nOut and "minimal input: nan" in nOut)
check("float specials: same seed replays byte-identical output",
  nanHuntOut(424242) == nanHuntOut(424242))

# Defaults never produce NaN/Inf and stay in range; -0.0 and subnormals do
# appear (fixed seed 7: measured 83 -0.0s and 163 subnormals in 5000 draws).
var rDef = initRng(7)
var defNan, defInf, defNegZero, defSub = 0
var defInRange = true
for _ in 0 ..< 2000:
  let x = rDef.genFloat(-10.0, 10.0)
  if x != x: inc defNan
  elif x == Inf or x == -Inf: inc defInf
  elif x == 0.0 and 1.0 / x == -Inf: inc defNegZero
  elif x != 0.0 and abs(x) < 1e-300: inc defSub
  if x < -10.0 or x >= 10.0: defInRange = false
check("float specials: defaults never produce NaN/Inf",
  defNan == 0 and defInf == 0)
check("float specials: defaults stay in [lo, hi)", defInRange)
check("float specials: defaults produce -0.0 and subnormals",
  defNegZero > 0 and defSub > 0)

# Opt-in produces the specials (fixed seed 7).
var rOpt = initRng(7)
var optNan, optInf = 0
for _ in 0 ..< 2000:
  let x = rOpt.genFloat(-10.0, 10.0, allowNaN = true, allowInf = true)
  if x != x: inc optNan
  elif x == Inf or x == -Inf: inc optInf
check("float specials: opt-in produces NaN and ±Inf",
  optNan > 0 and optInf > 0)

if failures > 0:
  echo failures, " self-test(s) failed"
  quit(1)
echo "all falsify self-tests pass"
