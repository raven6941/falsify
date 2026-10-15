## Self-tests for falsify: the harness must catch known-broken properties,
## shrink to minimal counterexamples, and stay deterministic per seed.

import falsify

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

if failures > 0:
  echo failures, " self-test(s) failed"
  quit(1)
echo "all falsify self-tests pass"
