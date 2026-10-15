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

if failures > 0:
  echo failures, " self-test(s) failed"
  quit(1)
echo "all falsify self-tests pass"
