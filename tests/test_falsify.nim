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

if failures > 0:
  echo failures, " self-test(s) failed"
  quit(1)
echo "all falsify self-tests pass"
