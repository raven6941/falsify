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


type
  Rng* = object
    s: uint64

proc initRng*(seed: uint64): Rng =
  ## Seed the generator. Seed 0 maps to a fixed nonzero default.
  var s = seed
  if s == 0: s = 0x9E3779B97F4A7C15'u64
  Rng(s: s)

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
  doAssert lo <= hi, "genInt: lo > hi"
  lo + r.below(hi - lo + 1)

proc genFloat*(r: var Rng, lo, hi: float): float =
  ## Float in [lo, hi).
  doAssert lo <= hi, "genFloat: lo > hi"
  lo + (hi - lo) * (r.next().float / high(uint64).float)

proc genChar*(r: var Rng): char =
  ## Printable ASCII char.
  chr(r.genInt(32, 126))

proc genString*(r: var Rng, maxLen: int): string =
  ## String of printable ASCII, length in [0, maxLen].
  let n = r.below(maxLen + 1)
  result = newString(n)
  for i in 0 ..< n:
    result[i] = r.genChar()

proc genSeq*[T](r: var Rng, maxLen: int, gen: proc(r: var Rng): T): seq[T] =
  ## Seq of length in [0, maxLen], elements from `gen`.
  let n = r.below(maxLen + 1)
  result = newSeq[T](n)
  for i in 0 ..< n:
    result[i] = gen(r)

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

proc forAll*[T](name: string, r: var Rng, n: int,
                gen: proc(r: var Rng): T,
                prop: proc(x: T): bool,
                shrink: proc(x: T): seq[T] = nil): bool =
  ## Run `prop` on `n` generated inputs. On the first failure, shrink
  ## (if a shrinker is given) and print the seed + minimal case, then
  ## return false. Returns true iff all cases pass.
  ##
  ## A custom shrinker has type `proc(x: T): seq[T]` returning candidates
  ## ordered most-aggressive first; see `shrinkInt` for the pattern.
  ## For seqs, `shrinkSeq[T]` needs an element shrinker:
  ##   `proc(s: seq[int]): seq[seq[int]] = s.shrinkSeq(shrinkInt)`.
  result = true
  for i in 0 ..< n:
    let x = gen(r)
    var failed = false
    try:
      failed = not prop(x)
    except CatchableError as e:
      echo "FAIL [", name, "]: exception on input: ", e.msg
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
            if cf:
              minimal = c
              cands = shrink(minimal)
              progressed = true
              break
          if not progressed: break
      echo "FAIL [", name, "]: case ", i, ", minimal input: ", $minimal
      return false
  echo "ok [", name, "]: ", n, " cases"
