-- symcount returns the number of symbols in a regular expression.

import VerifiedFilter.Regex.Regex

namespace VerifiedFilter.Regex.Regex

@[reducible, simp]
def symcount (r: Regex σ): Nat :=
  match r with
  | emptyset => 0 | emptystr => 0 | symbol _ => 1 | star r1 => symcount r1
  | or r1 r2 => symcount r1 + symcount r2 | concat r1 r2 => symcount r1 + symcount r2
  | interleave r1 r2 => symcount r1 + symcount r2
  | and r1 r2 => symcount r1 + symcount r2 | compliment r1 => symcount r1
  | xor r1 r2 => symcount r1 + symcount r2

#guard symcount (or (symbol 'a') (star (symbol 'b'))) = 2
