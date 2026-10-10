-- nsym returns the number of symbols in a regular expression.

import VerifiedFilter.Regex.Regex

namespace VerifiedFilter.Regex.Regex

@[reducible, simp]
def nsym (r: Regex σ): Nat :=
  match r with
  | emptyset => 0 | emptystr => 0 | symbol _ => 1 | star r1 => nsym r1
  | or r1 r2 => nsym r1 + nsym r2 | concat r1 r2 => nsym r1 + nsym r2
  | interleave r1 r2 => nsym r1 + nsym r2
  | and r1 r2 => nsym r1 + nsym r2 | compliment r1 => nsym r1
  | xor r1 r2 => nsym r1 + nsym r2

#guard nsym (or (symbol 'a') (star (symbol 'b'))) = 2

class NumberOfSymbols (α: Type) where
  numberOfSymbols: α -> Nat

macro:max atomic("|" noWs) r:term noWs "|" : term => `(NumberOfSymbols.numberOfSymbols $r)

instance: NumberOfSymbols (Regex σ) where
  numberOfSymbols := nsym

#guard |or (symbol 'a') (star (symbol 'b'))| = 2
