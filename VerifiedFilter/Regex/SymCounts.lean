-- SymCounts.lean is a version of SymCount.lean that handles a Vector a Regexes instead of a single Regex.
-- This is used by Fused.

import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.SymCount

namespace VerifiedFilter.Regex.Regex

def nsyms (rs: Vector (Regex σ) l): Nat :=
  Vector.foldl (· + ·) 0 (Vector.map nsym rs)

instance: NumberOfSymbols (Vector (Regex σ) l) where
  numberOfSymbols := nsyms

#guard |#v[Regex.emptyset, Regex.symbol 1, Regex.or (Regex.symbol 1) (Regex.emptystr)]|
  = 2

theorem nsyms_add (rs: Vector (Regex σ) l) (r: Regex σ):
  |Vector.push rs r| = |r| + |rs| := by
  -- rw??
  simp only [|·|]
  rw [show
      nsyms (rs.push r) =
        Vector.foldl (fun x1 x2 => x1 + x2) 0 (Vector.map nsym (rs.push r))
      from rfl]
  -- rw??
  rw [Vector.foldl_map]
  -- rw??
  rw [Vector.foldl_push]
  -- rw??
  rw [Nat.add_comm r.nsym (nsyms rs)]
  -- rw??
  rw [Nat.add_left_inj]
  rw [← Vector.foldl_map]
  rw [← nsyms]

theorem nsyms_add1 (rs: Vector (Regex σ) (l + 1)):
  |rs| = |Vector.back rs| + |Vector.pop rs| := by
  rw [← nsyms_add]
  rw [Vector.push_pop_back]
  rfl
