-- Enters.lean is a version of Enter.lean that handles a Vector a Regexs instead of a single Regex.
-- This is used by Fused.

import VerifiedFilter.Std.Memoize.Memoize

import VerifiedFilter.Std.Hashable
import VerifiedFilter.Std.Decidable
import VerifiedFilter.Regex.Katydids
import VerifiedFilter.Regex.Katydid
import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Preds
import VerifiedFilter.Regex.Extracts

namespace VerifiedFilter.Regex.Regex.Memoize

abbrev entersParam (σ: Type) := Σ (l: Nat), Vector (Regex σ) l
abbrev entersResult (_Γ: σ → Bool → β) (rs: entersParam σ) := Preds σ β |rs.2|

abbrev enters {σ: Type} (Γ: σ → Bool → β): (a: entersParam σ) → entersResult Γ a
  | rs => Regex.enters Γ rs.2

abbrev entersMemTable (σ: Type) [DecidableEq σ] [Hashable σ] (Γ: σ → Bool → β) :=
  MemTable (enters Γ) (α := entersParam σ)

def MemTable.enters [DecidableEq σ] [Hashable σ] [Monad m]
  (Γ: σ → Bool → β) [monadState: MonadState (entersMemTable σ Γ) m]
  (param: entersParam σ): m { res // res = Regex.Memoize.enters Γ param } :=
  MemTable.call (Regex.Memoize.enters Γ) param

private theorem MemTable.enter_is_correct [DecidableEq σ] [Hashable σ]
  (Γ: σ → Bool → β) (param: entersParam σ) (table: (entersMemTable σ Γ)):
  Regex.Memoize.enters Γ param = (StateM.run (s := table) (MemTable.enters Γ param)).1 := by
  generalize (StateM.run (MemTable.enters Γ param) table) = x
  obtain ⟨⟨res, hres⟩, table'⟩ := x
  simp only
  rw [hres]

instance [DecidableEq σ] [Hashable σ] [Monad m]
  (Γ: σ → Bool → β) [MonadState (entersMemTable σ Γ) m]:
  Memoize (α := entersParam σ) (β := entersResult Γ) (Regex.Memoize.enters Γ) m where
  call param := MemTable.enters Γ param

abbrev MemoizedEnters (σ: Type) [DecidableEq σ] [Hashable σ] (Γ: σ → Bool → β) :=
  Memoize (@enter σ) (StateM (entersMemTable σ Γ))
