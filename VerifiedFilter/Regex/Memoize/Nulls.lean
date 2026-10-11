-- Nulls.lean memoizes the nullability of a Vector of regexes.
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

abbrev nullsParam (β: Type) := Σ (l: Nat), Vector β l
abbrev nullsResult (rs: nullsParam β) := Vector Bool rs.1

abbrev nulls {β: Type} (ν: β → Bool): (a: nullsParam β) → nullsResult a
  | rs => Vector.map ν rs.2

abbrev nullsMemTable (β: Type) [DecidableEq β] [Hashable β] (ν: β → Bool) :=
  MemTable (nulls ν) (α := nullsParam β)

def MemTable.nulls [DecidableEq β] [Hashable β] [Monad m]
  (ν: β → Bool) [monadState: MonadState (nullsMemTable β ν) m]
  (param: nullsParam β): m { res // res = Regex.Memoize.nulls ν param } :=
  MemTable.call (Regex.Memoize.nulls ν) param

private theorem MemTable.null_is_correct [DecidableEq β] [Hashable β]
  (ν: β → Bool) (param: nullsParam β) (table: (nullsMemTable β ν)):
  Regex.Memoize.nulls ν param = (StateM.run (s := table) (MemTable.nulls ν param)).1 := by
  generalize (StateM.run (MemTable.nulls ν param) table) = x
  obtain ⟨⟨res, hres⟩, table'⟩ := x
  simp only
  rw [hres]

instance [DecidableEq β] [Hashable β] [Monad m]
  (ν: β → Bool) [MonadState (nullsMemTable β ν) m]:
  Memoize (α := nullsParam β) (β := nullsResult) (Regex.Memoize.nulls ν) m where
  call param := MemTable.nulls ν param

abbrev MemoizedNulls (β: Type) [DecidableEq β] [Hashable β] (ν: β → Bool) :=
  Memoize (nulls ν) (StateM (nullsMemTable β ν))
