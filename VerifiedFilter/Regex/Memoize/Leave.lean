-- We define MemTable.leave memoizes the uncurried leave function.
-- We also prove soundness of this function using the State monad.

import VerifiedFilter.Std.Hashable
import VerifiedFilter.Std.Decidable
import VerifiedFilter.Std.Memoize.Memoize

import VerifiedFilter.Regex.Katydid
import VerifiedFilter.Regex.Regex

namespace VerifiedFilter.Regex.Regex.Memoize

abbrev leaveParam (σ: Type) := Σ (r: Regex σ), (Vector Bool (symcount r))
abbrev leaveResult {σ: Type} (_: leaveParam σ) := Regex σ

abbrev leave {σ: Type}: (a: leaveParam σ) → leaveResult a
  | ⟨r, bools⟩ => Regex.leave r bools

abbrev leaveMemTable (σ: Type) [DecidableEq σ] [Hashable σ] := MemTable leave (α := leaveParam σ)

def MemTable.leave {σ: Type} [DecidableEq σ] [Hashable σ] [Monad m] [monadState: MonadState (leaveMemTable σ) m]
  (param: leaveParam σ): m { res // res = Regex.Memoize.leave param } :=
  MemTable.call Regex.Memoize.leave param

private theorem MemTable.leave_is_correct [DecidableEq σ] [Hashable σ] (param: leaveParam σ) (table: leaveMemTable σ):
  Regex.Memoize.leave param = (StateM.run (s := table) (MemTable.leave param)).1 := by
  generalize (StateM.run (leave param) table) = x
  obtain ⟨⟨res, hres⟩, table'⟩ := x
  simp only
  rw [hres]

instance {σ: Type} [DecidableEq σ] [Hashable σ] [Monad m] [MonadState (leaveMemTable σ) m]:
  Memoize (α := leaveParam σ) (β := leaveResult) Regex.Memoize.leave m where
  call param := MemTable.leave param

abbrev MemoizedLeave (σ: Type) [DecidableEq σ] [Hashable σ] := Memoize (@Regex.Memoize.leave σ) (StateM (leaveMemTable σ))

private theorem Memoize.StateM.leave_is_correct
  [DecidableEq σ] [Hashable σ] [memleave: MemoizedLeave σ]
  (param: leaveParam σ) (table: leaveMemTable σ):
  Regex.Memoize.leave param = (memleave.call param table).1 := by
  generalize (memleave.call param table) = x
  obtain ⟨⟨res, hres⟩, table'⟩ := x
  simp only
  rw [hres]
