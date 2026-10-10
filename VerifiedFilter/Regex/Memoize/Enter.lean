-- We define MemTable.enter memoizes the enter function.
-- We also prove soundness of this function using the State monad.

import VerifiedFilter.Std.Memoize.Memoize

import VerifiedFilter.Regex.Katydid
import VerifiedFilter.Regex.Regex

namespace VerifiedFilter.Regex.Regex.Memoize

abbrev enterParam (σ: Type) := Regex σ
abbrev enterMemTable (σ: Type) [DecidableEq σ] [Hashable σ] := MemTable enter (α := enterParam σ)
abbrev enterResult (r: Regex σ) := Preds σ |r|

def MemTable.enter [DecidableEq σ] [Hashable σ] [Monad m] [monadState: MonadState (enterMemTable σ) m]
  (param: Regex σ): m { res // res = enter param } :=
  MemTable.call Regex.enter param

private theorem MemTable.enter_is_correct [DecidableEq σ] [Hashable σ] (param: enterParam σ) (table: (enterMemTable σ)):
  Regex.enter param = (StateM.run (s := table) (MemTable.enter param)).1 := by
  generalize (StateM.run (MemTable.enter param) table) = x
  obtain ⟨⟨res, hres⟩, table'⟩ := x
  simp only
  rw [hres]

instance [DecidableEq σ] [Hashable σ] [Monad m] [MonadState (enterMemTable σ) m]:
  Memoize (α := enterParam σ) (β := enterResult) enter m where
  call param := MemTable.enter param

abbrev MemoizedEnter (σ: Type) [DecidableEq σ] [Hashable σ] := Memoize (@enter σ) (StateM (enterMemTable σ))

private theorem Memoize.StateM.enter_is_correct
  [DecidableEq σ] [Hashable σ] [mementer: MemoizedEnter σ]
  (param: enterParam σ) (table: enterMemTable σ):
  enter param = (mementer.call param table).1 := by
  generalize (mementer.call param table) = x
  obtain ⟨⟨res, hres⟩, table'⟩ := x
  simp only
  rw [hres]
