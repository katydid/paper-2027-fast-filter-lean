-- Memoizes.lean is a version of Memoize.lean that handles Vectors of Regexes instead of a single Regex.
-- This is used by Fused.

import VerifiedFilter.Std.Vector
import VerifiedFilter.Std.Memoize.Memoize

import VerifiedFilter.Regex.SymCount
import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Katydid

import VerifiedFilter.Regex.Memoize.Enters
import VerifiedFilter.Regex.Memoize.Nulls
import VerifiedFilter.Regex.Memoize.Leaves

namespace VerifiedFilter.Regex.Regex.Memoize

class MemoizeKatydids (m: Type → Type u) σ [DecidableEq σ] [Hashable σ] (Γ: σ → Bool → β) (ν: β -> Bool) where
  entersM : (rs: Σ (l: Nat), Vector (Regex σ) l) → m { res: Preds σ β |rs.2| // res = Regex.enters Γ rs.2 }
  nullsM  : (rs: Σ (l: Nat), Vector β l) → m { res: Vector Bool rs.1 // res = Vector.map ν rs.2 }
  leavesM : (param: Σ (l: Nat), Σ (rs: Vector (Regex σ) l), (Vector Bool |rs|))
             → m { res: Vector (Regex σ) param.1 // res = Regex.leaves param.2.1 param.2.2 }

instance (m: Type → Type u) (σ: Type) [DecidableEq σ] [Hashable σ] [DecidableEq β] [Hashable β] [Monad m]
  (Γ: σ → Bool → β) (ν: β -> Bool)
  [Memoize (α := entersParam σ) (β := entersResult Γ) (enters Γ) m]
  [entersState: MonadState (entersMemTable σ Γ) m]
  [Memoize (α := nullsParam β) (β := nullsResult) (nulls ν) m]
  [nullsState: MonadState (nullsMemTable β ν) m]
  [Memoize (α := leavesParam σ) (β := leavesResult) leaves m]
  [leavesState: MonadState (leavesMemTable σ) m]
  : MemoizeKatydids m σ Γ ν where
  entersM param := MemTable.enters (monadState := entersState) Γ param
  nullsM  param := MemTable.nulls  (monadState := nullsState)  ν param
  leavesM param := MemTable.leaves (monadState := leavesState)   param

def derives [Monad m] [DecidableEq σ] [Hashable σ]
  (Γ: σ → Bool → β) (ν: β -> Bool) [mem: MemoizeKatydids m σ Γ ν]
  (Φ: σ → Bool) (rs: Vector (Regex σ) l): m {drs: Vector (Regex σ) l // drs = Regex.Katydid.derives Γ ν Φ rs } := do
  let ⟨preds, hpreds⟩ ← mem.entersM ⟨l, rs⟩
  let evals := preds.eval Φ
  let ⟨nulls, hnulls⟩ ← mem.nullsM ⟨|rs|, evals⟩
  let ⟨res, hres⟩ ← mem.leavesM ⟨l, rs, nulls⟩
  let h: res = Regex.Katydid.derives Γ ν Φ rs := by
    simp only at hres
    rw [hnulls] at hres
    simp only at hres
    subst evals
    rw [hpreds] at hres
    assumption
  pure (Subtype.mk res h)

def validates [Monad m] [DecidableEq σ] [Hashable σ] (Γ: σ → Bool → β) (ν: β -> Bool) [MemoizeKatydids m σ Γ ν]
  (Φ: σ → α → Bool) (r: Regex σ) (xs: List α): m Bool := do
  let dr ← (List.foldlMemoize (fun dr x => Regex.Katydid.derives Γ ν (flip Φ x) dr) (fun dr x => Regex.Memoize.derives Γ ν (flip Φ x) dr) #v[r] xs)
  return Regex.null dr.val.head

def filters  [Monad m] [DecidableEq σ] [Hashable σ] (Γ: σ → Bool → β) (ν: β -> Bool) [MemoizeKatydids m σ Γ ν]
  (Φ: σ → α → Bool) (r: Regex σ) (xss: List (List α)): m (List (List α)) :=
  List.filterM (Regex.Memoize.validates Γ ν Φ r) xss
