import VerifiedFilter.Regex.IfExpr

import VerifiedFilter.Std.Memoize

namespace VerifiedFilter.Regex

inductive Preds σ l where
  | Id (xs: Vector σ l)
  | IfExpr (i: IfExpr σ l)
  deriving Repr, DecidableEq

def Preds.mk (xs: Vector σ l): Preds σ l :=
  -- An exponential blow up can occur when creating an IfExpr, so we limit the size of the resulting vector.
  -- We fallback to a simple Vector in cases where the exponential blow up of IfExpr would be too large.
  -- In general we prefer IfExpr, since it preallocates the resulting boolean Vectors, which avoids heap allocations.
  if l < 20
  then Preds.IfExpr <| IfExpr.mk xs
  else Preds.Id xs

theorem Preds_is_IfExpr (h: Preds.mk xs = Preds.IfExpr i):
  Preds.mk xs = Preds.IfExpr (IfExpr.mk xs) := by
  simp_all [Preds.mk]
  grind

theorem Preds_is_Id (h: Preds.mk xs = Preds.Id xs'):
  Preds.mk xs = Preds.Id xs := by
  simp_all [Preds.mk]
  grind

def Preds.eval (Φ: σ -> Bool) (ps: Preds σ l): Vector Bool l :=
  match ps with
  | Id xs => Vector.map Φ xs
  | IfExpr i => i.eval Φ

theorem preds_eval_is_map:
  (Preds.mk xs).eval Φ = xs.map Φ := by
  cases h: (Preds.mk xs) with
  | Id xs' =>
    simp [Preds.eval]
    rw [Preds_is_Id h] at h
    simp at h
    rw [<- h]
  | IfExpr i =>
    simp [Preds.eval]
    rw [Preds_is_IfExpr h] at h
    simp at h
    rw [<- h]
    rw [IfExpr.eval_is_map]

def IfExpr.evalMemoize [Monad m]
  (puref: α → Bool) (memf: (a: α) → m {res // res = puref a}) (ifexpr : IfExpr α n)
  : m {ys: (Vector Bool n) // ys = IfExpr.eval puref ifexpr } := do
  match ifexpr with
  | res bools => return ⟨bools, by
      simp [eval]
    ⟩
  | expr s thn els =>
    let ⟨cond, hcond⟩ <- memf s
    if hcond': cond
    then
      let ⟨ys, hys⟩ <- evalMemoize puref memf thn
      return ⟨ys, by
        rw [hys]
        simp only [eval]
        rw [<- hcond]
        rw [hcond']
        simp only
        simp only [↓reduceIte]
      ⟩
    else
      let ⟨ys, hys⟩ <- evalMemoize puref memf els
      return ⟨ys, by
        rw [hys]
        simp only [eval]
        rw [<- hcond]
        cases cond
        · simp
        · contradiction
      ⟩

def Preds.evalMemoize [Monad m]
  (puref: α → Bool) (memf: (a: α) → m {res // res = puref a}) (preds : Preds α n)
  : m {ys: (Vector Bool n) // ys = Preds.eval puref preds } :=
  match preds with
  | Preds.Id xs => Vector.mapMemoize puref memf xs
  | Preds.IfExpr i => IfExpr.evalMemoize puref memf i
