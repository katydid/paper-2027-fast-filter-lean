import VerifiedFilter.Regex.IfExpr

import VerifiedFilter.Std.Memoize

namespace VerifiedFilter.Regex

structure PredsId σ β l where
  xs: Vector (σ × β × β) l
  deriving Repr, DecidableEq

inductive Preds σ β l where
  | Id (xs: PredsId σ β l)
  | IfExpr (i: IfExpr σ β l)
  deriving Repr, DecidableEq

def PredsId.mk' (xs: Vector σ l) (Γ: σ → Bool → β): PredsId σ β l :=
  PredsId.mk <| xs.map (fun x => (x, Γ x true, Γ x false))

def Preds.mk' (xs: Vector σ l) (Γ: σ → Bool → β): Preds σ β l :=
  -- An exponential blow up can occur when creating an IfExpr, so we limit the size of the resulting vector.
  -- We fallback to a simple Vector in cases where the exponential blow up of IfExpr would be too large.
  -- In general we prefer IfExpr, since it preallocates the resulting boolean Vectors, which avoids heap allocations.
  if l < 20
  then Preds.IfExpr <| IfExpr.mk xs Γ
  else Preds.Id <| PredsId.mk' xs Γ

def Preds.mk (xs: Vector σ l): Preds σ Bool l :=
  Preds.mk' xs (fun _ c => c)

theorem Preds_is_IfExpr (h: Preds.mk' xs f = Preds.IfExpr i):
  Preds.mk' xs f = Preds.IfExpr (IfExpr.mk xs f) := by
  simp_all [Preds.mk']
  grind

theorem Preds_is_Id (h: Preds.mk' xs f = Preds.Id xs'):
  Preds.mk' xs f = Preds.Id (PredsId.mk' xs f) := by
  simp_all [Preds.mk']
  grind

def PredsId.eval (Φ: σ -> Bool) (p: PredsId σ β l): Vector β l :=
  p.xs.map (fun ⟨φ, thn, els⟩ => if Φ φ then thn else els)

def PredsId.evalM [Monad m] (Φ: σ -> m Bool) (p: PredsId σ β l): m (Vector β l) :=
  p.xs.mapM (fun ⟨φ, thn, els⟩ => do if ← Φ φ then return thn else return els)

def PredsId.evalMemoize [Monad m]
  (puref: α → Bool) (memf: (a: α) → m {res // res = puref a}) (p : PredsId α β n)
  : m {ys: (Vector β n) // ys = PredsId.eval puref p } := do
  Vector.mapMemoize
    (fun ⟨φ, thn, els⟩ => if puref φ then thn else els)
    (fun ⟨φ, thn, els⟩ => do
      let c ← memf φ
      if h: c
      then return ⟨thn, by
        simp only
        obtain ⟨c, hc⟩ := c
        simp only at h
        subst_vars
        rw [h]
        simp
      ⟩
      else return ⟨els, by
        simp only
        obtain ⟨c, hc⟩ := c
        simp only at h
        simp at h
        subst_vars
        rw [h]
        simp
      ⟩
    )
    p.xs

theorem PredsId.eval_is_map (xs: Vector σ l): (PredsId.mk' xs Γ).eval Φ = Vector.map (fun x => Γ x (Φ x)) xs := by
  simp [PredsId.eval]
  simp [PredsId.mk']
  intro φ
  intro hxs
  cases (Φ φ) with
  | true =>
    simp
  | false =>
    simp

def Preds.eval (Φ: σ -> Bool) (ps: Preds σ β l): Vector β l :=
  match ps with
  | Id xs => xs.eval Φ
  | IfExpr i => i.eval Φ

theorem preds_eval_is_map' (Φ: σ -> Bool) (xs: Vector σ l):
  Preds.eval Φ (Preds.mk' xs Γ) = Vector.map (fun x => Γ x (Φ x)) xs := by
  cases h: (Preds.mk' xs Γ) with
  | Id xs' =>
    simp [Preds.eval]
    rw [Preds_is_Id h] at h
    simp at h
    rw [<- h]
    rw [PredsId.eval_is_map]
  | IfExpr i =>
    simp [Preds.eval]
    rw [Preds_is_IfExpr h] at h
    simp at h
    rw [<- h]
    rw [IfExpr.eval_is_map]

theorem preds_eval_is_map: Preds.eval Φ (Preds.mk xs) = Vector.map Φ xs := by
  simp only [Preds.mk]
  apply preds_eval_is_map'

def IfExpr.evalMemoize [Monad m]
  (puref: α → Bool) (memf: (a: α) → m {res // res = puref a}) (ifexpr : IfExpr α β n)
  : m {ys: (Vector β n) // ys = IfExpr.eval puref ifexpr } := do
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

def IfExpr.evalM [Monad m] (f: σ → m Bool) (ifexpr : IfExpr σ β n): m (Vector β n) := do
  match ifexpr with
  | res bools => return bools
  | expr cond thn els =>
    if ← f cond
    then IfExpr.evalM f thn
    else IfExpr.evalM f els

def Preds.evalM [Monad m]
  (f: σ → m Bool) (preds : Preds σ β n): m (Vector β n) :=
  match preds with
  | Preds.Id xs => PredsId.evalM f xs
  | Preds.IfExpr i => IfExpr.evalM f i

def Preds.evalMemoize [Monad m]
  (puref: σ → Bool) (memf: (a: σ) → m {res // res = puref a}) (preds : Preds σ β n)
  : m {ys: (Vector β n) // ys = Preds.eval puref preds } :=
  match preds with
  | Preds.Id xs => PredsId.evalMemoize puref memf xs
  | Preds.IfExpr i => IfExpr.evalMemoize puref memf i
