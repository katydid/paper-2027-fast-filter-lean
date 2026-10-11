-- IfExpr represents a nested if expression where each symbol represents a condition and each leaf represents the a combination of booleans.
-- The booleans represent wheher a predicate matched or did not match a symbol on the path to the leaf.
-- This way all possible boolean Vectors are precomputed and heap allocations are avoided outside of the memoized IfExpr.enter.
-- Unfortunately this results in a exponential blowup in memory usage.
-- We provide examples: `example of an IfExpr for two symbols` and `example of evaluating an IfExpr for two symbols`.
-- We prove that evaluating the IfExpr is the same as mapping the predicate over the vector in theorem eval_is_map: (IfExpr.mk xs).eval Φ = Vector.map Φ xs

import VerifiedFilter.Std.Vector

namespace VerifiedFilter.Regex

inductive IfExpr (σ: Type) (β: Type) (l: Nat) where
  | res (evals: Vector β l): IfExpr σ β l
  | expr (s: σ) (thn: IfExpr σ β l) (els: IfExpr σ β l)
  deriving Repr, DecidableEq

end Regex

namespace Regex.IfExpr

def cast (x: IfExpr σ β l) (h: l = k): IfExpr σ β k := by
  cases h
  exact x

def eval (Φ: σ → Bool): IfExpr σ β l → Vector β l
  | res evals => evals
  | expr s thn els => if Φ s then thn.eval Φ else els.eval Φ

def mkAcc (xs: Vector σ k) (f: σ → Bool → β) (acc: Vector β l): IfExpr σ β (l + k) :=
  match k with
  | 0 =>
    IfExpr.res (Vector.cast (by omega) acc)
  | k + 1 =>
    let xs': Vector σ k := Vector.cast (by omega) xs.tail
    let pos: Vector β (l + 1) := (Vector.push acc (f xs.head true))
    let neg: Vector β (l + 1) := (Vector.push acc (f xs.head false))
    let posexpr: IfExpr σ β ((l + 1) + k) := IfExpr.mkAcc xs' f pos
    let negexpr: IfExpr σ β ((l + 1) + k) := IfExpr.mkAcc xs' f neg
    IfExpr.expr (Vector.head xs)
      (IfExpr.cast posexpr (by omega))
      (IfExpr.cast negexpr (by omega))

def mk (xs: Vector σ n) (f: σ → Bool → β): IfExpr σ β n :=
  IfExpr.cast (IfExpr.mkAcc xs f #v[]) (by omega)

-- example of an IfExpr for two symbols:
#guard IfExpr.mk #v['a','b'] (fun _ b => b)
  = IfExpr.expr 'a'
      (IfExpr.expr 'b'
        (IfExpr.res  #v[true, true])
        (IfExpr.res  #v[true, false]))
      (IfExpr.expr
        'b'
        (IfExpr.res  #v[false, true])
        (IfExpr.res  #v[false, false]))

-- example of evaluating an IfExpr for two symbols:
#guard (IfExpr.mk #v['a','b'] (fun _ b => b)).eval (· == 'a')
  = #v[true, false]

theorem lift_cast_eval (x: IfExpr σ β k) (h: k = l):
  (x.cast h).eval Φ = Vector.cast h (x.eval Φ) := by
    subst h
    rfl

theorem Vector.tail_cons (x: α) (xs: List α) (hxs : (Array.mk (x :: xs)).size = n + 1):
  (Vector.mk { toList := x :: xs } hxs).tail = Vector.mk { toList := xs } (by simp_all) := by
  have hlen : xs.length = n := by
    simp +arith only [List.size_toArray, List.length_cons] at hxs
    exact hxs
  apply Vector.eq
  simp +arith only [Nat.add_one_sub_one, Vector.tail_eq_cast_extract, Vector.extract_mk,
    List.extract_toArray, Vector.cast_mk, Vector.toList_mk]
  subst hlen
  exact List.take_length

theorem mkAcc_eval_cons_list (xs: Vector σ k) (b: β) (acc: Vector β l):
  ((IfExpr.mkAcc xs f (Vector.cons b acc)).eval Φ).toList =
    b :: ((IfExpr.mkAcc xs f acc).eval Φ).toList := by
  induction k generalizing l with
  | zero => simp only [IfExpr.mkAcc, IfExpr.eval, Vector.cast_toList, Vector.toList_cons]
  | succ k ih =>
      obtain ⟨⟨xs⟩, hxs⟩ := xs
      cases xs with
      | nil => contradiction
      | cons x xs =>
          let xs' : Vector σ k :=
            Vector.cast (by rfl) ((Vector.mk { toList := x :: xs } hxs).tail)
          have hhead : (Vector.mk { toList := x :: xs } hxs).head = x := rfl
          have hpush : ∀ x, (Vector.cons b acc).push x = Vector.cons b (acc.push x) := by
            intro x
            exact Vector.cons_push (x := b) (xs := acc) (y := x)
          cases hx : Φ x with
          | true =>
              simp only [IfExpr.mkAcc, IfExpr.eval, hhead, hx, IfExpr.lift_cast_eval, hpush]
              exact ih (xs := xs') (acc := acc.push (f x true))
          | false =>
              simp only [IfExpr.mkAcc, IfExpr.eval, hhead, hx, IfExpr.lift_cast_eval, hpush]
              exact ih (xs := xs') (acc := acc.push (f x false))

theorem eval_is_map_list (xs: Vector σ n):
  ((IfExpr.mk xs f).eval Φ).toList = (Vector.map (fun x => f x (Φ x)) xs).toList := by
  simp only [Vector.toList_map]
  induction n with
  | zero =>
    obtain ⟨⟨xs⟩, hxs⟩ := xs
    cases xs with
    | nil =>
        simp only [Vector.toList_mk, List.map_nil, Vector.toList_eq_nil_iff]
    | cons x xs =>
        simp +arith only [List.size_toArray, List.length_cons] at hxs
  | succ n ih =>
    obtain ⟨⟨xs⟩, hxs⟩ := xs
    cases xs with
    | nil =>
      simp +arith only [List.size_toArray, List.length_nil] at hxs
    | cons x xs =>
      have ih := ih (Vector.mk (Array.mk xs) (by simp_all))
      simp only [Vector.toList_mk] at ih
      simp only [Vector.toList_mk, List.map_cons]
      rw [←ih]
      simp only [IfExpr.mk, IfExpr.mkAcc]
      have hhead : (Vector.mk { toList := x :: xs } hxs).head = x := rfl
      rw [hhead]
      simp only [Vector.tail_cons, Vector.push, Array.push, List.concat]
      cases hx : Φ x with
      | true =>
          have htrue :
              (Vector.mk { toList := [f x true] } (by rfl)) =
                Vector.cons (f x true) #v[] := by
            apply Vector.eq
            simp only [Vector.toList_cons, Vector.toList_mk]
          simp only [hx, IfExpr.eval, IfExpr.lift_cast_eval, Vector.cast_toList]
          rw [htrue]
          apply IfExpr.mkAcc_eval_cons_list
      | false =>
          have hfalse :
              (Vector.mk { toList := [f x false] } (by rfl)) =
                Vector.cons (f x false) #v[] := by
            apply Vector.eq
            simp only [Vector.toList_cons, Vector.toList_mk]
          simp only [hx, IfExpr.eval, IfExpr.lift_cast_eval, Vector.cast_toList]
          rw [hfalse]
          apply IfExpr.mkAcc_eval_cons_list

theorem eval_is_map (xs: Vector σ l): (IfExpr.mk xs f).eval Φ = Vector.map (fun x => f x (Φ x)) xs := by
  apply Vector.eq
  rw [IfExpr.eval_is_map_list]
