-- Memoize is a standard package for generic memoization.
import Std.Data.ExtDHashMap

import VerifiedFilter.Std.State
import VerifiedFilter.Std.Vector

-- MemTable is a hashtable containing function input parameter and result as the key and value respectively.
-- The value of the key-value pair also includes a proof that value was obtained by called the function f with the corresponding key.
abbrev MemTable {α: Type} {β: α → Type} [DecidableEq α] [Hashable α] (f: (a: α) → β a) :=
  Std.ExtDHashMap
    α
    (fun a =>
      { b: β a // b = f a }
    )

-- MemTable.init creates an empty MemTable.
def MemTable.init {α: Type} {β: α → Type} [DecidableEq α] [Hashable α]
  (f: (a: α) → β a): MemTable f := Std.ExtDHashMap.emptyWithCapacity

-- MemTable.modifyGet is an example of how to implement modifyGet for a State monad with MemTable as the state.
def MemTable.modifyGet
  {α: Type} [DecidableEq α] [Hashable α] {β: α → Type}
  (f: (a: α) → β a)
  (a: α): MemTable f → ({ b: β a // b = f a } × MemTable f) :=
  fun table =>
    match Std.ExtDHashMap.get? table a with
    | Option.none =>
      let b: { b: β a // b = f a } := Subtype.mk (f a) rfl
      (b, (Std.ExtDHashMap.insert table a b))
    | Option.some b =>
      (b, table)

-- MemTable.call calls the function f with MemTable as the state of the MonadState class.
-- This will first try to lookup if the MemTable already contains any results, so that we can avoid calling f.
-- If this fails, f will be called and the result will be stored in MemTable for next time.
def MemTable.call
  {α: Type} [DecidableEq α] [Hashable α] {β: α → Type}
  (f: (a: α) → β a)
  [Monad m] [MonadState (MemTable f) m]
  (a: α): m { b: β a // b = f a } := do
  let table ← MonadState.get
  match Std.ExtDHashMap.get? table a with
  | Option.none =>
    let b: { b: β a // b = f a } := Subtype.mk (f a) rfl
    MonadState.set (Std.ExtDHashMap.insert table a b)
    return b
  | Option.some b => return b

-- Memoize is a class that allows a function to be called inside a monad, but still produce the same result inside the monad.
-- A typical use case would be a state monad that memoizes the results of calling f for optimization purposes.
class Memoize [DecidableEq α] [Hashable α] {β: α → Type}
  (f: (a: α) → β a) (m: Type → Type u)
  where call: (a: α) → m { b: β a // b = f a }

-- Vector.mapMemoize is Vector.mapM, but also includes a subtype for memoization purposes.
-- The `memf` is the only function called and is a memoized version of `puref`.
-- Although a pure function `puref` is passed, it is never called in the implementation, only in the proofs for the subtype.
-- The proofs in the subtype, show that this `map` function is the same as calling `Vector.map`, except that results might be memoized for optimization purposes.
def Vector.mapMemoize [Monad m]
  (puref: α → β) (memf: (a: α) → m {res // res = puref a}) (xs : Vector α n)
  : m {ys: (Vector β n) // ys = Vector.map puref xs } := do
  go 0 (Nat.zero_le n) ⟨#v[], by simp⟩
where
  go (k : Nat) (h : k ≤ n) (acc : {ys: (Vector β k) // ys = Vector.cast (by omega) (Vector.map puref (Vector.take xs k)) })
    : m {ys: (Vector β n) // ys = Vector.map puref xs } := do
      if h' : k < n then
        memf xs[k] >>=
          fun xsk =>
            go (k+1) (by omega) (Subtype.mk (acc.val.push xsk) (by
              obtain ⟨acc, hacc⟩ := acc
              simp only
              rw [hacc]
              obtain ⟨xsk, hxsk⟩ := xsk
              simp only
              rw [hxsk]
              apply Vector.eq
              rw [Vector.cast_toList]
              rw [Vector.map_toList]
              rw [Vector.toList_take]
              rw [Vector.toList_push]
              rw [Vector.cast_toList]
              rw [Vector.map_toList]
              rw [Vector.toList_take]
              rw [← hxsk]
              cases n with
              | zero =>
                contradiction
              | succ n' =>
                rw [Vector.take_succ_toList (h := by omega)]
                rw [List.map_append]
                congr
            ))
      else
        return ⟨Vector.cast (by omega) acc.val, by
          obtain ⟨acc, hacc⟩ := acc
          simp only
          rw [hacc]
          -- aesop?
          subst hacc
          simp only [take_eq_extract, map_extract, cast_cast]
          have h'' : k = n := by
            omega
          subst h''
          simp_all only [extract_size, Nat.sub_zero, cast_cast, Vector.cast_rfl]
        ⟩

-- List.foldlMemoizeWithMembership is List.foldlM, but also includes a subtype for memoization purposes and also another subtype on the input parameter of `memf`.
-- The `memf` is the only function called and is a memoized version of `puref`.
-- The subtype on the input parameter of `memf` is their to show that the it will always receive a member of the input list, which is used for termination proof pursoses.
-- Although a pure function `puref` is passed, it is never called in the implementation, only in the proofs for the subtype.
-- The proofs in the subtype, show that this `foldl` function is the same as calling `List.foldl`, except that results might be memoized for optimization purposes.
def List.foldlMemoizeWithMembership [Monad m] (puref: β → α → β) (xs: List α)
  (memf: (acc: β) → (a: {a': α // a' ∈ xs}) → m {res: β // res = puref acc a } )
  (init: β)
  : m {res': β // res' = List.foldl puref init xs } :=
  match xs with
  | [] => pure ⟨init, rfl⟩
  | (x::xs') => do
    let fx ← memf init (Subtype.mk x (by simp))
    let fxs ← List.foldlMemoizeWithMembership puref xs' (fun acc a => do
      let ⟨b, hb⟩ := a
      let a'': { a' // a' ∈ x :: xs' } := Subtype.mk b (by
        -- aesop?
        simp_all only [mem_cons, or_true]
      )
      let f': { res // res = puref acc a''.val } ← memf acc a''
      let f'': { res // res = puref acc b } := by
        subst a''
        simp only at f'
        assumption
      pure f''
    ) fx.val
    pure (Subtype.mk fxs.val (by
      obtain ⟨fxs, hfxs⟩ := fxs
      simp only
      obtain ⟨fx, hfx⟩ := fx
      simp only at hfxs
      rw [hfxs]
      rw [hfx]
      simp only
      simp only [List.foldl]
    ))

-- List.foldlMemoize is List.foldlM, but also includes a subtype for memoization purposes.
-- The `memf` is the only function called and is a memoized version of `puref`.
-- Although a pure function `puref` is passed, it is never called in the implementation, only in the proofs for the subtype.
-- The proofs in the subtype, show that this `foldl` function is the same as calling `List.foldl`, except that results might be memoized for optimization purposes.
def List.foldlMemoize [Monad m] (puref: β → α → β)
  (memf: (acc: β) → (a: α) → m {res: β // res = puref acc a } ) (init: β) (xs: List α)
  : m {res': β // res' = List.foldl puref init xs } :=
  match xs with
  | [] => pure ⟨init, rfl⟩
  | (x::xs') => do
    let fx ← memf init x
    let fxs ← List.foldlMemoizeWithMembership puref xs' (fun acc a => do
      let ⟨b, hb⟩ := a
      let a'': { a' // a' ∈ x :: xs' } := Subtype.mk b (by
        -- aesop?
        simp_all only [mem_cons, or_true]
      )
      let f': { res // res = puref acc a''.val } ← memf acc a''
      let f'': { res // res = puref acc b } := by
        subst a''
        simp only at f'
        assumption
      pure f''
    ) fx.val
    pure (Subtype.mk fxs.val (by
      obtain ⟨fxs, hfxs⟩ := fxs
      simp only
      obtain ⟨fx, hfx⟩ := fx
      simp only at hfxs
      rw [hfxs]
      rw [hfx]
      simp only [List.foldl]
    ))

-- List.filterMemoize is List.filterM, but also includes a subtype for memoization purposes.
-- The `memf` is the only function called and is a memoized version of `puref`.
-- Although a pure function `puref` is passed, it is never called in the implementation, only in the proofs for the subtype.
-- The proofs in the subtype, show that this `filter` function is the same as calling `List.filter`, except that results might be memoized for optimization purposes.
def List.filterMemoize [Monad m] (puref: α → Bool)
  (memf: (a: α) → m {res: Bool // res = puref a } ) (xs: List α)
  : m {res': List α // res' = List.filter puref xs } :=
  match xs with
  | [] => pure ⟨[], rfl⟩
  | (x::xs) => do
    let fx ← memf x
    let fxs ← List.filterMemoize puref memf xs
    if hfx1: fx.1
    then pure (Subtype.mk (x :: fxs.val) (by
      obtain ⟨fxs, hfxs⟩ := fxs
      obtain ⟨fx, hfx⟩ := fx
      obtain ⟨fx1, hfx1⟩ := hfx1
      simp only
      simp only [List.filter]
      rw [← hfx]
      simp only
      rw [hfxs]
    ))
    else pure (Subtype.mk (fxs.val) (by
      obtain ⟨fxs, hfxs⟩ := fxs
      obtain ⟨fx, hfx⟩ := fx
      simp only at hfx1
      simp only [Bool.not_eq_true] at hfx1
      simp only
      simp only [List.filter]
      rw [← hfx]
      rw [hfx1]
      rw [← hfxs]
    ))
