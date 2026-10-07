-- Proofs of correctness for the optimized Katydid algorith with memoization via the state monad.
-- Here we prove derive_commutes, validate_commutes and the ultimate proof of the paper: memoize_mem_filter.

import VerifiedFilter.Std.Decidable
import VerifiedFilter.Std.Hedge
import VerifiedFilter.Std.Vector

import VerifiedFilter.Regex.Lang
import VerifiedFilter.Regex.Katydid
import VerifiedFilter.Regex.Memoize.Memoize
import VerifiedFilter.Regex.Memoize.StateMemoize
import VerifiedFilter.Regex.SymCount

import VerifiedFilter.Grammar.Denote
import VerifiedFilter.Grammar.Grammar
import VerifiedFilter.Grammar.Katydid
import VerifiedFilter.Grammar.Lang
import VerifiedFilter.Grammar.Denote

import VerifiedFilter.Grammar.Memoize.Memoize

open VerifiedFilter.Regex
open Regex.Memoize
open Hedge

def StateMemoize.Grammar.derive.run {φ: Type} [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Bool) (r: Regex (φ × Ref n)) (node: Node α): Regex (φ × Ref n) :=
  StateMemoize.run state (Grammar.Memoize.derive G Φ r node)

def StateMemoize.Grammar.validate.run [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Bool) (nodes: Hedge α): Bool :=
  StateMemoize.run state (Grammar.Memoize.validate G Φ nodes)

def StateMemoize.Grammar.filter.run [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Bool) (xss: List (Hedge α)): List (Hedge α) :=
  StateMemoize.run state (Grammar.Memoize.filter G Φ xss)

theorem StateMemoize.Grammar.derive.run_unfold {φ: Type} [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Bool) (r: Regex (φ × Ref n)) (node: Node α):
  (StateMemoize.Grammar.derive.run state G Φ r node) = StateMemoize.run state (Grammar.Memoize.derive G Φ r node) :=
  rfl

theorem StateMemoize.Grammar.derive.run_is_sound [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n))
  (Φ: φ → α → Bool) (G: Grammar n φ) (r: Regex (φ × Ref n)) (node: Node α):
  StateMemoize.Grammar.derive.run state G Φ r node = Grammar.Katydid.derive G Φ r node := by
  rw [StateMemoize.Grammar.derive.run_unfold]
  generalize StateMemoize.run state (Grammar.Memoize.derive G Φ r node) = x
  obtain ⟨dr, hdr⟩ := x
  simp only
  rw [hdr]

theorem StateMemoize.Grammar.derive_commutes [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n))
  (Φ: φ → α → Bool)
  (G: Grammar n φ) (r: Regex (φ × Ref n)) (node: Node α):
  Grammar.Rule.denote G Φ (StateMemoize.Grammar.derive.run state G Φ r node)
  = Lang.derive (Grammar.Rule.denote G Φ r) node := by
  rw [StateMemoize.Grammar.derive.run_is_sound]
  rw [← Grammar.Katydid.derive_commutes]

theorem StateMemoize.Grammar.validate.run_unfold [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Bool) (nodes: Hedge α):
  (StateMemoize.Grammar.validate.run state G Φ nodes) = StateMemoize.run state (Grammar.Memoize.validate G Φ nodes) :=
  rfl

theorem StateMemoize.validate.run_is_sound {φ: Type} {α: Type} [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Bool) (nodes: Hedge α):
  StateMemoize.Grammar.validate.run state G Φ nodes = Grammar.Katydid.validate G Φ nodes := by
  rw [StateMemoize.Grammar.validate.run_unfold]
  generalize StateMemoize.run state (Grammar.Memoize.validate G Φ nodes) = x
  obtain ⟨b, hd⟩ := x
  simp only
  assumption

theorem Regex.StateMemoize.validate_commutes {φ: Type} {α: Type} [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Bool) (nodes: Hedge α):
  StateMemoize.Grammar.validate.run state G Φ nodes = Grammar.denote G Φ nodes := by
  rw [StateMemoize.validate.run_is_sound]
  rw [← Grammar.Katydid.validate_commutes]

theorem StateMemoize.Grammar.filter.run_unfold {φ: Type} {α: Type} [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Bool) (xss: List (Hedge α)):
  (StateMemoize.Grammar.filter.run state G Φ xss) = StateMemoize.run state (Grammar.Memoize.filter G Φ xss) :=
  rfl

theorem Grammar.StateMemoize.mem_filter [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) Φ (xs: List (Hedge α)):
  ∀ x, (x ∈ StateMemoize.Grammar.filter.run state G Φ xs) ↔ (Lang.MemFilter (Grammar.denote G Φ) xs x) := by
  intro x
  rw [StateMemoize.Grammar.filter.run_unfold]
  generalize StateMemoize.run state (Grammar.Memoize.filter G Φ xs) = h
  obtain ⟨res, hres⟩ := h
  simp only
  rw [hres]
  unfold Katydid.filter
  rw [List.mem_filter]
  unfold Lang.MemFilter
  rw [Katydid.validate_commutes]

open Regex

abbrev leave (r: Regex σ) (param2: (Vector Bool (symcount r))) := Regex.leave r param2

theorem StateM.StateT.run11 :
  StateM.run' (StateT.run' f s1) s2 = (StateM.run (StateT.run f s1) s2).1.1 := by
  rfl

-- (enterState: Std.ExtDHashMap (Regex (φ × Ref n)) (fun r => {res: Vector (φ × Ref n) (symbols r) // res = enter r }))
-- (leaveState: Std.ExtDHashMap (Σ (r: Regex (φ × Ref n)), (Vector Bool (symbols r))) (fun param => {r: Regex (φ × Ref n) // r = leave param.1 param.2 }))

theorem memoize_mem_filter [DecidableEq φ] [Hashable φ] (state: memoizeState (φ × Ref n))
  (G: Grammar n φ) Φ (xs: List (Hedge α)):
  ∀ x, (x ∈ (flip StateM.run' state.leave (flip StateT.run' state.enter
       (Grammar.Memoize.filter G Φ xs))).val)
    ↔ (x ∈ xs ∧ Grammar.denote G Φ x) := by
  intro x
  simp only [flip]
  rw [StateM.StateT.run11]
  generalize (StateM.run (StateT.run (Grammar.Memoize.filter G Φ xs) state.enter) state.leave).1.1 = h
  obtain ⟨res, hres⟩ := h
  simp only
  rw [hres]
  unfold Grammar.Katydid.filter
  rw [List.mem_filter]
  rw [Grammar.Katydid.validate_commutes]
