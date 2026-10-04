-- The memoized Katydid algorithm defined over regular expressions with an instance of the state monad.
-- This shows that memoization can be proven correct, when an instance of Memoize for enter and leave is provided, see StateMemoize.
-- see theorems StateMemoize.Regex.derive.run_is_sound, StateMemoize.validate.run_is_sound and theorem Regex.StateMemoize.mem_filter.

import VerifiedFilter.Std.Vector
import VerifiedFilter.Std.Memoize.StateMemoize

import VerifiedFilter.Regex.ExtractReplace
import VerifiedFilter.Regex.Lang
import VerifiedFilter.Regex.SymCount
import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Katydid

import VerifiedFilter.Regex.Memoize.Enter
import VerifiedFilter.Regex.Memoize.Leave
import VerifiedFilter.Regex.Memoize.Memoize

namespace VerifiedFilter.Regex.Regex.Memoize

abbrev StateMemoize σ [DecidableEq σ] [Hashable σ] := StateT (enterMemTable σ) (StateM (leaveMemTable σ))
abbrev memoizeState σ [DecidableEq σ] [Hashable σ] := (enterMemTable σ × leaveMemTable σ)
def memoizeState.init {σ: Type} [DecidableEq σ] [Hashable σ]: memoizeState σ := ((MemTable.init enter), (MemTable.init leave))
def memoizeState.enter {σ: Type} [DecidableEq σ] [Hashable σ] (m: memoizeState σ): enterMemTable σ := m.1
def memoizeState.leave {σ: Type} [DecidableEq σ] [Hashable σ] (m: memoizeState σ): leaveMemTable σ := m.2

def StateMemoize.run {σ: Type} {β: Type} [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ) (f: StateMemoize σ β): β :=
  ((StateM.run (StateT.run f state.1) state.2).1).1

def StateMemoize.Regex.derive [DecidableEq σ] [Hashable σ] (Φ: σ → Bool) (r: Regex σ): StateMemoize σ (Regex σ) :=
  Regex.Memoize.derive Φ r

def StateMemoize.Regex.derive.run {σ: Type} [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ) (Φ: σ → Bool) (r: Regex σ): Regex σ :=
  StateMemoize.run state (Regex.Memoize.derive Φ r)

#guard StateMemoize.Regex.derive.run memoizeState.init
  (· == 'a') (Regex.or (Regex.symbol 'a') (Regex.symbol 'b'))
  = Regex.or Regex.emptystr Regex.emptyset

def StateMemoize.Regex.validate [DecidableEq σ] [Hashable σ]
  (Φ: σ → α → Bool) (r: Regex σ) (xs: List α): StateMemoize σ Bool :=
  Regex.Memoize.validate Φ r xs

def StateMemoize.Regex.validate.run {σ: Type} [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ) (Φ: σ → α → Bool) (r: Regex σ) (xs: List α): Bool :=
  StateMemoize.run state (Regex.Memoize.validate Φ r xs)

#guard StateMemoize.Regex.validate.run memoizeState.init
  (· == ·) (Regex.or (Regex.symbol 'a') (Regex.symbol 'b')) ['a']
  = true

def StateMemoize.Regex.filter [DecidableEq σ] [Hashable σ]
  (Φ: σ → α → Bool) (r: Regex σ) (xss: List (List α)): StateMemoize σ (List (List α)) :=
  Regex.Memoize.filter Φ r xss

def StateMemoize.Regex.filter.run [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ)
  (Φ: σ → α → Bool) (r: Regex σ) (xss: List (List α)): List (List α) :=
  StateMemoize.run state (Regex.Memoize.filter Φ r xss)

theorem StateMemoize.Regex.derive.run_unfold [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ) (Φ: σ → Bool) (r: Regex σ):
  (StateMemoize.Regex.derive.run state Φ r) = StateMemoize.run state (Regex.Memoize.derive Φ r) :=
  rfl

theorem StateMemoize.Regex.derive.run_is_sound [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ)
  (Φ: σ → Bool) (r: Regex σ):
  StateMemoize.Regex.derive.run state Φ r = Regex.Katydid.derive Φ r := by
  rw [StateMemoize.Regex.derive.run_unfold]
  generalize StateMemoize.run state (Regex.Memoize.derive Φ r) = x
  obtain ⟨dr, hdr⟩ := x
  simp only
  rw [hdr]

theorem Regex.StateMemoize.derive_commutes {σ: Type} {α: Type} [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ) (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (a: α):
  denote Φ (StateMemoize.Regex.derive.run state (flip (decideRel Φ) a) r) = Lang.derive (denote Φ r) a := by
  rw [StateMemoize.Regex.derive.run_is_sound]
  rw [← Regex.Katydid.derive_commutes]

theorem StateMemoize.Regex.validate.run_unfold [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ) (Φ: σ → α → Bool) (r: Regex σ):
  (StateMemoize.Regex.validate.run state Φ r xs) = StateMemoize.run state (Regex.Memoize.validate Φ r xs) :=
  rfl

theorem StateMemoize.validate.run_is_sound {σ: Type} {α: Type} [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ) (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (xs: List α):
  StateMemoize.Regex.validate.run state (decideRel Φ) r xs = Regex.Katydid.validate (decideRel Φ) r xs := by
  rw [StateMemoize.Regex.validate.run_unfold]
  generalize StateMemoize.run state (Regex.Memoize.validate (decideRel Φ) r xs) = x
  obtain ⟨b, hd⟩ := x
  simp only
  assumption

theorem Regex.StateMemoize.validate_commutes {σ: Type} {α: Type} [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ) (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (xs: List α):
  StateMemoize.Regex.validate.run state (decideRel Φ) r xs = denote Φ r xs := by
  rw [StateMemoize.validate.run_is_sound]
  rw [← Regex.Katydid.validate_commutes]

theorem StateMemoize.Regex.filter.run_unfold [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ) (Φ: σ → α → Bool) (r: Regex σ):
  (StateMemoize.Regex.filter.run state Φ r xs) = StateMemoize.run state (Regex.Memoize.filter Φ r xs) :=
  rfl

theorem Regex.StateMemoize.mem_filter {σ: Type} {α: Type} [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ) (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (xs: List (List α)) :
  ∀ x, (x ∈ StateMemoize.Regex.filter.run state (decideRel Φ) r xs) ↔ (Lang.MemFilter (denote Φ r) xs x) := by
  intro x
  rw [StateMemoize.Regex.filter.run_unfold]
  generalize StateMemoize.run state (Regex.Memoize.filter (decideRel Φ) r xs) = h
  obtain ⟨res, hres⟩ := h
  simp only
  rw [hres]
  unfold Lang.MemFilter
  rw [List.mem_filter]
  rw [Katydid.validate_commutes]
