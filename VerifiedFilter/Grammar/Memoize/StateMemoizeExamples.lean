-- Examples of using the optimized Katydid algorithm with memoization to validate and filter.

import VerifiedFilter.Std.Hedge

import VerifiedFilter.Regex.Memoize.StateMemoize

import VerifiedFilter.Grammar.Grammar
import VerifiedFilter.Grammar.Memoize.StateMemoize

import VerifiedFilter.Pred.AnyEq
import VerifiedFilter.Pred.Compare

open VerifiedFilter.Regex
open Hedge
open Regex.Memoize
open Pred
open Regex

def validate [DecidableEq φ] [Hashable φ] (G: Grammar n φ) (Φ: φ → α → Bool) (nodes: Hedge α): Bool :=
  StateMemoize.Grammar.validate.run memoizeState.init G Φ nodes

def filter [DecidableEq φ] [Hashable φ] (G: Grammar n φ) (Φ: φ → α → Bool) (hedges: List (Hedge α)): List (Hedge α) :=
  StateMemoize.Grammar.filter.run memoizeState.init G Φ hedges

def eq (v: α × Fin n) := symbol (Pred.Compare.Pred.eq v.1, v.2)
def field (v: α × Fin n) := contains (symbol (Pred.Compare.Pred.eq v.1, v.2))

def simple: Grammar 2 (Pred.Compare.Pred String) :=
  Grammar.mk (field ("Category", 1)) #v[emptystr, eq ("Computer Science", 0)]

#guard validate simple Pred.Compare.Pred.evalb
  [node "Category" [node "Computer Science" []]]

#guard validate simple Pred.Compare.Pred.evalb
  [node "Name" [node "ITP" []], node "Category" [node "Computer Science" []]]

#guard validate simple Pred.Compare.Pred.evalb
  [node "Name" [node "ICFP" []], node "Category" [node "Functional Programming" []]]
  = false

def complex : Grammar 7 (Pred.Compare.Pred String) :=
  Grammar.mk (interleave (eq ("Due", 1)) (interleave (eq ("Loc", 5)) starAny)) #v[emptystr,
    or (field ("Year", 2)) (and (field ("Year", 3)) (field ("Month", 4))),
    eq ("2026", 0), eq ("2025", 0), symbol (Pred.Compare.Pred.ge "10", 0),
    field ("Cont", 6), eq ("EU", 0)]

private def itp_2026 :=
  [
    node "Name" [node "ITP" []],
    node "Loc" [
      node "Cont" [node "EU" []],
      node "City" [node "Lisbon" []]
    ],
    node "Due" [
      node "Year" [node "2026" []],
      node "Month" [node "02" []],
      node "Day" [node "19" []],
    ],
  ]

#guard validate complex Pred.Compare.Pred.evalb itp_2026

private def itp_late_2025 :=
  [
    node "Name" [node "ITP" []],
    node "Loc" [
      node "Cont" [node "EU" []],
      node "City" [node "Amsterdam" []]
    ],
    node "Due" [
      node "Year" [node "2025" []],
      node "Month" [node "11" []],
      node "Day" [node "19" []],
    ],
  ]

#guard validate complex Pred.Compare.Pred.evalb itp_late_2025

private def itp_2027 := [
    node "Name" [node "ITP" []],
    node "Loc" [
      node "Cont" [node "EU" []],
    ],
    node "Due" [
      node "Y" [node "2027" []],
      node "Month" [node "02" []],
      node "Day" [node "19" []],
    ],
  ]

#guard validate complex Pred.Compare.Pred.evalb itp_2027 = false

private def itp_antarctia := [
    node "Name" [node "ITP" []],
    node "Loc" [
      node "Cont" [node "AN" []],
    ],
    node "Due" [
      node "Y" [node "2026" []],
      node "Month" [node "02" []],
      node "Day" [node "19" []],
    ],
  ]

#guard validate complex Pred.Compare.Pred.evalb itp_antarctia = false

#guard filter complex Pred.Compare.Pred.evalb [itp_2026, itp_late_2025, itp_2027, itp_antarctia] = [itp_2026, itp_late_2025]
