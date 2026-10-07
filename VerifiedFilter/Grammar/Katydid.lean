-- The optimized Katydid algorithm without memoization.
-- We define and proof correctness of derive, validate and filter, see theorem derive_commutes, validate_commutes and mem_filter.

import VerifiedFilter.Std.Decidable
import VerifiedFilter.Std.Hedge

import VerifiedFilter.Regex.Lang
import VerifiedFilter.Regex.Katydid

import VerifiedFilter.Grammar.Denote
import VerifiedFilter.Grammar.Grammar
import VerifiedFilter.Grammar.Lang

open VerifiedFilter.Regex
open Hedge

def Grammar.Katydid.derive (G: Grammar n φ) (Φ: φ → α → Bool)
  (r: Regex (φ × Ref n)) (node: Node α): Regex (φ × Ref n) :=
  let nodePred := fun ((labelPred, ref): (φ × Ref n)) =>
    let ⟨label, children⟩ := node
    let childr := if Φ labelPred label then G.lookup ref else Regex.emptyset
    Regex.null (List.foldl (Grammar.Katydid.derive G Φ) childr children)
  Regex.Katydid.derive nodePred r -- enter r |> Vector.map nodePred |> leave r

namespace Grammar.Katydid

def validate (G: Grammar n φ) (Φ: φ → α → Bool) (nodes: Hedge α): Bool :=
  Regex.null (List.foldl (derive G Φ) G.start nodes)

def filter (G: Grammar n φ) (Φ: φ → α → Bool) (hedges: List (Hedge α)) :=
  List.filter (validate G Φ) hedges

end Grammar.Katydid

-- A helper lemma to prove derive_emptyset, derive_emptystr, etc.
-- We needed to partially apply the node, to avoid the need for another termination proof.
-- This theorem undoes the partial application, so that we can reuse regular expression theorems that have not been partially applied.
theorem Grammar.Katydid.unapply_hedge_param_and_flip
  (G: Grammar n φ) (Φ: φ → α → Bool) (node: Node α):
  (fun ((pred, ref): (φ × Ref n)) =>
    let ⟨label, children⟩ := node
    let childr: Regex (φ × Ref n) := if Φ pred label then G.lookup ref else Regex.emptyset
    Regex.null (List.foldl (derive G Φ) childr children)
  )
  =
  (flip fun ((pred, ref): (φ × Ref n)) (node': Node α) =>
    let ⟨label, children⟩ := node'
    let childr: Regex (φ × Ref n) := if Φ pred label then G.lookup ref else Regex.emptyset
    Regex.null (List.foldl (derive G Φ) childr children)
  ) node := by
  rfl

-- A helper lemma for derive_commutes.
-- We undo the partial application and rewrite to the point derivative to a normal derivative for the emptyset operator.
theorem Grammar.Katydid.derive_emptyset {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (a: Node α):
  Grammar.Katydid.derive G Φ Regex.emptyset a = Regex.emptyset := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

-- A helper lemma for derive_commutes.
-- We undo the partial application and rewrite to the point derivative to a normal derivative for the emptystr operator.
theorem Grammar.Katydid.derive_emptystr (G: Grammar n φ) Φ (x: Node α):
  Grammar.Katydid.derive G Φ Regex.emptystr x = Regex.emptyset := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

-- A helper lemma for derive_commutes.
-- We undo the partial application and rewrite to the point derivative to a normal derivative for the symbol operator.
theorem Grammar.Katydid.derive_symbol (G: Grammar n φ) Φ (x: Node α):
  Grammar.Katydid.derive G Φ (Regex.symbol (pred, ref)) x
    = Regex.onlyif ((let ⟨label, children⟩ := x
        (List.foldl (Grammar.Katydid.derive  G Φ)
          (if Φ pred label then G.lookup ref else Regex.emptyset)
          children
        ).null) = true) Regex.emptystr := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

-- A helper lemma for derive_commutes.
-- We undo the partial application and rewrite to the point derivative to a normal derivative for the or operator.
theorem Grammar.Katydid.derive_or (G: Grammar n φ) Φ r1 r2 (node: Node α):
  Grammar.Katydid.derive G Φ (Regex.or r1 r2) node = Regex.or
    (Grammar.Katydid.derive G Φ r1 node) (Grammar.Katydid.derive G Φ r2 node) := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

-- A helper lemma for derive_commutes.
-- We undo the partial application and rewrite to the point derivative to a normal derivative for the concat operator.
theorem Grammar.Katydid.derive_concat (G: Grammar n φ) Φ r1 r2 (x: Node α):
  Grammar.Katydid.derive G Φ (Regex.concat r1 r2) x
    = Regex.or
      (Regex.concat (Grammar.Katydid.derive G Φ r1 x) r2)
      (Regex.onlyif (Regex.null r1) (Grammar.Katydid.derive G Φ r2 x)) := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

-- A helper lemma for derive_commutes.
-- We undo the partial application and rewrite to the point derivative to a normal derivative for the star operator.
theorem Grammar.Katydid.derive_star {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (r1: Regex (φ × Ref n)) (a: Node α):
  Grammar.Katydid.derive G Φ (Regex.star r1) a
  = Regex.concat (Grammar.Katydid.derive G Φ r1 a) (Regex.star r1) := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

-- A helper lemma for derive_commutes.
-- We undo the partial application and rewrite to the point derivative to a normal derivative for the interleave operator.
theorem Grammar.Katydid.derive_interleave {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (r1 r2: Regex (φ × Ref n)) (a: Node α):
  Grammar.Katydid.derive G Φ (Regex.interleave r1 r2) a
  = Regex.or
    (Regex.interleave (Grammar.Katydid.derive G Φ r1 a) r2)
    (Regex.interleave (Grammar.Katydid.derive G Φ r2 a) r1) := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

-- A helper lemma for derive_commutes.
-- We undo the partial application and rewrite to the point derivative to a normal derivative for the and operator.
theorem Grammar.Katydid.derive_and {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (r1 r2: Regex (φ × Ref n)) (a: Node α):
  Grammar.Katydid.derive G Φ (Regex.and r1 r2) a
  = Regex.and (Grammar.Katydid.derive G Φ r1 a) (Grammar.Katydid.derive G Φ r2 a) := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

-- A helper lemma for derive_commutes.
-- We undo the partial application and rewrite to the point derivative to a normal derivative for the compliment operator.
theorem Grammar.Katydid.derive_compliment {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (r1: Regex (φ × Ref n)) (a: Node α):
  Grammar.Katydid.derive G Φ (Regex.compliment r1) a
  = Regex.compliment (Grammar.Katydid.derive G Φ r1 a) := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

-- A helper lemma for derive_commutes.
-- We undo the partial application and rewrite to the point derivative to a normal derivative for the xor operator.
theorem Grammar.Katydid.derive_xor {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (r1 r2: Regex (φ × Ref n)) (a: Node α):
  Grammar.Katydid.derive G Φ (Regex.xor r1 r2) a
  = Regex.xor (Grammar.Katydid.derive G Φ r1 a) (Grammar.Katydid.derive G Φ r2 a) := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

theorem Grammar.Katydid.and_start {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (label: α) (children: Hedge α):
  ((List.foldl (derive G Φ) (if Φ p label then G.lookup ref else Regex.emptyset) children).null = true)
  = (Φ p label ∧ ((List.foldl (derive G Φ) (G.lookup ref) children).null = true)) := by
  generalize (G.lookup ref) = r
  split
  case isTrue h =>
    simp_all only [true_and]
  case isFalse h =>
    simp_all only [eq_iff_iff, Bool.not_eq_true]
    induction children with
    | nil =>
      simp only [List.foldl_nil, Regex.null, Bool.false_eq_true, false_and]
    | cons x xs ih =>
      simp_all only [List.foldl_cons, Bool.false_eq_true, false_and, iff_false, Bool.not_eq_true]
      rw [derive_emptyset]
      rw [ih]

theorem Grammar.Katydid.derive_denote_symbol_is_onlyif {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (label: α) (children: Hedge α):
  Lang.derive
    (Rule.denote G Φ
      (Regex.symbol (pred, ref))
    )
    (Node.node label children)
  =
    Lang.onlyif
      (Φ pred label ∧ Rule.denote G Φ (G.lookup ref) children)
      Lang.emptystr
  := by
  funext xs
  rw [Grammar.denote_symbol]
  rw [Lang.derive_iff_node]

namespace Grammar.Katydid

-- For each operator except symbol, we complete the proof by induction on the regular expression,
-- undoing the partial application of the node, permuting the parameters,
-- and applying theorem Regex.Katydid.derive_is_Regex_derive.
-- The symbol case needs extra work.
theorem derive_commutes G Φ (r: Regex (φ × Ref n)) (n: Node α):
  Rule.denote G Φ (derive G Φ r n) = Lang.derive (Rule.denote G Φ r) n := by
  induction r with
  | emptyset =>
    rw [Grammar.Katydid.derive_emptyset]
    rw [Grammar.denote_emptyset]
    rw [Lang.derive_emptyset]
  | emptystr =>
    rw [Grammar.Katydid.derive_emptystr]
    rw [Grammar.denote_emptystr]
    rw [Grammar.denote_emptyset]
    rw [Lang.derive_emptystr]
  | symbol s =>
    obtain ⟨pred, ref⟩ := s
    obtain ⟨label, children⟩ := n

    rw [Grammar.Katydid.derive_symbol]

    rw [derive_denote_symbol_is_onlyif]
    rw [Grammar.denote_onlyif]
    rw [Grammar.denote_emptystr]
    congr

    simp only [and_start]
    congr

    generalize G.lookup ref = r
    -- We cannot apply functional induction to a recursive closure, so we have create induction via well-founded induction.
    have ihr := fun r' x (hx: x ∈ children) => derive_commutes G Φ r' x
    -- The proof proceeds by induction on the children.
    induction children generalizing r with
    | nil =>
      simp only [List.foldl_nil]
      rw [Grammar.denote_nil_is_null]
    | cons x2 xs ihxs =>
      simp only [List.foldl]
      rw [ihxs]
      -- followed by a well-founded induction by recursing on derive_commutes.
      · rw [ihr]
        · rfl
        · simp only [List.mem_cons, true_or]
      · intro x r' hxs
        rw [ihr]
        simp only [List.mem_cons]
        apply Or.inr hxs
  | or r1 r2 ih1 ih2 =>
    rw [Grammar.Katydid.derive_or]
    rw [Grammar.denote_or]
    rw [Grammar.denote_or]
    rw [Lang.derive_or]
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    rw [Grammar.Katydid.derive_concat]
    rw [Grammar.denote_concat]
    rw [Grammar.denote_or]
    rw [Grammar.denote_concat]
    rw [Grammar.denote_onlyif]
    rw [Lang.derive_concat]
    rw [← ih1]
    rw [← ih2]
    congr
    apply Grammar.null_commutes
  | star r1 ih1 =>
    rw [Grammar.Katydid.derive_star]
    rw [Grammar.denote_star]
    rw [Grammar.denote_concat]
    rw [Grammar.denote_star]
    rw [Lang.derive_star]
    rw [ih1]
  | interleave r1 r2 ih1 ih2 =>
    rw [Grammar.Katydid.derive_interleave]
    rw [Grammar.denote_or]
    rw [Grammar.denote_interleave]
    rw [Grammar.denote_interleave]
    rw [ih1]
    rw [ih2]
    rw [Grammar.denote_interleave]
    rw [Lang.derive_interleave]
  | and r1 r2 ih1 ih2 =>
    rw [Grammar.Katydid.derive_and]
    rw [Grammar.denote_and]
    rw [Grammar.denote_and]
    rw [Lang.derive_and]
    rw [ih1]
    rw [ih2]
  | compliment r1 ih1 =>
    rw [Grammar.Katydid.derive_compliment]
    rw [Grammar.denote_compliment]
    rw [ih1]
    rw [Grammar.denote_compliment]
    rw [Lang.derive_compliment]
    unfold Lang.compliment
    rfl
  | xor r1 r2 ih1 ih2 =>
    rw [Grammar.Katydid.derive_xor]
    rw [Grammar.denote_xor]
    rw [Grammar.denote_xor]
    rw [Lang.derive_xor]
    rw [ih1]
    rw [ih2]
  termination_by n
  decreasing_by
    apply Node.sizeOf_children hx

theorem derive_commutesb (G: Grammar n φ) (Φ: φ → α → Bool) (r: Regex (φ × Ref n)) (x: Node α):
  Rule.denote G (fun s a => Φ s a) (derive G Φ r x)
  = Lang.derive (Rule.denote G (fun s a => Φ s a) r) x := by
  have h1: (fun s a => Φ s a) = (fun s a => Φ s a) := by
    -- aesop?
    simp_all only
  have h2: (fun s a => Φ s a) = Φ := by
    rfl
  have h3: (derive G Φ r x) = (derive G (fun s a => Φ s a) r x) := by
    rw [h2]
  rw [h3]
  rw [h1]
  rw [derive_commutes]

theorem derives_commutes (G: Grammar n φ) (Φ: φ → α → Bool) (r: Regex (φ × Ref n)) (nodes: Hedge α):
  Grammar.Rule.denote G Φ (List.foldl (derive G Φ) r nodes) = Lang.derives (Grammar.Rule.denote G Φ r) nodes := by
  rw [Lang.derives_foldl]
  induction nodes generalizing r with
  | nil =>
    simp only [List.foldl_nil]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h := derive_commutes G Φ r x
    have ih' := ih (Grammar.Katydid.derive G Φ r x)
    rw [h] at ih'
    exact ih'

-- Using theorem derive_commutes we can prove validate_commutes.
theorem validate_commutes (G: Grammar n φ) Φ (h: Hedge α):
  (validate G Φ h = true) = Grammar.denote G Φ h := by
  unfold Grammar.denote
  rw [← Lang.validate (Grammar.Rule.denote G Φ G.start) h]
  unfold validate
  rw [← derives_commutes]
  rw [← Grammar.null_commutes]

-- Using validate_commutes we can prove mem_filter.
theorem mem_filter (Φ: φ → α → Bool) (G: Grammar n φ) (xss: List (Hedge α)) :
  ∀ xs, (xs ∈ Grammar.Katydid.filter G Φ xss) ↔ (Lang.MemFilter (Grammar.denote G Φ) xss xs) := by
  unfold Grammar.Katydid.filter
  intro xs
  rw [List.mem_filter]
  unfold Lang.MemFilter
  apply Iff.intro
  case mp =>
    intro ⟨hxs, hd⟩
    apply And.intro hxs
    rw [← Grammar.Katydid.validate_commutes]
    assumption
  case mpr =>
    intro ⟨hxs, hd⟩
    apply And.intro hxs
    rw [Grammar.Katydid.validate_commutes]
    assumption
