-- This file contains the Regex.Point.derive function.
-- This is called point, for point in the plotted predicate graph.
-- The Regex is generic on the pair of the input and output of the predicate function or point.

import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Map

namespace VerifiedFilter.Regex

-- first returns a regular expression, where all symbols contain a tuple have been replaced with a symbol containing the first element of the tuple.
def Regex.Point.first (r: Regex (α × β)): Regex α := r.map (fun (s,_) => s)

-- Point.derive is the same as Regex.derive, except the answer to the predicate is already included in a tuple with the original symbol.
def Regex.Point.derive: (r: Regex (σ × Bool)) → Regex σ
  | emptyset => emptyset | emptystr => emptyset
  | symbol (_, res) => onlyif res emptystr
  | or r1 r2 => or (derive r1) (derive r2)
  | concat r1 r2 => or
      (concat (derive r1) (first r2))
      (onlyif (null r1) (derive r2))
  | star r1 => concat (derive r1) (star (first r1))
  | interleave r1 r2 => or
      (interleave (derive r1) (first r2))
      (interleave (derive r2) (first r1))
  | and r1 r2 => and (derive r1) (derive r2)
  | compliment r1 => compliment (derive r1)
  | xor r1 r2 => xor (derive r1) (derive r2)

namespace Regex.Point

-- map_first proves that if you mapping over a regular expression to create a tuple,
-- where the original symbol is the first element and then apply first,
-- you get back the original regular expression.
theorem map_first (f: σ → β) (r: Regex σ):
  first (Regex.map r (fun s => (s, f s))) = r := by
  induction r with
  | emptyset =>
    simp only [Regex.map, first]
  | emptystr =>
    simp only [Regex.map, first]
  | symbol _ =>
    simp only [Regex.map, first]
  | or r1 r2 ih1 ih2 =>
    simp only [Regex.map, first]
    simp only [or.injEq]
    apply And.intro
    · exact ih1
    · exact ih2
  | concat r1 r2 ih1 ih2 =>
    simp only [Regex.map, first]
    simp only [concat.injEq]
    apply And.intro
    · exact ih1
    · exact ih2
  | star r1 ih1 =>
    simp only [Regex.map, first]
    simp only [star.injEq]
    exact ih1
  | interleave r1 r2 ih1 ih2 =>
    simp only [Regex.map, first]
    simp only [interleave.injEq]
    apply And.intro
    · exact ih1
    · exact ih2
  | and r1 r2 ih1 ih2 =>
    simp only [Regex.map, first]
    simp only [and.injEq]
    apply And.intro
    · exact ih1
    · exact ih2
  | compliment r1 ih1 =>
    simp only [Regex.map, first]
    simp only [compliment.injEq]
    exact ih1
  | xor r1 r2 ih1 ih2 =>
    simp only [Regex.map, first]
    simp only [xor.injEq]
    apply And.intro
    · exact ih1
    · exact ih2

-- We prove that mapping a predicate and then taking the point derivative is
-- the same as taking the derivative of a regular expression.
theorem regex_derive_is_point_derive (Φ: σ → α → Bool) (r: Regex σ) (a: α):
  Regex.derive Φ r a = Regex.Point.derive (r.map (fun s => (s, Φ s a))) := by
  induction r with
  | emptyset =>
    simp only [Regex.derive, Regex.map, derive]
  | emptystr =>
    simp only [Regex.derive, Regex.map, derive]
  | symbol _ =>
    simp only [Regex.derive, Regex.map, derive]
  | or r1 r2 ih1 ih2 =>
    simp only [Regex.derive, Regex.map, derive]
    rw [← ih1]
    rw [← ih2]
  | concat r1 r2 ih1 ih2 =>
    simp only [Regex.derive, Regex.map, derive]
    rw [← ih1]
    rw [← ih2]
    have h : first (r2.map fun s => (s, Φ s a)) = r2 := by
      apply map_first
    have h' : (r1.map fun s => (s, Φ s a)).null = r1.null := by
      apply map_null
    rw [h]
    rw [h']
  | star r1 ih1 =>
    simp only [Regex.derive, Regex.map, derive]
    rw [← ih1]
    have h : first (r1.map fun s => (s, Φ s a)) = r1 := by
      apply map_first
    rw [h]
  | interleave r1 r2 ih1 ih2 =>
    simp only [Regex.derive, Regex.map, derive]
    rw [← ih1]
    rw [← ih2]
    have h1 : first (r1.map fun s => (s, Φ s a)) = r1 := by
      apply map_first
    have h2 : first (r2.map fun s => (s, Φ s a)) = r2 := by
      apply map_first
    rw [h1]
    rw [h2]
  | and r1 r2 ih1 ih2 =>
    simp only [Regex.derive, Regex.map, derive]
    rw [← ih1]
    rw [← ih2]
  | compliment r1 ih1 =>
    simp only [Regex.derive, Regex.map, derive]
    rw [← ih1]
  | xor r1 r2 ih1 ih2 =>
    simp only [Regex.derive, Regex.map, derive]
    rw [← ih1]
    rw [← ih2]
