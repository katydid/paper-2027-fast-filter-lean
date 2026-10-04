-- replace replaces the symbols that were extracted from a regular expression with the symbols found at the indices in the Vector.
-- It is used by leave in Katydid.lean and ExtractReplace.lean.

import VerifiedFilter.Std.Vector

import VerifiedFilter.Regex.SymCount
import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.RegexID

namespace VerifiedFilter.Regex.Regex

-- replaceLE is a helper function for defining the replace function.
def replaceLE (r: RegexID n) (xs: Vector σ l) (h: n <= l): Regex σ :=
  match r with
  | emptyset => emptyset | emptystr => emptystr
  | symbol ⟨s, hs⟩ => symbol (Vector.get xs (Fin.mk s (by omega)))
  | or r1 r2 => or (replaceLE r1 xs h) (replaceLE r2 xs h)
  | concat r1 r2 => concat (replaceLE r1 xs h) (replaceLE r2 xs h)
  | star r1 => star (replaceLE r1 xs h)
  | interleave r1 r2 => interleave (replaceLE r1 xs h) (replaceLE r2 xs h)
  | and r1 r2 => and (replaceLE r1 xs h) (replaceLE r2 xs h)
  | compliment r1 => compliment (replaceLE r1 xs h)
  | xor r1 r2 => xor (replaceLE r1 xs h) (replaceLE r2 xs h)

-- replace replaces the symbols that were extracted from a regular expression with the symbols found at the indices in the Vector.
def replace (r: Regex (Fin n)) (xs: Vector σ n): Regex σ :=
  replaceLE r xs (Nat.le_refl n)

-- example of using replace.
#guard replace (or (symbol 0) (star (symbol 1))) #v['a', 'b']
  = (or (symbol 'a') (star (symbol 'b')))

theorem replaceLE_cast_both (r: RegexID n) (xs: Vector σ n) (h: n = l):
  replaceLE r xs (by omega) = replaceLE (RegexID.cast r h) (Vector.cast h xs) (by omega) := by
  subst h
  simp only [Vector.cast_rfl]
  rfl

theorem replaceLE_cast_symcount (r: RegexID n) (xs: Vector σ n) (h: n = l):
  replaceLE r xs (by omega) = replaceLE r (Vector.cast h xs) (by omega) := by
  subst h
  simp only [Vector.cast_rfl]

theorem replaceLE_take (r: RegexID n) (xs: Vector σ (n + l)):
  replaceLE r (Vector.take xs n) (by omega) = replaceLE r xs (by omega):= by
  induction r with
  | emptyset =>
    simp only [replaceLE]
  | emptystr =>
    simp only [replaceLE]
  | symbol s =>
    simp only [replaceLE]
    obtain ⟨s, hs⟩ := s
    simp only [Regex.symbol.injEq]
    rw [Vector.take_get]
    omega
  | or r1 r2 ih1 ih2 =>
    simp only [replaceLE, Regex.or.injEq]
    rw [← ih1]
    rw [← ih2]
    apply And.intro rfl rfl
  | concat r1 r2 ih1 ih2 =>
    simp only [replaceLE, Regex.concat.injEq]
    rw [← ih1]
    rw [← ih2]
    apply And.intro rfl rfl
  | star r1 ih1 =>
    simp only [replaceLE]
    rw [← ih1]
  | interleave r1 r2 ih1 ih2 =>
    simp only [replaceLE, Regex.interleave.injEq]
    rw [← ih1]
    rw [← ih2]
    apply And.intro rfl rfl
  | and r1 r2 ih1 ih2 =>
    simp only [replaceLE, Regex.and.injEq]
    rw [← ih1]
    rw [← ih2]
    apply And.intro rfl rfl
  | compliment r1 ih1 =>
    simp only [replaceLE]
    rw [← ih1]
  | xor r1 r2 ih1 ih2 =>
    simp only [replaceLE, Regex.xor.injEq]
    rw [← ih1]
    rw [← ih2]
    apply And.intro rfl rfl

theorem replaceLE_regexid_add (r: RegexID n) (xs: Vector σ (n + l)):
  replaceLE r xs (by omega) = replaceLE (RegexID.cast_add l r) xs (by omega):= by
  induction r with
  | emptyset =>
    simp only [replaceLE, RegexID.cast_add, Regex.map]
  | emptystr =>
    simp only [replaceLE, RegexID.cast_add, Regex.map]
  | symbol s =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Fin.val_castLE]
  | or r1 r2 ih1 ih2 =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Regex.or.injEq]
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | concat r1 r2 ih1 ih2 =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Regex.concat.injEq]
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | star r1 ih1 =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Regex.star.injEq]
    rw [ih1]
    rfl
  | interleave r1 r2 ih1 ih2 =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Regex.interleave.injEq]
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | and r1 r2 ih1 ih2 =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Regex.and.injEq]
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | compliment r1 ih1 =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Regex.compliment.injEq]
    rw [ih1]
    rfl
  | xor r1 r2 ih1 ih2 =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Regex.xor.injEq]
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
