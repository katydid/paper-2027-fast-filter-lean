-- In this file we prove that if we split function application of the map function over a regular expression can be broken up into three steps:
-- 1. extract
-- 2. apply function
-- 3. replace

-- We prove the following properties:
-- * theorem extract_replace_is_id: r = replace (extract r).1 (extract r).2
-- * theorem extract_replace_is_map: Regex.map r f = replace (extract r).1 (Vector.map f (extract r).2)

import VerifiedFilter.Regex.Extract
import VerifiedFilter.Regex.Replace

namespace VerifiedFilter.Regex.Regex

theorem extractAcc_replace_is_id (r: Regex σ) (acc: Vector σ l):
  r = replace (extractAcc r acc).1 (extractAcc r acc).2 := by
  simp only [replace]
  revert acc l
  induction r with
  | emptyset =>
    intro n acc
    simp only [replaceLE, extractAcc]
  | emptystr =>
    intro n acc
    simp only [replaceLE, extractAcc]
  | symbol s =>
    intro n acc
    simp only [replaceLE, extractAcc]
    rw [Vector.push_get]
  | or r1 r2 ih1 ih2 =>
    intro n acc
    simp only [extractAcc]
    simp only [replaceLE]
    have hh1 :
      r1 =
        (replaceLE
          (RegexID.cast_assoc (RegexID.cast_add |r2| (extractAcc r1 acc).1))
          (Vector.cast_assoc (extractAcc r2 (extractAcc r1 acc).2).2)
          (by omega)
        ) := by
      clear ih2
      rw [RegexID.cast_assoc]
      rw [Vector.cast_assoc]
      rw [← replaceLE_cast_both]
      rw [← replaceLE_regexid_add]
      rw [← replaceLE_take]
      rw [extractAcc_take]
      have ih1' := ih1 acc
      rw [replaceLE_cast_symcount] at ih1'
      rw [← ih1']
      omega
    rw [← hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.cast_assoc]
    rw [Vector.cast_assoc]
    rw [← replaceLE_cast_both]
    rw [← ih2 ((extractAcc r1 acc).2)]
  | concat r1 r2 ih1 ih2 =>
    intro n acc
    simp only [extractAcc]
    simp only [replaceLE]
    have hh1 :
      r1 =
        (replaceLE
          (RegexID.cast_assoc (RegexID.cast_add |r2| (extractAcc r1 acc).1))
          (Vector.cast_assoc (extractAcc r2 (extractAcc r1 acc).2).2)
          (by omega)
        ) := by
      clear ih2
      rw [RegexID.cast_assoc]
      rw [Vector.cast_assoc]
      rw [← replaceLE_cast_both]
      rw [← replaceLE_regexid_add]
      rw [← replaceLE_take]
      rw [extractAcc_take]
      have ih1' := ih1 acc
      rw [replaceLE_cast_symcount] at ih1'
      rw [← ih1']
      omega
    rw [← hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.cast_assoc]
    rw [Vector.cast_assoc]
    rw [← replaceLE_cast_both]
    rw [← ih2 ((extractAcc r1 acc).2)]
  | star r1 ih1 =>
    simp only [extractAcc]
    simp only [replaceLE]
    intro n acc
    rw [← ih1 acc]
  | interleave r1 r2 ih1 ih2 =>
    intro n acc
    simp only [extractAcc]
    simp only [replaceLE]
    have hh1 :
      r1 =
        (replaceLE
          (RegexID.cast_assoc (RegexID.cast_add |r2| (extractAcc r1 acc).1))
          (Vector.cast_assoc (extractAcc r2 (extractAcc r1 acc).2).2)
          (by omega)
        ) := by
      clear ih2
      rw [RegexID.cast_assoc]
      rw [Vector.cast_assoc]
      rw [← replaceLE_cast_both]
      rw [← replaceLE_regexid_add]
      rw [← replaceLE_take]
      rw [extractAcc_take]
      have ih1' := ih1 acc
      rw [replaceLE_cast_symcount] at ih1'
      rw [← ih1']
      omega
    rw [← hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.cast_assoc]
    rw [Vector.cast_assoc]
    rw [← replaceLE_cast_both]
    rw [← ih2 ((extractAcc r1 acc).2)]
  | and r1 r2 ih1 ih2 =>
    intro n acc
    simp only [extractAcc]
    simp only [replaceLE]
    have hh1 :
      r1 =
        (replaceLE
          (RegexID.cast_assoc (RegexID.cast_add |r2| (extractAcc r1 acc).1))
          (Vector.cast_assoc (extractAcc r2 (extractAcc r1 acc).2).2)
          (by omega)
        ) := by
      clear ih2
      rw [RegexID.cast_assoc]
      rw [Vector.cast_assoc]
      rw [← replaceLE_cast_both]
      rw [← replaceLE_regexid_add]
      rw [← replaceLE_take]
      rw [extractAcc_take]
      have ih1' := ih1 acc
      rw [replaceLE_cast_symcount] at ih1'
      rw [← ih1']
      omega
    rw [← hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.cast_assoc]
    rw [Vector.cast_assoc]
    rw [← replaceLE_cast_both]
    rw [← ih2 ((extractAcc r1 acc).2)]
  | compliment r1 ih1 =>
    simp only [extractAcc]
    simp only [replaceLE]
    intro n acc
    rw [← ih1 acc]
  | xor r1 r2 ih1 ih2 =>
    intro n acc
    simp only [extractAcc]
    simp only [replaceLE]
    have hh1 :
      r1 =
        (replaceLE
          (RegexID.cast_assoc (RegexID.cast_add |r2| (extractAcc r1 acc).1))
          (Vector.cast_assoc (extractAcc r2 (extractAcc r1 acc).2).2)
          (by omega)
        ) := by
      clear ih2
      rw [RegexID.cast_assoc]
      rw [Vector.cast_assoc]
      rw [← replaceLE_cast_both]
      rw [← replaceLE_regexid_add]
      rw [← replaceLE_take]
      rw [extractAcc_take]
      have ih1' := ih1 acc
      rw [replaceLE_cast_symcount] at ih1'
      rw [← ih1']
      omega
    rw [← hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.cast_assoc]
    rw [Vector.cast_assoc]
    rw [← replaceLE_cast_both]
    rw [← ih2 ((extractAcc r1 acc).2)]

theorem extractAcc_replaceLE_is_id (r: Regex σ) (acc: Vector σ l):
  r = replaceLE (extractAcc r acc).1 (extractAcc r acc).2 (by omega) := by
  rw [← replace]
  rw [← extractAcc_replace_is_id]

theorem extract_replace_is_id (r: Regex σ):
  r = replace (extract r).1 (extract r).2 := by
  simp only [extract]
  simp only [replace]
  rw [← replaceLE_cast_both]
  rw [← extractAcc_replaceLE_is_id r #v[]]

theorem extractAcc_replace_is_fmap (r: Regex α) (acc: Vector α l) (f: α → β):
  Regex.map r f = replace (extractAcc r acc).1 (Vector.map f (extractAcc r acc).2) := by
  simp only [replace]
  revert acc l
  induction r with
  | emptyset =>
    intro n acc
    simp only [replaceLE, extractAcc, Regex.map]
  | emptystr =>
    intro n acc
    simp only [replaceLE, extractAcc, Regex.map]
  | symbol s =>
    intro n acc
    simp only [replaceLE, extractAcc, Regex.map]
    simp only [Vector.push_map]
    rw [Vector.push_get]
  | or r1 r2 ih1 ih2 =>
    intro n acc
    simp only [extractAcc]
    simp only [replaceLE]
    simp only [Regex.map]
    have hh1 :
      Regex.map r1 f =
        (replaceLE
          (RegexID.cast_assoc (RegexID.cast_add |r2| (extractAcc r1 acc).1))
          (Vector.map f (Vector.cast_assoc (extractAcc r2 (extractAcc r1 acc).2).2))
          (by omega)
        ) := by
      clear ih2
      rw [RegexID.cast_assoc]
      rw [Vector.cast_assoc]
      rw [Vector.map_cast]
      rw [← replaceLE_cast_both]
      rw [← replaceLE_regexid_add]
      rw [← replaceLE_take]
      rw [extractAcc_take_fmap]
      have ih1' := ih1 acc
      rw [replaceLE_cast_symcount] at ih1'
      rw [← ih1']
      omega
    rw [← hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.cast_assoc]
    rw [Vector.cast_assoc]
    rw [Vector.map_cast]
    rw [← replaceLE_cast_both]
    rw [← ih2 ((extractAcc r1 acc).2)]
  | concat r1 r2 ih1 ih2 =>
    intro n acc
    simp only [extractAcc]
    simp only [replaceLE]
    simp only [Regex.map]
    have hh1 :
      Regex.map r1 f =
        (replaceLE
          (RegexID.cast_assoc (RegexID.cast_add |r2| (extractAcc r1 acc).1))
          (Vector.map f (Vector.cast_assoc (extractAcc r2 (extractAcc r1 acc).2).2))
          (by omega)
        ) := by
      clear ih2
      rw [RegexID.cast_assoc]
      rw [Vector.cast_assoc]
      rw [Vector.map_cast]
      rw [← replaceLE_cast_both]
      rw [← replaceLE_regexid_add]
      rw [← replaceLE_take]
      rw [extractAcc_take_fmap]
      have ih1' := ih1 acc
      rw [replaceLE_cast_symcount] at ih1'
      rw [← ih1']
      omega
    rw [← hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.cast_assoc]
    rw [Vector.cast_assoc]
    rw [Vector.map_cast]
    rw [← replaceLE_cast_both]
    rw [← ih2 ((extractAcc r1 acc).2)]
  | star r1 ih1 =>
    simp only [extractAcc]
    simp only [replaceLE]
    intro n acc
    rw [← ih1 acc]
    simp only [Regex.map]
  | interleave r1 r2 ih1 ih2 =>
    intro n acc
    simp only [extractAcc]
    simp only [replaceLE]
    simp only [Regex.map]
    have hh1 :
      Regex.map r1 f =
        (replaceLE
          (RegexID.cast_assoc (RegexID.cast_add |r2| (extractAcc r1 acc).1))
          (Vector.map f (Vector.cast_assoc (extractAcc r2 (extractAcc r1 acc).2).2))
          (by omega)
        ) := by
      clear ih2
      rw [RegexID.cast_assoc]
      rw [Vector.cast_assoc]
      rw [Vector.map_cast]
      rw [← replaceLE_cast_both]
      rw [← replaceLE_regexid_add]
      rw [← replaceLE_take]
      rw [extractAcc_take_fmap]
      have ih1' := ih1 acc
      rw [replaceLE_cast_symcount] at ih1'
      rw [← ih1']
      omega
    rw [← hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.cast_assoc]
    rw [Vector.cast_assoc]
    rw [Vector.map_cast]
    rw [← replaceLE_cast_both]
    rw [← ih2 ((extractAcc r1 acc).2)]
  | and r1 r2 ih1 ih2 =>
    intro n acc
    simp only [extractAcc]
    simp only [replaceLE]
    simp only [Regex.map]
    have hh1 :
      Regex.map r1 f =
        (replaceLE
          (RegexID.cast_assoc (RegexID.cast_add |r2| (extractAcc r1 acc).1))
          (Vector.map f (Vector.cast_assoc (extractAcc r2 (extractAcc r1 acc).2).2))
          (by omega)
        ) := by
      clear ih2
      rw [RegexID.cast_assoc]
      rw [Vector.cast_assoc]
      rw [Vector.map_cast]
      rw [← replaceLE_cast_both]
      rw [← replaceLE_regexid_add]
      rw [← replaceLE_take]
      rw [extractAcc_take_fmap]
      have ih1' := ih1 acc
      rw [replaceLE_cast_symcount] at ih1'
      rw [← ih1']
      omega
    rw [← hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.cast_assoc]
    rw [Vector.cast_assoc]
    rw [Vector.map_cast]
    rw [← replaceLE_cast_both]
    rw [← ih2 ((extractAcc r1 acc).2)]
  | compliment r1 ih1 =>
    simp only [extractAcc]
    simp only [replaceLE]
    intro n acc
    rw [← ih1 acc]
    simp only [Regex.map]
  | xor r1 r2 ih1 ih2 =>
    intro n acc
    simp only [extractAcc]
    simp only [replaceLE]
    simp only [Regex.map]
    have hh1 :
      Regex.map r1 f =
        (replaceLE
          (RegexID.cast_assoc (RegexID.cast_add |r2| (extractAcc r1 acc).1))
          (Vector.map f (Vector.cast_assoc (extractAcc r2 (extractAcc r1 acc).2).2))
          (by omega)
        ) := by
      clear ih2
      rw [RegexID.cast_assoc]
      rw [Vector.cast_assoc]
      rw [Vector.map_cast]
      rw [← replaceLE_cast_both]
      rw [← replaceLE_regexid_add]
      rw [← replaceLE_take]
      rw [extractAcc_take_fmap]
      have ih1' := ih1 acc
      rw [replaceLE_cast_symcount] at ih1'
      rw [← ih1']
      omega
    rw [← hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.cast_assoc]
    rw [Vector.cast_assoc]
    rw [Vector.map_cast]
    rw [← replaceLE_cast_both]
    rw [← ih2 ((extractAcc r1 acc).2)]

theorem extractAcc_replaceLE_is_fmap (r: Regex α) (acc: Vector α l) (f: α → β):
  Regex.map r f = replaceLE (extractAcc r acc).1 (Vector.map f (extractAcc r acc).2) (by omega) := by
  rw [← replace]
  rw [← extractAcc_replace_is_fmap]

theorem extract_replace_is_map (r: Regex α) (f: α → β):
  Regex.map r f = replace (extract r).1 (Vector.map f (extract r).2) := by
  simp only [extract]
  simp only [replace]
  rw [Vector.map_cast]
  rw [← replaceLE_cast_both]
  rw [← extractAcc_replaceLE_is_fmap r #v[]]
