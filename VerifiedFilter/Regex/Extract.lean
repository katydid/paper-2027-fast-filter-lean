-- extract extracts the symbols from a regular expression into a Vector and replaces them with indices into the Vector.
-- It is used by enter and leave in Katydid.lean and ExtractReplace.lean.

import VerifiedFilter.Std.Vector

import VerifiedFilter.Regex.SymCount
import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.RegexID

namespace VerifiedFilter.Regex.Regex

private theorem lt_add_symbol:
  n < n + |symbol s| := by
  simp only [|·|]
  simp only [nsym]
  omega

-- extractAcc is a helper function for writing the extract function.
def extractAcc (r: Regex σ) (acc: Vector σ n): RegexID (n + |r|) × Vector σ (n + |r|) :=
  match r with
  | emptyset => (emptyset, acc)
  | emptystr => (emptystr, acc)
  | symbol s => (symbol (Fin.mk acc.size lt_add_symbol), Vector.push acc s)
  | or r1 r2 =>
    let (rid1, acc1) := extractAcc r1 acc
    let (rid2, acc2) := extractAcc r2 acc1
    (or (rid1.cast_add |r2|).cast_assoc rid2.cast_assoc, acc2.cast_assoc)
  | concat r1 r2 =>
    let (rid1, acc1) := extractAcc r1 acc
    let (rid2, acc2) := extractAcc r2 acc1
    (concat (rid1.cast_add |r2|).cast_assoc rid2.cast_assoc, acc2.cast_assoc)
  | star r1 => let (rid1, acc1) := extractAcc r1 acc; (star rid1, acc1)
  | interleave r1 r2 =>
    let (rid1, acc1) := extractAcc r1 acc
    let (rid2, acc2) := extractAcc r2 acc1
    (interleave (rid1.cast_add |r2|).cast_assoc rid2.cast_assoc, acc2.cast_assoc)
  | and r1 r2 =>
    let (rid1, acc1) := extractAcc r1 acc
    let (rid2, acc2) := extractAcc r2 acc1
    (and (rid1.cast_add |r2|).cast_assoc rid2.cast_assoc, acc2.cast_assoc)
  | compliment r1 => let (rid1, acc1) := extractAcc r1 acc; (compliment rid1, acc1)
  | xor r1 r2 =>
    let (rid1, acc1) := extractAcc r1 acc
    let (rid2, acc2) := extractAcc r2 acc1
    (xor (rid1.cast_add |r2|).cast_assoc rid2.cast_assoc, acc2.cast_assoc)

-- extract extracts the symbols from a regular expression into a Vector and replaces them with indices into the Vector.
def extract (r: Regex σ): Regex (Fin |r|) × Vector σ |r| :=
  let (rid, xs) := extractAcc r #v[]
  (RegexID.cast rid (by omega), Vector.cast (by omega) xs)

-- example of using extract.
#guard extract (or (symbol 'a') (star (symbol 'b')))
  = ((or (symbol 0) (star (symbol 1))), #v['a', 'b'])

theorem extractAcc_append_toList (acc: Vector σ n) (r: Regex σ):
  Vector.toList (extractAcc r acc).2 = Vector.toList (acc ++ (extractAcc r #v[]).2) := by
  induction r generalizing acc n  with
  | emptyset =>
    simp only [|·|, Nat.add_zero, extractAcc, Vector.append_nil, Vector.cast_toList]
  | emptystr =>
    simp only [|·|, Nat.add_zero, extractAcc, Vector.append_nil, Vector.cast_toList]
  | symbol s =>
    simp only [extractAcc]
    simp only [|·|, nsym, Nat.reduceAdd, Vector.push_mk, List.push_toArray, List.nil_append,
      Vector.append_singleton]
  | or r1 r2 ih1 ih2 =>
    simp only [extractAcc]
    rw [Vector.cast_assoc]
    rw [Vector.cast_assoc]
    rw [Vector.toList_append]
    rw [Vector.cast_toList]
    rw [Vector.cast_toList]
    rw [ih2]
    rw [Vector.toList_append]
    rw [ih1]
    rw [Vector.toList_append]
    rw [ih2]
    rw [ih2]
    rw [← ih2]
    rw [Vector.toList_append]
    -- aesop?
    simp_all only [List.append_assoc]
  | concat r1 r2 ih1 ih2 =>
    simp only [extractAcc]
    rw [Vector.cast_assoc]
    rw [Vector.cast_assoc]
    rw [Vector.toList_append]
    rw [Vector.cast_toList]
    rw [Vector.cast_toList]
    rw [ih2]
    rw [Vector.toList_append]
    rw [ih1]
    rw [Vector.toList_append]
    rw [ih2]
    rw [ih2]
    rw [← ih2]
    rw [Vector.toList_append]
    -- aesop?
    simp_all only [List.append_assoc]
  | star r1 ih1 =>
    simp only [extractAcc]
    rw [ih1]
  | interleave r1 r2 ih1 ih2 =>
    simp only [extractAcc]
    rw [Vector.cast_assoc]
    rw [Vector.cast_assoc]
    rw [Vector.toList_append]
    rw [Vector.cast_toList]
    rw [Vector.cast_toList]
    rw [ih2]
    rw [Vector.toList_append]
    rw [ih1]
    rw [Vector.toList_append]
    rw [ih2]
    rw [ih2]
    rw [← ih2]
    rw [Vector.toList_append]
    -- aesop?
    simp_all only [List.append_assoc]
  | and r1 r2 ih1 ih2 =>
    simp only [extractAcc]
    rw [Vector.cast_assoc]
    rw [Vector.cast_assoc]
    rw [Vector.toList_append]
    rw [Vector.cast_toList]
    rw [Vector.cast_toList]
    rw [ih2]
    rw [Vector.toList_append]
    rw [ih1]
    rw [Vector.toList_append]
    rw [ih2]
    rw [ih2]
    rw [← ih2]
    rw [Vector.toList_append]
    -- aesop?
    simp_all only [List.append_assoc]
  | compliment r1 ih1 =>
    simp only [extractAcc]
    rw [ih1]
  | xor r1 r2 ih1 ih2 =>
    simp only [extractAcc]
    rw [Vector.cast_assoc]
    rw [Vector.cast_assoc]
    rw [Vector.toList_append]
    rw [Vector.cast_toList]
    rw [Vector.cast_toList]
    rw [ih2]
    rw [Vector.toList_append]
    rw [ih1]
    rw [Vector.toList_append]
    rw [ih2]
    rw [ih2]
    rw [← ih2]
    rw [Vector.toList_append]
    -- aesop?
    simp_all only [List.append_assoc]

theorem extract_take_toList (acc: Vector σ l):
  (Vector.toList
    (Vector.take
      (extractAcc r2
        (extractAcc r1 acc).2).2
      (l + |r1|)
    )
  )
  =
  (Vector.toList (extractAcc r1 acc).2) := by
  rw [Vector.toList_take]
  rw [extractAcc_append_toList]
  rw [Vector.toList_append]
  -- aesop?
  simp_all only [Vector.length_toList, List.take_left']

theorem extractAcc_take (acc: Vector σ l):
  (Vector.take
    (extractAcc r2
      (extractAcc r1 acc).2).2
    (l + |r1|)
  )
  =
    Vector.cast
    (by omega)
    (extractAcc r1 acc).2 := by
  apply Vector.eq
  rw [extract_take_toList]
  rw [← Vector.cast_toList]

theorem extractAcc_take_toList_fmap (acc: Vector σ l):
  (Vector.toList
    (Vector.take
      (Vector.map
        f
        (extractAcc r2
          (extractAcc r1 acc).2).2
      )
      (l + |r1|)
    )
  )
  =
  (Vector.toList
    (Vector.map
      f
      (extractAcc r1 acc).2
    )
  ) := by
  rw [Vector.toList_take]
  rw [Vector.map_toList]
  rw [extractAcc_append_toList]
  rw [Vector.toList_append]
  rw [Vector.toList_map]
  -- aesop?
  simp_all only [List.map_append, List.length_map, Vector.length_toList,
    List.take_left']

theorem extractAcc_take_fmap (acc: Vector α l) (f: α → β):
  (Vector.take
    (Vector.map
      f
      (extractAcc r2
        (extractAcc r1 acc).2).2
    )
    (l + |r1|)
  )
  =
    Vector.cast
    (by omega)
    (Vector.map
      f
      (extractAcc r1 acc).2
    ) := by
  apply Vector.eq
  rw [extractAcc_take_toList_fmap]
  rw [← Vector.cast_toList]
