-- Katydids.lean is a version of Katydid.lean that handles a Vector a Regexes instead of a single Regex.
-- This is used by Fused.

import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Point
import VerifiedFilter.Regex.Preds
import VerifiedFilter.Regex.Extracts
import VerifiedFilter.Regex.Replaces

namespace VerifiedFilter.Regex

def Regex.Point.derives (rs: Vector (Regex (σ × Bool)) l): Vector (Regex σ) l :=
  Vector.map (xs := rs) Regex.Point.derive

namespace Regex

def enters (lookup: σ → Bool → β) (rs: Vector (Regex σ) l): Preds σ β |rs| :=
  Preds.mk' (Regex.extracts rs).2 lookup

def leaves (rs: Vector (Regex σ) l) (bools: Vector Bool |rs|): (Vector (Regex σ) l) :=
  let points: Vector (σ × Bool) |rs| := Vector.zip (Regex.extracts rs).2 bools
  let replaced: Vector (Regex (σ × Bool)) l := Regex.replaces (Regex.extracts rs).1 points
  Regex.Point.derives replaced

end Regex

def Regex.Katydid.derives (Γ: σ → Bool → β) (ν: β → Bool) (Φ: σ → Bool) (r: Vector (Regex σ) l): Vector (Regex σ) l :=
  enters Γ r |> Preds.eval Φ |> Vector.map ν |> leaves r
