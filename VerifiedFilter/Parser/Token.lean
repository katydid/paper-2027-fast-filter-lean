-- Token defines all the Tokens that the `Parser Token` can return.
-- This is useful to emulate a Parser that has parsed serialized data, such as JSON or Protocol Buffers.

import VerifiedFilter.Std.Bytes
import VerifiedFilter.Std.Float

inductive Token where
  | null | bool (v: Bool) | string (v: String) | bytes (v: Bytes)
  | int64 (v: Int64) | float64 (v: Float64Bits) | decimal (v: String)
  | nanoseconds (v: Int64) | datetime (v: String) | tag (v: String)
  deriving DecidableEq, Ord, Repr, Hashable

instance : ToString Token :=
  ⟨ fun t =>
    match t with
    | Token.null => "_"
    | Token.bool v =>
      if v
      then "t"
      else "f"
    | Token.bytes v => "x:" ++ reprStr v
    | Token.string v => v
    | Token.int64 v => "-:" ++ reprStr v
    | Token.float64 v => ".:" ++ reprStr v.toFloat
    | Token.decimal v => "/:" ++ v
    | Token.nanoseconds v => "9:" ++ reprStr v
    | Token.datetime v => "z:" ++ v
    | Token.tag v => "#:" ++ v
  ⟩

namespace Token
