import VerifiedFilter.Std.Bytes
import Std.Data.HashMap
import Std

import Base64Lean

def decode_base64 (s: String): Except String Bytes :=
  match decode s with
  | Option.some k => return k.data
  | Option.none => throw s!"failed to decode base64 {s}"
