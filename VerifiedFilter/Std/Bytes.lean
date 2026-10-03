import Lean.Data.Json
import Lean.Data.Json.FromToJson

open Lean
open Lean.Json

def Bytes := Array UInt8
  deriving DecidableEq, Ord, Repr, Hashable

def UInt8.fromJson? (j: Json): Except String UInt8 :=
  match j with
  | Json.num n =>
    return n.toFloat.toUInt8
  | _ => throw s!"UInt8.fromJson? expected number {j}"

def Bytes.fromJson? (j: Json): Except String Bytes :=
  match j with
  | Json.arr elems => Array.mapM UInt8.fromJson? elems
  | _ => throw s!"Bytes.fromJson? expected array {j}"

instance : FromJson Bytes where
  fromJson? := Bytes.fromJson?

instance : LT Bytes where
  lt x y := LT.lt x.toList y.toList

@[extern "lean_bytes_dec_lt", implicit_reducible]
def Bytes.decLt (a b : Bytes) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toList < b.toList))

instance : LE Bytes where
  le x y := LE.le x.toList y.toList

@[extern "lean_bytes_dec_le", implicit_reducible]
def Bytes.decLe (a b : Bytes) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toList ≤ b.toList))

attribute [instance] Bytes.decLt Bytes.decLe
