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
