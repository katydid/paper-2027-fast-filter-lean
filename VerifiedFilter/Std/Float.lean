import Lean.Data.Json.Parser
import Lean.Data.Json

open Lean
open Lean.Json

def Float.fromString? (s: String): Except String Float := do
  let j <- Lean.Json.parse s
  match j with
  | Lean.Json.num n =>
    return n.toFloat
  | _ => throw s!"Float64.fromString? expected json number, but got {j}"

abbrev Float64Bits := UInt64
def toFloat (f: Float64Bits): Float := Float.ofBits f
def fromFloat (f: Float): Float64Bits := Float.toBits f

def Float64Bits.fromJson? (j: Json): Except String Float64Bits :=
  Float.toBits <$> Float.fromJson? j

instance : FromJson Float64Bits where
  fromJson? := Float64Bits.fromJson?
