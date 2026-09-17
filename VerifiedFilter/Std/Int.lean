import Lean.Data.Json.Parser
import Lean.Data.Json

open Lean
open Lean.Json

def Int64.fromJson? (j: Json): Except String Int64 :=
  Float.toInt64 <$> Float.fromJson? j

instance : FromJson Int64 where
  fromJson? := Int64.fromJson?
