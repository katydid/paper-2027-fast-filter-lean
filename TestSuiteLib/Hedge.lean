import Lean.Data.Json.Parser
import Std

import VerifiedFilter.Std.Hedge
import VerifiedFilter.Std.Except
import VerifiedFilter.Std.Base64
import VerifiedFilter.Std.Float
import VerifiedFilter.Parser.Token

open Lean
open Lean.Json

namespace TestSuiteLib

def Token.fromPair? (kind: String) (value: String): Except String Token := do
  match kind with
  | "unknown" =>
    throw "unknown token"
  | "null" =>
    return Token.null
  | "false" =>
    return Token.bool false
  | "true" =>
    return Token.bool true
  | "bytes" =>
    Token.bytes <$> decode_base64 value
  | "string" =>
    return Token.string value
  | "int64" =>
    match value.toInt? with
    | Option.none => throw s!"int64 could not parse {value}"
    | Option.some i => return Token.int64 i.toInt64
  | "float64" =>
    Token.float64 <$> Float.toBits <$> Float.fromString? value
  | "decimal" =>
    return Token.decimal value
  | "nanoseconds" =>
    match value.toInt? with
    | Option.none => throw s!"int64 could not parse {value}"
    | Option.some i => return Token.nanoseconds i.toInt64
  | "dateTime" =>
    return Token.datetime value
  | "tag" =>
    return Token.tag value
  | _ =>
    throw s!"unexpected kind: {kind}"

def Token.fromJson? (j: Json): Except String Token :=
  match j with
  | Json.obj (kvPairs : Std.TreeMap.Raw String Json) =>
    let kv := kvPairs.toList
    match kv with
    | [("Kind", Json.str kind), ("Value", Json.str value)] =>
      Token.fromPair? kind value
    | [("Value", Json.str value), ("Kind", Json.str kind)] =>
      Token.fromPair? kind value
    | [("Kind", Json.str kind)] =>
      Token.fromPair? kind ""
    | _ =>
      throw s!"Token expected object with Kind and Value, but got {kv}"
  | _ => throw s! "Token expected object, but got {j}"

instance : FromJson Token where
  fromJson? := Token.fromJson?

partial def Hedge.Node.fromJson? (j: Json): Except String (Hedge.Node Token) := do
  match j with
  | Json.obj (kvPairs : Std.TreeMap.Raw String Json) =>
    let kv := kvPairs.toList
    match kv with
    | [("Children", Json.arr children), ("Label", label)] =>
      let label <- Token.fromJson? label
      let children <- List.mapM Hedge.Node.fromJson? children.toList
      return Hedge.Node.node label children
    | [("Label", label), ("Children", Json.arr children)] =>
      let label <- Token.fromJson? label
      let children <- List.mapM Hedge.Node.fromJson? children.toList
      return Hedge.Node.node label children
    | [("Label", label)] =>
      let label <- Token.fromJson? label
      return Hedge.Node.node label []
    | _ =>
      throw s!"Hedge.Node expected object with Label and Children, but got {kv}"
  | _ => throw s!"Hedge.Node expected object, but got {j}"

instance : FromJson (Hedge.Node Token) where
  fromJson? := Hedge.Node.fromJson?

def Hedge.fromJson? (j: Json): Except String (Hedge Token) := do
  match j with
  | Json.arr (elems) =>
    List.mapM Hedge.Node.fromJson? elems.toList
  | _ => throw s!"Hedge expected array, but got {j}"

instance : FromJson (Hedge Token) where
  fromJson? := Hedge.fromJson?

#guard Hedge.Node.fromJson? (mkObj [
    ("Label", mkObj [("Kind", str "string"), ("Value", str "A")]),
    ("Children", Json.arr #[ mkObj [("Label", mkObj [("Kind", str "string"), ("Value", str "B")])] ])
  ])
  = Except.ok (Hedge.Node.node (Token.string "A") [Hedge.Node.node (Token.string "B") []])

#guard Hedge.Node.fromJson? (mkObj [
    ("Label", mkObj [("Kind", str "int64"), ("Value", str "123")]),
  ])
  = Except.ok (Hedge.Node.node (Token.int64 123) [])
