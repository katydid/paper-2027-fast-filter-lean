import Lean.Data.Json.FromToJson
import Lean.Data.Json.Parser

import VerifiedFilter.Std.Except
import VerifiedFilter.Std.Bytes
import VerifiedFilter.Std.Int
import VerifiedFilter.Std.Float

open Lean -- Lean.FromJson

namespace TestSuiteLib.GoGrammar

inductive Typ where
  | unknown
  | single_double
  | single_int
  | single_uint
  | single_bool
  | single_bytes
  | single_string
  | single_tag
  | list_double
  | list_int
  | list_uint
  | list_bool
  | list_bytes
  | list_string
  | list_tag
  deriving Repr, DecidableEq

def Typ.fromUInt8 (u: UInt8): Except String Typ := do
  match u with
  | 0 => return Typ.unknown
  | 101 => return Typ.single_double
  | 103 => return Typ.single_int
  | 104 => return Typ.single_uint
  | 108 => return Typ.single_bool
  | 109 => return Typ.single_string
  | 112 => return Typ.single_bytes
  | 113 => return Typ.single_tag
  | 201 => return Typ.list_double
  | 203 => return Typ.list_int
  | 204 => return Typ.list_uint
  | 208 => return Typ.list_bool
  | 209 => return Typ.list_string
  | 212 => return Typ.list_bytes
  | 213 => return Typ.list_tag
  | _ => throw s!"Typ.fromJson? unexpected {u}"

def Typ.fromJson? (j: Json): Except String Typ :=
  match j with
  | Json.num n => Typ.fromUInt8 n.toFloat.toUInt8
  | _ => throw s!"Typ.fromJson? expected number {j}"

instance : FromJson Typ where
  fromJson? := Typ.fromJson?

-- type Space struct {
-- 	Space []string `json:"Space,omitempty"`
-- }

structure Space where
  Spaces: Option (List String)
  deriving Repr, DecidableEq, FromJson

#guard (fromJson? (α := Space) =<< Lean.Json.parse r#"{"Spaces": ["\n", "\t", " "]}"#)
  = Except.ok { Spaces := ["\n", "\t", " "] }

-- type Keyword struct {
-- 	Before *Space `json:"Before,omitempty"`
-- 	Value  string `json:"Value"`
-- }

structure Keyword where
  Before: Option Space
  Value: String
  deriving FromJson, Repr, DecidableEq

#guard fromJson? (α := Keyword) =<< Lean.Json.parse r#"{"Value": "a"}"#
  = Except.ok { Before := none, Value := "a" }

#guard fromJson? (α := Keyword) =<< Lean.Json.parse r#"{"Before": {"Spaces": [" "]}, "Value": "a"}"#
  = Except.ok { Before := some { Spaces := [" "] }, Value := "a" }

-- type Variable struct {
-- 	Type types.Type `json:"Type"`
-- }

structure Variable where
  Typ: Typ
  deriving Repr, DecidableEq

def Variable.fromJson? (j: Json): Except String Variable :=
  match j with
  | Json.obj kvPairs =>
    match kvPairs.toList with
    | [("Type", jtyp)] => do
      let typ <- Typ.fromJson? jtyp
      return {Typ := typ}
    | _ => throw s!"Variable.fromJson? expected object with Type field, but got {j}"
  | _ => throw s!"Variable.fromJson? expected object {j}"

instance : FromJson Variable where
  fromJson? := Variable.fromJson?

#guard Variable.fromJson? =<< Lean.Json.parse r#"{"Type": 103}"#
  = Except.ok { Typ := Typ.single_int }

-- type Terminal struct {
-- 	Before      *Space    `json:"Before,omitempty"`
-- 	DoubleValue *float64  `json:"DoubleValue,omitempty"`
-- 	IntValue    *int64    `json:"IntValue,omitempty"`
-- 	UintValue   *uint64   `json:"UintValue,omitempty"`
-- 	BoolValue   *bool     `json:"BoolValue,omitempty"`
-- 	StringValue *string   `json:"StringValue,omitempty"`
-- 	BytesValue  []byte    `json:"BytesValue,omitempty"`
-- 	TagValue    *string   `json:"TagValue,omitempty"`
-- 	Variable    *Variable `json:"Variable,omitempty"`
-- }

structure Terminal where
  Before: Option Space
  DoubleValue: Option Float64Bits
  IntValue: Option Int64
  UintValue: Option UInt64
  BoolValue: Option Bool
  StringValue: Option String
  BytesValue: Option Bytes
  TagValue: Option String
  Variable: Option Variable
  deriving Repr, DecidableEq, FromJson

#guard fromJson? (α := Terminal) =<< Lean.Json.parse r#"{"IntValue": 123}"#
  = Except.ok {
    Before := none,
    DoubleValue := none,
    IntValue := some 123,
    UintValue := none,
    BoolValue := none,
    StringValue := none,
    BytesValue := none,
    TagValue := none,
    Variable := none
  }

-- type AnyName struct {
-- 	Underscore *Keyword `json:"Underscore,omitempty"`
-- }

structure AnyName where
  Underscore: Keyword
  deriving FromJson, Repr, DecidableEq

-- type RegexName struct {
-- 	Tilde   *Keyword `json:"Tilde,omitempty"`
-- 	Pattern string   `json:"Pattern"`
-- }

structure RegexName where
  Tilde: Keyword
  Pattern: String
  deriving FromJson, Repr, DecidableEq

-- type Name struct {
-- 	Before      *Space   `json:"Before,omitempty"`
-- 	DoubleValue *float64 `json:"DoubleValue,omitempty"`
-- 	IntValue    *int64   `json:"IntValue,omitempty"`
-- 	UintValue   *uint64  `json:"UintValue,omitempty"`
-- 	BoolValue   *bool    `json:"BoolValue,omitempty"`
-- 	StringValue *string  `json:"StringValue,omitempty"`
-- 	BytesValue  []byte   `json:"BytesValue,omitempty"`
-- 	TagValue    *string  `json:"TagValue,omitempty"`
-- }

structure NameValue where
  Before: Option Space
  DoubleValue: Option Float64Bits
  IntValue: Option Int64
  UintValue: Option UInt64
  BoolValue: Option Bool
  StringValue: Option String
  BytesValue: Option Bytes
  TagValue: Option String
  deriving Repr, DecidableEq, FromJson

#guard fromJson? (α := NameValue) =<< Lean.Json.parse r#"{"Before": {"Spaces": [" "]}, "StringValue": "a"}"#
  = Except.ok {
    Before := some { Spaces := [" "] },
    DoubleValue := none,
    IntValue := none,
    UintValue := none,
    BoolValue := none,
    StringValue := some "a",
    BytesValue := none,
    TagValue := none
  }

-- type NameExpr struct {
-- 	Name          *Name          `json:"Name,omitempty"`
-- 	AnyName       *AnyName       `json:"AnyName,omitempty"`
-- 	NameConj      *NameConj      `json:"NameConj,omitempty"`
-- 	AnyNameExcept *AnyNameExcept `json:"AnyNameExcept,omitempty"`
-- 	NameChoice    *NameChoice    `json:"NameChoice,omitempty"`
-- 	RegexName     *RegexName     `json:"RegexName,omitempty"`
-- }

-- type AnyNameExcept struct {
-- 	Exclamation *Keyword  `json:"Exclamation,omitempty"`
-- 	OpenParen   *Keyword  `json:"OpenParen,omitempty"`
-- 	Except      *NameExpr `json:"Except,omitempty"`
-- 	CloseParen  *Keyword  `json:"CloseParen,omitempty"`
-- }

-- type NameChoice struct {
-- 	OpenParen  *Keyword  `json:"OpenParen,omitempty"`
-- 	Left       *NameExpr `json:"Left,omitempty"`
-- 	Pipe       *Keyword  `json:"Pipe,omitempty"`
-- 	Right      *NameExpr `json:"Right,omitempty"`
-- 	CloseParen *Keyword  `json:"CloseParen,omitempty"`
-- }

-- type NameConj struct {
-- 	OpenParen  *Keyword  `json:"OpenParen,omitempty"`
-- 	Left       *NameExpr `json:"Left,omitempty"`
-- 	Ampersand  *Keyword  `json:"Ampersand,omitempty"`
-- 	Right      *NameExpr `json:"Right,omitempty"`
-- 	CloseParen *Keyword  `json:"CloseParen,omitempty"`
-- }

inductive NameExpr where
  | Name: NameValue -> NameExpr
  | AnyNam: AnyName -> NameExpr
  | RegexNam: RegexName -> NameExpr
  | AnyNameExcept (Exclamation: Keyword) (OpenParen: Keyword) (Except: NameExpr) (CloseParen: Keyword): NameExpr
  | NameChoice (OpenParen: Option Keyword) (Left: NameExpr) (Pipe: Keyword) (Right: NameExpr) (CloseParen: Option Keyword): NameExpr
  | NameConj (OpenParen: Option Keyword) (Left: NameExpr) (Ampersand: Keyword) (Right: NameExpr) (CloseParen: Option Keyword): NameExpr
  deriving Repr, DecidableEq

def get? (kvpairs: Std.TreeMap.Raw String α) (key: String): Except String α :=
  match kvpairs.get? key with
  | none => throw s!"missing key {key}"
  | some v => return v

def keyword (kvpairs: Std.TreeMap.Raw String Json) (key: String): Except String Keyword :=
  match kvpairs.get? key with
  | none => throw s!"missing key {key}"
  | some v => FromJson.fromJson? (α := Keyword) v

def keyword? (kvpairs: Std.TreeMap.Raw String Json) (key: String): Except String (Option Keyword) :=
  match kvpairs.get? key with
  | none => return none
  | some v => FromJson.fromJson? (α := Keyword) v

def space? (kvpairs: Std.TreeMap.Raw String Json) (key: String): Except String (Option Space) :=
  match kvpairs.get? key with
  | none => return none
  | some v => FromJson.fromJson? (α := Space) v

def string (kvpairs: Std.TreeMap.Raw String Json) (key: String): Except String String :=
  match kvpairs.get? key with
  | none => throw s!"missing key {key}"
  | some v => FromJson.fromJson? (α := String) v

partial def NameExpr.fromJson? (j: Json): Except String NameExpr :=
  match j with
  | Json.obj kvPairs =>
    match kvPairs.toList with
    | [("Name", jvalue)] => NameExpr.Name <$> FromJson.fromJson? jvalue
    | [("AnyName", jvalue)] => NameExpr.AnyNam <$> FromJson.fromJson? jvalue
    | [("RegexName", jvalue)] => NameExpr.RegexNam <$> FromJson.fromJson? jvalue
    | [("AnyNameExcept", Json.obj jkvpairs)] =>
      NameExpr.AnyNameExcept <$>
        (keyword jkvpairs "Exclamation") <*>
        (keyword jkvpairs "OpenParen") <*>
        (NameExpr.fromJson? =<< get? jkvpairs "Except") <*>
        (keyword jkvpairs "CloseParen")
    | [("NameChoice", Json.obj jkvpairs)] =>
      NameExpr.NameChoice <$>
        (keyword? jkvpairs "OpenParen") <*>
        (NameExpr.fromJson? =<< get? jkvpairs "Left") <*>
        (keyword jkvpairs "Pipe") <*>
        (NameExpr.fromJson? =<< get? jkvpairs "Right") <*>
        (keyword? jkvpairs "CloseParen")
    | [("NameConj", Json.obj jkvpairs)] =>
      NameExpr.NameConj <$>
        (keyword? jkvpairs "OpenParen") <*>
        (NameExpr.fromJson? =<< get? jkvpairs "Left") <*>
        (keyword jkvpairs "Ampersand") <*>
        (NameExpr.fromJson? =<< get? jkvpairs "Right") <*>
        (keyword? jkvpairs "CloseParen")
    | _ => throw s!"NameExpr.fromJson? expected object with a name, but got {j}"
  | _ => throw s!"NameExpr.fromJson? expected object {j}"

instance : FromJson NameExpr where
  fromJson? := NameExpr.fromJson?

-- type Expr struct {
-- 	RightArrow *Keyword  `json:"RightArrow,omitempty"`
-- 	Comma      *Keyword  `json:"Comma,omitempty"`
-- 	Terminal   *Terminal `json:"Terminal,omitempty"`
-- 	List       *List     `json:"List,omitempty"`
-- 	Function   *Function `json:"Function,omitempty"`
-- 	BuiltIn    *BuiltIn  `json:"BuiltIn,omitempty"`
-- }

-- type List struct {
-- 	Before     *Space     `json:"Before,omitempty"`
-- 	Type       types.Type `json:"Type"`
-- 	OpenCurly  *Keyword   `json:"OpenCurly,omitempty"`
-- 	Elems      []*Expr    `json:"Elems,omitempty"`
-- 	CloseCurly *Keyword   `json:"CloseCurly,omitempty"`
-- }

-- type Function struct {
-- 	Before     *Space   `json:"Before,omitempty"`
-- 	Name       string   `json:"Name"`
-- 	OpenParen  *Keyword `json:"OpenParen,omitempty"`
-- 	Params     []*Expr  `json:"Params,omitempty"`
-- 	CloseParen *Keyword `json:"CloseParen,omitempty"`
-- }

-- type BuiltIn struct {
-- 	Symbol *Keyword `json:"Symbol,omitempty"`
-- 	Expr   *Expr    `json:"Expr,omitempty"`
-- }

inductive Expr where
  | Terminal (RightArrow: Option Keyword) (Comma: Option Keyword) (Terminal: Terminal)
  | List (RightArrow: Option Keyword) (Comma: Option Keyword) (Before: Option Space) (Typ: Typ) (OpenCurly: Keyword) (Params: List Expr) (CloseCurly: Keyword)
  | Function (RightArrow: Option Keyword) (Comma: Option Keyword) (Before: Option Space) (Name: String) (OpenParen: Keyword) (Params: List Expr) (CloseParen: Keyword)
  | BuiltIn (RightArrow: Option Keyword) (Comma: Option Keyword) (Symbol: Keyword) (Expr: Expr)
  deriving Repr, BEq
-- Not deriving DecidableEq, because nested inductive types are not supported https://github.com/leanprover/lean4/issues/2329

partial def Expr.fromJson? (j: Json): Except String Expr :=
  match j with
  | Json.obj outerKvPairs =>
    let oneKey := outerKvPairs.toList.filter (fun (k, _) => k != "RightArrow" && k != "Comma")
    match oneKey with
    | [("Terminal", Json.obj innerKvPairs)] =>
      Expr.Terminal <$>
        (keyword? outerKvPairs "RightArrow") <*>
        (keyword? outerKvPairs "Comma") <*>
        (FromJson.fromJson? (Json.obj innerKvPairs))
    | [("List", Json.obj innerKvPairs)] =>
      Expr.List <$>
        (keyword? outerKvPairs "RightArrow") <*>
        (keyword? outerKvPairs "Comma") <*>
        (space? innerKvPairs "Before") <*>
        (FromJson.fromJson? =<< get? innerKvPairs "Type") <*>
        (keyword innerKvPairs "OpenCurly") <*>
        (
          match get? innerKvPairs "Params" with
          | Except.error _ => return []
          | Except.ok jparams =>
          match jparams with
          | Json.arr elems => elems.toList.mapM Expr.fromJson?
          | _ => throw s!"Expr.fromJson? list expected params to be an array, but got {jparams}"
        ) <*>
        (keyword innerKvPairs "CloseCurly")
    | [("Function", Json.obj innerKvPairs)] =>
      Expr.Function <$>
        (keyword? outerKvPairs "RightArrow") <*>
        (keyword? outerKvPairs "Comma") <*>
        (space? innerKvPairs "Before") <*>
        (string innerKvPairs "Name") <*>
        (keyword innerKvPairs "OpenParen") <*>
        (
          match get? innerKvPairs "Params" with
          | Except.error _ => return []
          | Except.ok jparams =>
          match jparams with
          | Json.arr elems => elems.toList.mapM Expr.fromJson?
          | _ => throw s!"Expr.fromJson? list expected params to be an array, but got {jparams}"
        ) <*>
        (keyword innerKvPairs "CloseParen")
    | [("BuiltIn", Json.obj innerKvPairs)] =>
      Expr.BuiltIn <$>
        (keyword? outerKvPairs "RightArrow") <*>
        (keyword? outerKvPairs "Comma") <*>
        (keyword innerKvPairs "Symbol") <*>
        (Expr.fromJson? =<< get? innerKvPairs "Expr")
    | _ => throw s!"Expr.fromJson? expected object with an expr, but got {j}"
  | _ => throw s!"Expr.fromJson? expected object {j}"

instance : FromJson Expr where
  fromJson? := Expr.fromJson?

-- type Empty struct {
-- 	Empty *Keyword `json:"Empty,omitempty"`
-- }

structure EmptyNode where
  Empty: Keyword
  deriving Repr, DecidableEq, FromJson

-- type ZAny struct {
-- 	Star *Keyword `json:"Star,omitempty"`
-- }

structure ZAny where
  Star: Keyword
  deriving Repr, DecidableEq, FromJson

-- type Reference struct {
-- 	At   *Keyword `json:"At,omitempty"`
-- 	Name string   `json:"Name"`
-- }

structure Reference where
  At: Keyword
  Name: String
  deriving Repr, DecidableEq, FromJson

-- type LeafNode struct {
-- 	Expr *Expr `json:"Expr,omitempty"`
-- }

structure LeafNode where
  Expr: Expr
  deriving Repr, FromJson
-- Not deriving DecidableEq, because Expr can't derive DecidableEq

-- type Pattern struct {
-- 	Empty      *Empty      `json:"Empty,omitempty"`
-- 	ZAny       *ZAny       `json:"ZAny,omitempty"`
-- 	Reference  *Reference  `json:"Reference,omitempty"`

-- 	LeafNode   *LeafNode   `json:"LeafNode,omitempty"`
-- 	TreeNode   *TreeNode   `json:"TreeNode,omitempty"`

-- 	Or         *Or         `json:"Or,omitempty"`
-- 	And        *And        `json:"And,omitempty"`
-- 	Xor        *Xor        `json:"Xor,omitempty"`

-- 	Concat     *Concat     `json:"Concat,omitempty"`
-- 	Interleave *Interleave `json:"Interleave,omitempty"`

-- 	ZeroOrMore *ZeroOrMore `json:"ZeroOrMore,omitempty"`
-- 	Not        *Not        `json:"Not,omitempty"`
-- 	Contains   *Contains   `json:"Contains,omitempty"`
-- 	Optional   *Optional   `json:"Optional,omitempty"`
-- }

-- type TreeNode struct {
-- 	Name    *NameExpr `json:"Name,omitempty"`
-- 	Colon   *Keyword  `json:"Colon,omitempty"`
-- 	Pattern *Pattern  `json:"Pattern,omitempty"`
-- }

-- type Or struct {
-- 	OpenParen    *Keyword `json:"OpenParen,omitempty"`
-- 	LeftPattern  *Pattern `json:"LeftPattern,omitempty"`
-- 	Pipe         *Keyword `json:"Pipe,omitempty"`
-- 	RightPattern *Pattern `json:"RightPattern,omitempty"`
-- 	CloseParen   *Keyword `json:"CloseParen,omitempty"`
-- }

-- type And struct {
-- 	OpenParen    *Keyword `json:"OpenParen,omitempty"`
-- 	LeftPattern  *Pattern `json:"LeftPattern,omitempty"`
-- 	Ampersand    *Keyword `json:"Ampersand,omitempty"`
-- 	RightPattern *Pattern `json:"RightPattern,omitempty"`
-- 	CloseParen   *Keyword `json:"CloseParen,omitempty"`
-- }

-- type Xor struct {
-- 	OpenParen    *Keyword `json:"OpenParen,omitempty"`
-- 	LeftPattern  *Pattern `json:"LeftPattern,omitempty"`
-- 	Caret        *Keyword `json:"Caret,omitempty"`
-- 	RightPattern *Pattern `json:"RightPattern,omitempty"`
-- 	CloseParen   *Keyword `json:"CloseParen,omitempty"`
-- }

-- type Contains struct {
-- 	Dot     *Keyword `json:"Dot,omitempty"`
-- 	Pattern *Pattern `json:"Pattern,omitempty"`
-- }

-- type Concat struct {
-- 	OpenBracket  *Keyword `json:"OpenBracket,omitempty"`
-- 	LeftPattern  *Pattern `json:"LeftPattern,omitempty"`
-- 	Comma        *Keyword `json:"Comma,omitempty"`
-- 	RightPattern *Pattern `json:"RightPattern,omitempty"`
-- 	ExtraComma   *Keyword `json:"ExtraComma,omitempty"`
-- 	CloseBracket *Keyword `json:"CloseBracket,omitempty"`
-- }

-- type Interleave struct {
-- 	OpenCurly      *Keyword `json:"OpenCurly,omitempty"`
-- 	LeftPattern    *Pattern `json:"LeftPattern,omitempty"`
-- 	SemiColon      *Keyword `json:"SemiColon,omitempty"`
-- 	RightPattern   *Pattern `json:"RightPattern,omitempty"`
-- 	ExtraSemiColon *Keyword `json:"ExtraSemiColon,omitempty"`
-- 	CloseCurly     *Keyword `json:"CloseCurly,omitempty"`
-- }

-- type ZeroOrMore struct {
-- 	OpenParen  *Keyword `json:"OpenParen,omitempty"`
-- 	Pattern    *Pattern `json:"Pattern,omitempty"`
-- 	CloseParen *Keyword `json:"CloseParen,omitempty"`
-- 	Star       *Keyword `json:"Star,omitempty"`
-- }

-- type Not struct {
-- 	Exclamation *Keyword `json:"Exclamation,omitempty"`
-- 	OpenParen   *Keyword `json:"OpenParen,omitempty"`
-- 	Pattern     *Pattern `json:"Pattern,omitempty"`
-- 	CloseParen  *Keyword `json:"CloseParen,omitempty"`
-- }

-- type Contains struct {
-- 	Dot     *Keyword `json:"Dot,omitempty"`
-- 	Pattern *Pattern `json:"Pattern,omitempty"`
-- }

-- type Optional struct {
-- 	OpenParen    *Keyword `json:"OpenParen,omitempty"`
-- 	Pattern      *Pattern `json:"Pattern,omitempty"`
-- 	CloseParen   *Keyword `json:"CloseParen,omitempty"`
-- 	QuestionMark *Keyword `json:"QuestionMark,omitempty"`
-- }

inductive Pattern where
  | Empty (Empty: EmptyNode)
  | ZAny (ZAny: ZAny)
  | Reference (Reference: Reference)
  | LeafNode (LeafNode: LeafNode)
  | TreeNode (Name: NameExpr) (Colon: Option Keyword) (Pattern: Pattern)
  | Or (OpenParen: Option Keyword) (LeftPattern: Pattern) (Pipe: Keyword) (RightPattern: Pattern) (CloseParen: Option Keyword)
  | And (OpenParen: Option Keyword) (LeftPattern: Pattern) (Ampersand: Keyword) (RightPattern: Pattern) (CloseParen: Option Keyword)
  | Xor (OpenParen: Option Keyword) (LeftPattern: Pattern) (Caret: Keyword) (RightPattern: Pattern) (CloseParen: Option Keyword)
  | Concat (OpenBracket: Option Keyword) (LeftPattern: Pattern) (Comma: Keyword) (RightPattern: Pattern) (ExtraComma: Option Keyword) (CloseBracket: Option Keyword)
  | Interleave (OpenCurly: Option Keyword) (LeftPattern: Pattern) (SemiColon: Keyword) (RightPattern: Pattern) (ExtraSemiColon: Option Keyword) (CloseCurly: Option Keyword)
  | ZeroOrMore (OpenParen: Option Keyword) (Pattern: Pattern) (CloseParen: Option Keyword) (Star: Keyword)
  | Not (Exclamation: Keyword) (OpenParen: Option Keyword) (Pattern: Pattern) (CloseParen: Option Keyword)
  | Contains (Dot: Keyword) (Pattern: Pattern)
  | Optional (OpenParen: Option Keyword) (Pattern: Pattern) (CloseParen: Option Keyword) (QuestionMark: Keyword)
  deriving Repr
-- Not deriving DecidableEq, because Expr can't derive DecidableEq


partial def Pattern.fromJson? (j: Json): Except String Pattern :=
  match j with
  | Json.obj kvPairs =>
    match kvPairs.toList with
    | [("Empty", jvalue)] =>
      Pattern.Empty <$> FromJson.fromJson? jvalue
    | [("ZAny", jvalue)] =>
      Pattern.ZAny <$> FromJson.fromJson? jvalue
    | [("Reference", jvalue)] =>
      Pattern.Reference <$> FromJson.fromJson? jvalue
    | [("LeafNode", jvalue)] =>
      Pattern.LeafNode <$> FromJson.fromJson? jvalue
    | [("TreeNode", Json.obj jkvpair)] =>
      Pattern.TreeNode <$>
        (FromJson.fromJson? =<< get? jkvpair "Name") <*>
        (keyword? jkvpair "Colon") <*>
        (Pattern.fromJson? =<< get? jkvpair "Pattern")
    | [("Or", Json.obj jkvpair)] =>
      Pattern.Or <$>
        (keyword? jkvpair "OpenParen") <*>
        (Pattern.fromJson? =<< get? jkvpair "LeftPattern") <*>
        (keyword jkvpair "Pipe") <*>
        (Pattern.fromJson? =<< get? jkvpair "RightPattern") <*>
        (keyword? jkvpair "CloseParen")
    | [("And", Json.obj jkvpair)] =>
      Pattern.And <$>
        (keyword? jkvpair "OpenParen") <*>
        (Pattern.fromJson? =<< get? jkvpair "LeftPattern") <*>
        (keyword jkvpair "Ampersand") <*>
        (Pattern.fromJson? =<< get? jkvpair "RightPattern") <*>
        (keyword? jkvpair "CloseParen")
    | [("Xor", Json.obj jkvpair)] =>
      Pattern.Xor <$>
        (keyword? jkvpair "OpenParen") <*>
        (Pattern.fromJson? =<< get? jkvpair "LeftPattern") <*>
        (keyword jkvpair "Caret") <*>
        (Pattern.fromJson? =<< get? jkvpair "RightPattern") <*>
        (keyword? jkvpair "CloseParen")
    | [("Concat", Json.obj jkvpair)] =>
      Pattern.Concat <$>
        (keyword? jkvpair "OpenBracket") <*>
        (Pattern.fromJson? =<< get? jkvpair "LeftPattern") <*>
        (keyword jkvpair "Comma") <*>
        (Pattern.fromJson? =<< get? jkvpair "RightPattern") <*>
        (keyword? jkvpair "ExtraComma") <*>
        (keyword? jkvpair "CloseBracket")
    | [("Interleave", Json.obj jkvpair)] =>
      Pattern.Interleave <$>
        (keyword? jkvpair "OpenCurly") <*>
        (Pattern.fromJson? =<< get? jkvpair "LeftPattern") <*>
        (keyword jkvpair "SemiColon") <*>
        (Pattern.fromJson? =<< get? jkvpair "RightPattern") <*>
        (keyword? jkvpair "ExtraSemiColon") <*>
        (keyword? jkvpair "CloseCurly")
    | [("ZeroOrMore", Json.obj jkvpair)] =>
      Pattern.ZeroOrMore <$>
        (keyword? jkvpair "OpenParen") <*>
        (Pattern.fromJson? =<< get? jkvpair "Pattern") <*>
        (keyword jkvpair "CloseParen") <*>
        (keyword jkvpair "Star")
    | [("Not", Json.obj jkvpair)] =>
      Pattern.Not <$>
        (keyword jkvpair "Exclamation") <*>
        (keyword? jkvpair "OpenParen") <*>
        (Pattern.fromJson? =<< get? jkvpair "Pattern") <*>
        (keyword jkvpair "CloseParen")
    | [("Contains", Json.obj jkvpair)] =>
       Pattern.Contains <$>
        (keyword jkvpair "Dot") <*>
        (Pattern.fromJson? =<< get? jkvpair "Pattern")
    | [("Optional", Json.obj jkvpair)] =>
      Pattern.ZeroOrMore <$>
        (keyword? jkvpair "OpenParen") <*>
        (Pattern.fromJson? =<< get? jkvpair "Pattern") <*>
        (keyword jkvpair "CloseParen") <*>
        (keyword jkvpair "QuestionMark")
    | _ => throw s!"Pattern.fromJson? expected object with a pattern, but got {j}"
  | _ => throw s!"Pattern.fromJson? expected object {j}"

instance : FromJson Pattern where
  fromJson? := Pattern.fromJson?

-- type PatternDecl struct {
-- 	Hash    *Keyword `json:"Hash,omitempty"`
-- 	Before  *Space   `json:"Before,omitempty"`
-- 	Name    string   `json:"Name"`
-- 	Eq      *Keyword `json:"Eq,omitempty"`
-- 	Pattern *Pattern `json:"Pattern,omitempty"`
-- }

structure PatternDecl where
  Hash: Keyword
  Before: Option Space
  Name: String
  Eq: Keyword
  Pattern: Pattern
  deriving FromJson, Repr
-- Not deriving DecidableEq, because Expr can't derive DecidableEq

-- type Grammar struct {
-- 	TopPattern   *Pattern       `json:"TopPattern,omitempty"`
-- 	PatternDecls []*PatternDecl `json:"PatternDecls,omitempty"`
-- 	After        *Space         `json:"After,omitempty"`
-- }

structure Grammar where
  TopPattern: Pattern
  PatternDecls: Option (List PatternDecl)
  After: Option Space
  deriving FromJson, Repr
-- Not deriving DecidableEq, because Expr can't derive DecidableEq
