import Mathlib.Tactic.RewriteSearch
import Aesop

import TestSuiteLib.GoGrammar
import TestSuiteLib.Pred
import VerifiedFilter.Grammar
import Std
import Std.Data.HashMap

namespace TestSuiteLib

abbrev Rule := Regex (TestSuiteLib.Pred Bool × Nat)

def maxRef (r: Rule): Nat :=
  match r with
  | Regex.emptyset => 0
  | Regex.emptystr => 0
  | Regex.star r1 => maxRef r1
  | Regex.symbol s => s.2
  | Regex.or r1 r2 => max (maxRef r1) (maxRef r2)
  | Regex.concat r1 r2 => max (maxRef r1) (maxRef r2)
  | Regex.interleave r1 r2 => max (maxRef r1) (maxRef r2)
  | Regex.and r1 r2 => max (maxRef r1) (maxRef r2)
  | Regex.compliment r1 => maxRef r1
  | Regex.xor r1 r2 => max (maxRef r1) (maxRef r2)

def Rule.toFin (r: Rule) (n: Nat) (h: n > maxRef r): Regex (TestSuiteLib.Pred Bool × Ref n) :=
  match hr: r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptystr
  | Regex.star r1 => Regex.star <| Rule.toFin r1 n h
  | Regex.symbol (s1, s2) => Regex.symbol
    (s1, Fin.mk s2 (by
      simp only [maxRef] at h
      exact h
    ))
  | Regex.or r1 r2 => Regex.or
    (Rule.toFin r1 n (by simp only [maxRef] at h; omega))
    (Rule.toFin r2 n (by simp only [maxRef] at h; omega))
  | Regex.concat r1 r2 => Regex.concat
    (Rule.toFin r1 n (by simp only [maxRef] at h; omega))
    (Rule.toFin r2 n (by simp only [maxRef] at h; omega))
  | Regex.interleave r1 r2 => Regex.interleave
    (Rule.toFin r1 n (by simp only [maxRef] at h; omega))
    (Rule.toFin r2 n (by simp only [maxRef] at h; omega))
  | Regex.and r1 r2 => Regex.and
    (Rule.toFin r1 n (by simp only [maxRef] at h; omega))
    (Rule.toFin r2 n (by simp only [maxRef] at h; omega))
  | Regex.compliment r1 => Regex.compliment <| Rule.toFin r1 n h
  | Regex.xor r1 r2 => Regex.xor
    (Rule.toFin r1 n (by simp only [maxRef] at h; omega))
    (Rule.toFin r2 n (by simp only [maxRef] at h; omega))

abbrev GoGrammarMap := Std.HashMap String (GoGrammar.Pattern × Nat)

def treecount (p: GoGrammar.Pattern) (n: Nat): Nat :=
  match p with
  | GoGrammar.Pattern.Empty (_Empty: GoGrammar.EmptyNode) => n
  | GoGrammar.Pattern.ZAny (_ZAny: GoGrammar.ZAny) => n
  | GoGrammar.Pattern.Reference (_Reference: GoGrammar.Reference) => n
  | GoGrammar.Pattern.LeafNode (_LeafNode: GoGrammar.LeafNode) => n
  | GoGrammar.Pattern.TreeNode (_Name: GoGrammar.NameExpr) (_Colon: Option GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) =>
    treecount Pattern n + 1
  | GoGrammar.Pattern.Or (_OpenParen: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (_Pipe: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) =>
    treecount LeftPattern (treecount RightPattern n)
  | GoGrammar.Pattern.And (_OpenParen: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (_Ampersand: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) =>
    treecount LeftPattern (treecount RightPattern n)
  | GoGrammar.Pattern.Xor (_OpenParen: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (_Caret: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) =>
    treecount LeftPattern (treecount RightPattern n)
  | GoGrammar.Pattern.Concat (_OpenBracket: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (_Comma: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (_ExtraComma: Option GoGrammar.Keyword) (_CloseBracket: Option GoGrammar.Keyword) =>
    treecount LeftPattern (treecount RightPattern n)
  | GoGrammar.Pattern.Interleave (_OpenCurly: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (_SemiColon: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (_ExtraSemiColon: Option GoGrammar.Keyword) (_CloseCurly: Option GoGrammar.Keyword) =>
    treecount LeftPattern (treecount RightPattern n)
  | GoGrammar.Pattern.ZeroOrMore (_OpenParen: Option GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) (_Star: GoGrammar.Keyword) =>
    treecount Pattern n
  | GoGrammar.Pattern.Not (_Exclamation: GoGrammar.Keyword) (_OpenParen: Option GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) =>
    treecount Pattern n
  | GoGrammar.Pattern.Contains (_Dot: GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) =>
    treecount Pattern n
  | GoGrammar.Pattern.Optional (_OpenParen: Option GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) (_QuestionMark: GoGrammar.Keyword) =>
    treecount Pattern n

def GoGrammar.mk (g: GoGrammar.Grammar): Id GoGrammarMap := do
  let mut h: GoGrammarMap := Std.HashMap.emptyWithCapacity
  -- reserve 0 for the emptystr regex
  h := h.insert "main" (g.TopPattern, 1)
  match g.PatternDecls with
  | none => return h
  | some decls =>
  let mut n := treecount g.TopPattern 1
  for decl in decls do
    h := h.insert decl.Name (decl.Pattern, n)
    n := treecount decl.Pattern n
  h

def AnyName.toPred (_: GoGrammar.AnyName): Except String (TestSuiteLib.Pred Bool) :=
  return TestSuiteLib.Pred.any

def RegexName.toPred (r: GoGrammar.RegexName): Except String (TestSuiteLib.Pred Bool) :=
  return TestSuiteLib.Pred.regex (TestSuiteLib.Pred.string_const r.Pattern) TestSuiteLib.Pred.string_var

def NameValue.toPred (n: GoGrammar.NameValue): Except String (TestSuiteLib.Pred Bool) :=
  match n.DoubleValue with
  | some d => return TestSuiteLib.Pred.eq_double (TestSuiteLib.Pred.double_const d) TestSuiteLib.Pred.double_var
  | none =>
  match n.IntValue with
  | some i => return TestSuiteLib.Pred.eq_int (TestSuiteLib.Pred.int_const i) TestSuiteLib.Pred.int_var
  | none =>
  match n.UintValue with
  | some u => return TestSuiteLib.Pred.eq_uint (TestSuiteLib.Pred.uint_const u) TestSuiteLib.Pred.uint_var
  | none =>
  match n.BoolValue with
  | some b => return TestSuiteLib.Pred.eq_bool (TestSuiteLib.Pred.bool_const b) TestSuiteLib.Pred.bool_var
  | none =>
  match n.StringValue with
  | some s => return TestSuiteLib.Pred.eq_string (TestSuiteLib.Pred.string_const s) TestSuiteLib.Pred.string_var
  | none =>
  match n.BytesValue with
  | some b => return TestSuiteLib.Pred.eq_bytes (TestSuiteLib.Pred.bytes_const b) TestSuiteLib.Pred.bytes_var
  | none =>
  match n.TagValue with
  | some b => return TestSuiteLib.Pred.eq_string (TestSuiteLib.Pred.string_const b) TestSuiteLib.Pred.tag_var
  | none =>
    throw s!"expected one of the terminals to be set, but got {repr n}"

-- inductive NameExpr where
--   | Name: NameValue -> NameExpr
--   | AnyNam: AnyName -> NameExpr
--   | RegexNam: RegexName -> NameExpr
--   | AnyNameExcept (Exclamation: Keyword) (OpenParen: Keyword) (Except: NameExpr) (CloseParen: Keyword): NameExpr
--   | NameChoice (OpenParen: Option Keyword) (Left: NameExpr) (Pipe: Keyword) (Right: NameExpr) (CloseParen: Option Keyword): NameExpr
--   | NameConj (OpenParen: Option Keyword) (Left: NameExpr) (Ampersand: Keyword) (Right: NameExpr) (CloseParen: Option Keyword): NameExpr
--   deriving Repr, DecidableEq

def NameExpr.toPred (n: GoGrammar.NameExpr): Except String (TestSuiteLib.Pred Bool) :=
  match n with
  | GoGrammar.NameExpr.Name n => NameValue.toPred n
  | GoGrammar.NameExpr.AnyNam _ => return TestSuiteLib.Pred.any
  | GoGrammar.NameExpr.RegexNam r => return TestSuiteLib.Pred.regex (TestSuiteLib.Pred.string_const r.Pattern) TestSuiteLib.Pred.string_var
  | GoGrammar.NameExpr.AnyNameExcept _ _ e _ => TestSuiteLib.Pred.not <$> NameExpr.toPred e
  | GoGrammar.NameExpr.NameChoice _ a _ b _ => TestSuiteLib.Pred.or <$> NameExpr.toPred a <*> NameExpr.toPred b
  | GoGrammar.NameExpr.NameConj _ a _ b _ => TestSuiteLib.Pred.and <$> NameExpr.toPred a <*> NameExpr.toPred b

def Variable.toPredBool (v: GoGrammar.Variable): Except String (TestSuiteLib.Pred Bool) :=
  match v.Typ with
  | GoGrammar.Typ.single_bool => return TestSuiteLib.Pred.bool_var
  | _ => throw s!"expected variable to be Bool {repr v}"

def Variable.toPredBytes (v: GoGrammar.Variable): Except String (TestSuiteLib.Pred Bytes) :=
  match v.Typ with
  | GoGrammar.Typ.single_bytes => return TestSuiteLib.Pred.bytes_var
  | _ => throw s!"expected variable to be Bytes {repr v}"

def Variable.toPredFloat64Bits (v: GoGrammar.Variable): Except String (TestSuiteLib.Pred Float64Bits) :=
  match v.Typ with
  | GoGrammar.Typ.single_double => return TestSuiteLib.Pred.double_var
  | _ => throw s!"expected variable to be Float64Bits {repr v}"

def Variable.toPredInt64 (v: GoGrammar.Variable): Except String (TestSuiteLib.Pred Int64) :=
  match v.Typ with
  | GoGrammar.Typ.single_int => return TestSuiteLib.Pred.int_var
  | _ => throw s!"expected variable to be Int64 {repr v}"

def Variable.toPredString (v: GoGrammar.Variable): Except String (TestSuiteLib.Pred String) :=
  match v.Typ with
  | GoGrammar.Typ.single_string => return TestSuiteLib.Pred.string_var
  | GoGrammar.Typ.single_tag => return TestSuiteLib.Pred.tag_var
  | _ => throw s!"expected variable to be String {repr v}"

def Variable.toPredUInt64 (v: GoGrammar.Variable): Except String (TestSuiteLib.Pred UInt64) :=
  match v.Typ with
  | GoGrammar.Typ.single_uint => return TestSuiteLib.Pred.uint_var
  | _ => throw s!"expected variable to be UInt64 {repr v}"

def Terminal.toPredBool (t: GoGrammar.Terminal): Except String (TestSuiteLib.Pred Bool) :=
  match t.BoolValue with
  | some b => return TestSuiteLib.Pred.bool_const b
  | none =>
  match t.Variable with
  | some v => Variable.toPredBool v
  | none =>
  throw s!"expected terminal of type Bool {repr t}"

def Terminal.toPredBytes (t: GoGrammar.Terminal): Except String (TestSuiteLib.Pred Bytes) :=
  match t.BytesValue with
  | some b => return TestSuiteLib.Pred.bytes_const b
  | none =>
  match t.Variable with
  | some v => Variable.toPredBytes v
  | none =>
  throw s!"expected terminal of type Bytes {repr t}"

def Terminal.toPredFloat64Bits (t: GoGrammar.Terminal): Except String (TestSuiteLib.Pred Float64Bits) :=
  match t.DoubleValue with
  | some d => return TestSuiteLib.Pred.double_const d
  | none =>
  match t.Variable with
  | some v => Variable.toPredFloat64Bits v
  | none =>
  throw s!"expected terminal of type Float64Bits {repr t}"

def Terminal.toPredInt64 (t: GoGrammar.Terminal): Except String (TestSuiteLib.Pred Int64) :=
  match t.IntValue with
  | some i => return TestSuiteLib.Pred.int_const i
  | none =>
  match t.Variable with
  | some v => Variable.toPredInt64 v
  | none =>
  throw s!"expected terminal of type Int64 {repr t}"

def Terminal.toPredUInt64 (t: GoGrammar.Terminal): Except String (TestSuiteLib.Pred UInt64) :=
  match t.UintValue with
  | some u => return TestSuiteLib.Pred.uint_const u
  | none =>
  match t.Variable with
  | some v => Variable.toPredUInt64 v
  | none =>
  throw s!"expected terminal of type UInt64 {repr t}"

def Terminal.toPredString (t: GoGrammar.Terminal): Except String (TestSuiteLib.Pred String) :=
  match t.StringValue with
  | some s => return TestSuiteLib.Pred.string_const s
  | none =>
  match t.TagValue with
  | some b => return TestSuiteLib.Pred.string_const b
  | none =>
  throw s!"expected terminal of type String {repr t}"

-- inductive Expr where
--   | Terminal (RightArrow: Option Keyword) (Comma: Option Keyword) (Terminal: Terminal)
--   | List (RightArrow: Option Keyword) (Comma: Option Keyword) (Before: Option Space) (Typ: Typ) (OpenCurly: Keyword) (Params: List Expr) (CloseCurly: Keyword)
--   | Function (RightArrow: Option Keyword) (Comma: Option Keyword) (Before: Option Space) (Name: String) (OpenParen: Keyword) (Params: List Expr) (CloseParen: Keyword)
--   | BuiltIn (RightArrow: Option Keyword) (Comma: Option Keyword) (Symbol: Keyword) (Expr: Expr)
--   deriving Repr

def Terminal.whichType (t: GoGrammar.Terminal): GoGrammar.Typ :=
  match t.BoolValue with
  | some _ => GoGrammar.Typ.single_bool
  | none =>
  match t.BytesValue with
  | some _ => GoGrammar.Typ.single_bytes
  | none =>
  match t.DoubleValue with
  | some _ => GoGrammar.Typ.single_double
  | none =>
  match t.IntValue with
  | some _ => GoGrammar.Typ.single_int
  | none =>
  match t.StringValue with
  | some _ => GoGrammar.Typ.single_string
  | none =>
  match t.UintValue with
  | some _ => GoGrammar.Typ.single_uint
  | none =>
  match t.TagValue with
  | some _ => GoGrammar.Typ.single_tag
  | none =>
  match t.Variable with
  | some v => v.Typ
  | none => GoGrammar.Typ.unknown

def builtInToFunctionName (s: String): Except String String :=
  match s with
  | "==" => return "eq"
  | "!=" => return "ne"
  | "<" => return "lt"
  | ">" => return "gt"
  | "<=" => return "le"
  | ">=" => return "ge"
  | "::" => return "type"
  | _ => throw s!"unknown builtin function {s}"

def singleType.fromListType (t: GoGrammar.Typ): GoGrammar.Typ :=
  match t with
  | GoGrammar.Typ.list_bool => GoGrammar.Typ.single_bool
  | GoGrammar.Typ.list_bytes => GoGrammar.Typ.single_bytes
  | GoGrammar.Typ.list_double => GoGrammar.Typ.single_double
  | GoGrammar.Typ.list_int => GoGrammar.Typ.single_int
  | GoGrammar.Typ.list_string => GoGrammar.Typ.single_string
  | GoGrammar.Typ.list_uint => GoGrammar.Typ.single_uint
  | _ => GoGrammar.Typ.unknown

def Terminals.toBools (es: List GoGrammar.Expr): Except String (List Bool) :=
  match es with
  | [] => return []
  | (e::es') =>
    match e with
    | GoGrammar.Expr.Terminal _ _ t =>
      match t.BoolValue with
      | some v =>
        (v :: ·) <$> Terminals.toBools es'
      | none =>
        throw "not all bools"
    | _ =>
      throw "not all terminals"

def Terminals.toBytess (es: List GoGrammar.Expr): Except String (List Bytes) :=
  match es with
  | [] => return []
  | (e::es') =>
    match e with
    | GoGrammar.Expr.Terminal _ _ t =>
      match t.BytesValue with
      | some v =>
        (v :: ·) <$> Terminals.toBytess es'
      | none =>
        throw "not all bytes"
    | _ =>
      throw "not all terminals"

def Terminals.toFloat64Bitss (es: List GoGrammar.Expr): Except String (List Float64Bits) :=
  match es with
  | [] => return []
  | (e::es') =>
    match e with
    | GoGrammar.Expr.Terminal _ _ t =>
      match t.DoubleValue with
      | some v =>
        (v :: ·) <$> Terminals.toFloat64Bitss es'
      | none =>
        throw "not all bytes"
    | _ =>
      throw "not all terminals"

def Terminals.toInt64s (es: List GoGrammar.Expr): Except String (List Int64) :=
  match es with
  | [] => return []
  | (e::es') =>
    match e with
    | GoGrammar.Expr.Terminal _ _ t =>
      match t.IntValue with
      | some v =>
        (v :: ·) <$> Terminals.toInt64s es'
      | none =>
        throw "not all bytes"
    | _ =>
      throw "not all terminals"

def Terminals.toStrings (es: List GoGrammar.Expr): Except String (List String) :=
  match es with
  | [] => return []
  | (e::es') =>
    match e with
    | GoGrammar.Expr.Terminal _ _ t =>
      match t.StringValue with
      | some v =>
        (v :: ·) <$> Terminals.toStrings es'
      | none =>
        throw "not all strings"
    | _ =>
      throw "not all terminals"

def Terminals.toUInt64s (es: List GoGrammar.Expr): Except String (List UInt64) :=
  match es with
  | [] => return []
  | (e::es') =>
    match e with
    | GoGrammar.Expr.Terminal _ _ t =>
      match t.UintValue with
      | some v =>
        (v :: ·) <$> Terminals.toUInt64s es'
      | none =>
        throw "not all uint"
    | _ =>
      throw "not all terminals"

mutual
def Expr.whichType (e: GoGrammar.Expr): GoGrammar.Typ :=
  match e with
  | GoGrammar.Expr.Terminal _ _ t => Terminal.whichType t
  | GoGrammar.Expr.List _ _ _ typ _ _ _ => typ
  | GoGrammar.Expr.BuiltIn _ _ _s _e => GoGrammar.Typ.single_bool
  | GoGrammar.Expr.Function _ _ _ name _ params _ => Function.whichType name params
def Function.whichType (name: String) (params: List GoGrammar.Expr): GoGrammar.Typ :=
  match name with
  | "and" => GoGrammar.Typ.single_bool
  | "or" => GoGrammar.Typ.single_bool
  | "xor" => GoGrammar.Typ.single_bool
  | "not" => GoGrammar.Typ.single_bool
  | "contains" => GoGrammar.Typ.single_bool
  | "elem" =>
    match params with
    | [p,_] => singleType.fromListType (Expr.whichType p)
    | _ => GoGrammar.Typ.unknown
  | "eq" => GoGrammar.Typ.single_bool
  | "ne" => GoGrammar.Typ.single_bool
  | "ge" => GoGrammar.Typ.single_bool
  | "gt" => GoGrammar.Typ.single_bool
  | "le" => GoGrammar.Typ.single_bool
  | "lt" => GoGrammar.Typ.single_bool
  | "length" => GoGrammar.Typ.single_int
  | "print" =>
    match params with
    | [p] => Expr.whichType p
    | _ => GoGrammar.Typ.unknown
  | "range" =>
    match params with
    | [p,_,_] => Expr.whichType p
    | _ => GoGrammar.Typ.unknown
  | "type" => GoGrammar.Typ.single_bool
  | "eqFold" => GoGrammar.Typ.single_bool
  | "hasPrefix" => GoGrammar.Typ.single_bool
  | "hasSuffix" => GoGrammar.Typ.single_bool
  | "toLower" => GoGrammar.Typ.single_string
  | "toUpper" => GoGrammar.Typ.single_string
  | "regex" => GoGrammar.Typ.single_bool
  | _ => GoGrammar.Typ.unknown
end

def Variable.fromType (t: GoGrammar.Typ): Except String GoGrammar.Expr :=
  return GoGrammar.Expr.Terminal none none (GoGrammar.Terminal.mk (Variable := GoGrammar.Variable.mk t) none none none none none none none none)

mutual
partial def Expr.toPredBool (e: GoGrammar.Expr): Except String (TestSuiteLib.Pred Bool) :=
  match e with
  | GoGrammar.Expr.Terminal _ _ t => Terminal.toPredBool t
  | GoGrammar.Expr.BuiltIn _ _ s e => do
    let name <- builtInToFunctionName s.Value
    let typ := whichType e
    let var <- Variable.fromType typ
    Expr.toPredBool (GoGrammar.Expr.Function (Name := name) (Params := [var, e]) none none none (GoGrammar.Keyword.mk none "") (GoGrammar.Keyword.mk none ""))
  | GoGrammar.Expr.Function _ _ _ name _ params _ =>
    match name with
    | "and" =>
      Pred.and <$> (Expr.toPredBool =<< List.get? params 0) <*> (Expr.toPredBool =<< List.get? params 1)
    | "or" =>
      Pred.or <$> (Expr.toPredBool =<< List.get? params 0) <*> (Expr.toPredBool =<< List.get? params 1)
    | "xor" =>
      Pred.xor <$> (Expr.toPredBool =<< List.get? params 0) <*> (Expr.toPredBool =<< List.get? params 1)
    | "not" =>
      Pred.not <$> (Expr.toPredBool =<< List.get? params 0)
    | "contains" => do
      -- func contains(int,const []int) bool
      -- func contains(string,const []string) bool
      -- func contains(string,string) bool
      -- func contains(uint,const []uint) bool
      let p <- List.get? params 0
      let ps <- List.get? params 1
      match Expr.whichType ps with
      | GoGrammar.Typ.list_int =>
        Pred.contains_ints <$> Expr.toPredInt64 p <*> Expr.toPredInt64s ps
      | GoGrammar.Typ.list_string =>
        Pred.contains_strings <$> Expr.toPredString p <*> Expr.toPredStrings ps
      | GoGrammar.Typ.single_string =>
        Pred.contains_string <$> Expr.toPredString p <*> Expr.toPredString ps
      | GoGrammar.Typ.list_uint =>
        Pred.contains_uints <$> Expr.toPredUInt64 p <*> Expr.toPredUInt64s ps
      | _ => throw s!"unsupported second type for contains {repr e}"
    | "elem" => do
      let ps <- List.get? params 0
      match Expr.whichType ps with
      | GoGrammar.Typ.list_bool =>
        Pred.elem_bools <$> Expr.toPredBools ps <*> (Expr.toPredInt64 =<< List.get? params 1)
      | _ => throw s!"elem expected Bools {repr e}"
    | "eq" => do
      let p1 <- List.get? params 0
      let p2 <- List.get? params 1
      match Expr.whichType p1 with
      | GoGrammar.Typ.single_bool =>
        Pred.eq_bool <$> Expr.toPredBool p1 <*> Expr.toPredBool p2
      | GoGrammar.Typ.single_bytes =>
        Pred.eq_bytes <$> Expr.toPredBytes p1 <*> Expr.toPredBytes p2
      | GoGrammar.Typ.single_double =>
        Pred.eq_double <$> Expr.toPredFloat64Bits p1 <*> Expr.toPredFloat64Bits p2
      | GoGrammar.Typ.single_int =>
        Pred.eq_int <$> Expr.toPredInt64 p1 <*> Expr.toPredInt64 p2
      | GoGrammar.Typ.single_string =>
        Pred.eq_string <$> Expr.toPredString p1 <*> Expr.toPredString p2
      | GoGrammar.Typ.single_uint =>
        Pred.eq_uint <$> Expr.toPredUInt64 p1 <*> Expr.toPredUInt64 p2
      | _ => throw s!"unsupported type {repr e}"
    | "ne" => do
      let p1 <- List.get? params 0
      let p2 <- List.get? params 1
      match Expr.whichType p1 with
      | GoGrammar.Typ.single_bool =>
        Pred.ne_bool <$> Expr.toPredBool p1 <*> Expr.toPredBool p2
      | GoGrammar.Typ.single_bytes =>
        Pred.ne_bytes <$> Expr.toPredBytes p1 <*> Expr.toPredBytes p2
      | GoGrammar.Typ.single_double =>
        Pred.ne_double <$> Expr.toPredFloat64Bits p1 <*> Expr.toPredFloat64Bits p2
      | GoGrammar.Typ.single_int =>
        Pred.ne_int <$> Expr.toPredInt64 p1 <*> Expr.toPredInt64 p2
      | GoGrammar.Typ.single_string =>
        Pred.ne_string <$> Expr.toPredString p1 <*> Expr.toPredString p2
      | GoGrammar.Typ.single_uint =>
        Pred.ne_uint <$> Expr.toPredUInt64 p1 <*> Expr.toPredUInt64 p2
      | _ => throw s!"unsupported type {repr e}"
    | "ge" => do
      let p1 <- List.get? params 0
      let p2 <- List.get? params 1
      match Expr.whichType p1 with
      | GoGrammar.Typ.single_bytes =>
        Pred.ge_bytes <$> Expr.toPredBytes p1 <*> Expr.toPredBytes p2
      | GoGrammar.Typ.single_double =>
        Pred.ge_double <$> Expr.toPredFloat64Bits p1 <*> Expr.toPredFloat64Bits p2
      | GoGrammar.Typ.single_int =>
        Pred.ge_int <$> Expr.toPredInt64 p1 <*> Expr.toPredInt64 p2
      | GoGrammar.Typ.single_string =>
        Pred.ge_string <$> Expr.toPredString p1 <*> Expr.toPredString p2
      | GoGrammar.Typ.single_uint =>
        Pred.ge_uint <$> Expr.toPredUInt64 p1 <*> Expr.toPredUInt64 p2
      | _ => throw s!"unsupported type {repr e}"
    | "gt" => do
      let p1 <- List.get? params 0
      let p2 <- List.get? params 1
      match Expr.whichType p1 with
      | GoGrammar.Typ.single_bytes =>
        Pred.gt_bytes <$> Expr.toPredBytes p1 <*> Expr.toPredBytes p2
      | GoGrammar.Typ.single_double =>
        Pred.gt_double <$> Expr.toPredFloat64Bits p1 <*> Expr.toPredFloat64Bits p2
      | GoGrammar.Typ.single_int =>
        Pred.gt_int <$> Expr.toPredInt64 p1 <*> Expr.toPredInt64 p2
      | GoGrammar.Typ.single_string =>
        Pred.gt_string <$> Expr.toPredString p1 <*> Expr.toPredString p2
      | GoGrammar.Typ.single_uint =>
        Pred.gt_uint <$> Expr.toPredUInt64 p1 <*> Expr.toPredUInt64 p2
      | _ => throw s!"unsupported type {repr e}"
    | "le" => do
      let p1 <- List.get? params 0
      let p2 <- List.get? params 1
      match Expr.whichType p1 with
      | GoGrammar.Typ.single_bytes =>
        Pred.le_bytes <$> Expr.toPredBytes p1 <*> Expr.toPredBytes p2
      | GoGrammar.Typ.single_double =>
        Pred.le_double <$> Expr.toPredFloat64Bits p1 <*> Expr.toPredFloat64Bits p2
      | GoGrammar.Typ.single_int =>
        Pred.le_int <$> Expr.toPredInt64 p1 <*> Expr.toPredInt64 p2
      | GoGrammar.Typ.single_string =>
        Pred.le_string <$> Expr.toPredString p1 <*> Expr.toPredString p2
      | GoGrammar.Typ.single_uint =>
        Pred.le_uint <$> Expr.toPredUInt64 p1 <*> Expr.toPredUInt64 p2
      | _ => throw s!"unsupported type {repr e}"
    | "lt" => do
      let p1 <- List.get? params 0
      let p2 <- List.get? params 1
      match Expr.whichType p1 with
      | GoGrammar.Typ.single_bytes =>
        Pred.lt_bytes <$> Expr.toPredBytes p1 <*> Expr.toPredBytes p2
      | GoGrammar.Typ.single_double =>
        Pred.lt_double <$> Expr.toPredFloat64Bits p1 <*> Expr.toPredFloat64Bits p2
      | GoGrammar.Typ.single_int =>
        Pred.lt_int <$> Expr.toPredInt64 p1 <*> Expr.toPredInt64 p2
      | GoGrammar.Typ.single_string =>
        Pred.lt_string <$> Expr.toPredString p1 <*> Expr.toPredString p2
      | GoGrammar.Typ.single_uint =>
        Pred.lt_uint <$> Expr.toPredUInt64 p1 <*> Expr.toPredUInt64 p2
      | _ => throw s!"unsupported type {repr e}"
    | "print" => do
      let p <- List.get? params 0
      match Expr.whichType p with
      | GoGrammar.Typ.single_bool => Pred.print_bool <$> Expr.toPredBool p
      -- | GoGrammar.Typ.list_bool => Pred.print_bools =<< Expr.toPredBools p
      -- | GoGrammar.Typ.list_bytes => Pred.print_bytess =<< Expr.toPredBytess p
      -- | GoGrammar.Typ.list_double => Pred.print_doubles =<< Expr.toPredFloat64Bitss p
      -- | GoGrammar.Typ.list_int => Pred.print_ints =<< Expr.toPredInt64s p
      -- | GoGrammar.Typ.list_string => Pred.print_strings =<< Expr.toPredStrings p
      -- | GoGrammar.Typ.list_uint => Pred.print_uints =<< Expr.toPredUInt64s p
      | _ => throw s!"unsupported type {repr e}"
  -- func range([][]byte,int,int) [][]byte
  -- func range([]bool,int,int) []bool
  -- func range([]double,int,int) []double
  -- func range([]int,int,int) []int
  -- func range([]string,int,int) []string
  -- func range([]uint,int,int) []uint
    -- | "range" => do
    --   let ps <- List.get? params 0
    --   let a <- List.get? params 1
    --   let b <- List.get? params 2
    --   match Expr.whichType ps with
    --   | GoGrammar.Typ.list_bool => Pred.range_bools <$> Expr.toPredBools ps <*> Expr.toPredInt64 a <*> Expr.toPredInt64 b
    --   | GoGrammar.Typ.list_bytes => Pred.range_bytes <$> Expr.toPredBytess ps <*> Expr.toPredInt64 a <*> Expr.toPredInt64 b
    --   | GoGrammar.Typ.list_double => Pred.range_doubles <$> Expr.toPredFloat64Bitss ps <*> Expr.toPredInt64 a <*> Expr.toPredInt64 b
    --   | GoGrammar.Typ.list_int => Pred.range_ints <$> Expr.toPredInt64s ps <*> Expr.toPredInt64 a <*> Expr.toPredInt64 b
    --   | GoGrammar.Typ.list_string => Pred.range_strings <$> Expr.toPredStrings ps <*> Expr.toPredInt64 a <*> Expr.toPredInt64 b
    --   | GoGrammar.Typ.list_uint => Pred.range_uints <$> Expr.toPredUInt64s ps <*> Expr.toPredInt64 a <*> Expr.toPredInt64 b
    --   | _ => throw s!"range unsupported type {repr e}"
    | "type" => do
      let p <- List.get? params 0
      match Expr.whichType p with
      | GoGrammar.Typ.single_bool => Pred.type_bool <$> Expr.toPredBool p
      | GoGrammar.Typ.single_bytes => Pred.type_bytes <$> Expr.toPredBytes p
      | GoGrammar.Typ.single_double => Pred.type_double <$> Expr.toPredFloat64Bits p
      | GoGrammar.Typ.single_int => Pred.type_int <$> Expr.toPredInt64 p
      | GoGrammar.Typ.single_string => Pred.type_string <$> Expr.toPredString p
      | GoGrammar.Typ.single_uint => Pred.type_uint <$> Expr.toPredUInt64 p
      | _ => throw s!"type unsupported type {repr e}"
    | "eqFold" => Pred.eqfold <$> (Expr.toPredString =<< List.get? params 0) <*> (Expr.toPredString =<< List.get? params 1)
    | "hasPrefix" => Pred.hasPrefix <$> (Expr.toPredString =<< List.get? params 0) <*> (Expr.toPredString =<< List.get? params 1)
    | "hasSuffix" => Pred.hasSuffix <$> (Expr.toPredString =<< List.get? params 0) <*> (Expr.toPredString =<< List.get? params 1)
    | "regex" => Pred.regex <$> (Expr.toPredString =<< List.get? params 0) <*> (Expr.toPredString =<< List.get? params 1)
    | _ => throw s!"expected bool function {repr e}"
  | _ => throw s!"expected expr of type bool {repr e}"
partial def Expr.toPredBytes (e: GoGrammar.Expr): Except String (TestSuiteLib.Pred Bytes) :=
  match e with
  | GoGrammar.Expr.Terminal _ _ t => Terminal.toPredBytes t
  | GoGrammar.Expr.BuiltIn _ _ s e => do
    let name <- builtInToFunctionName s.Value
    let typ := whichType e
    let var <- Variable.fromType typ
    Expr.toPredBytes (GoGrammar.Expr.Function (Name := name) (Params := [var, e]) none none none (GoGrammar.Keyword.mk none "") (GoGrammar.Keyword.mk none ""))
  | GoGrammar.Expr.Function _ _ _ name _ params _ =>
    match name with
    | "elem" => do
      let ps <- List.get? params 0
      match Expr.whichType ps with
      | GoGrammar.Typ.list_bytes =>
        Pred.elem_bytes <$> Expr.toPredBytess ps <*> (Expr.toPredInt64 =<< List.get? params 1)
      | _ => throw s!"elem expected Bools {repr e}"
    | "print" => do
      let p <- List.get? params 0
      match Expr.whichType p with
      | GoGrammar.Typ.single_bytes => Pred.print_bytes <$> Expr.toPredBytes p
      | _ => throw s!"unsupported type {repr e}"
    | _ => throw s!"expected bytes function {repr e}"
  | _ => throw s!"expected expr of type bytes {repr e}"
partial def Expr.toPredFloat64Bits (e: GoGrammar.Expr): Except String (TestSuiteLib.Pred Float64Bits) :=
  match e with
  | GoGrammar.Expr.Terminal _ _ t => Terminal.toPredFloat64Bits t
  | GoGrammar.Expr.BuiltIn _ _ s e => do
    let name <- builtInToFunctionName s.Value
    let typ := whichType e
    let var <- Variable.fromType typ
    Expr.toPredFloat64Bits (GoGrammar.Expr.Function (Name := name) (Params := [var, e]) none none none (GoGrammar.Keyword.mk none "") (GoGrammar.Keyword.mk none ""))
  | GoGrammar.Expr.Function _ _ _ name _ params _ =>
    match name with
    | "elem" => do
      let ps <- List.get? params 0
      match Expr.whichType ps with
      | GoGrammar.Typ.list_double =>
        Pred.elem_doubles <$> Expr.toPredFloat64Bitss ps <*> (Expr.toPredInt64 =<< List.get? params 1)
      | _ => throw s!"elem expected Bools {repr e}"
    | "print" => do
      let p <- List.get? params 0
      match Expr.whichType p with
      | GoGrammar.Typ.single_double => Pred.print_double <$> Expr.toPredFloat64Bits p
      | _ => throw s!"unsupported type {repr e}"
    | _ => throw s!"expected double function {repr e}"
  | _ => throw s!"expected expr of type double {repr e}"
partial def Expr.toPredInt64 (e: GoGrammar.Expr): Except String (TestSuiteLib.Pred Int64) :=
  match e with
  | GoGrammar.Expr.Terminal _ _ t => Terminal.toPredInt64 t
  | GoGrammar.Expr.BuiltIn _ _ s e => do
    let name <- builtInToFunctionName s.Value
    let typ := whichType e
    let var <- Variable.fromType typ
    Expr.toPredInt64 (GoGrammar.Expr.Function (Name := name) (Params := [var, e]) none none none (GoGrammar.Keyword.mk none "") (GoGrammar.Keyword.mk none ""))
  | GoGrammar.Expr.Function _ _ _ name _ params _ =>
    match name with
    | "elem" => do
      let ps <- List.get? params 0
      match Expr.whichType ps with
      | GoGrammar.Typ.list_int =>
        Pred.elem_ints <$> Expr.toPredInt64s ps <*> (Expr.toPredInt64 =<< List.get? params 1)
      | _ => throw s!"elem expected Bools {repr e}"
    | "print" => do
      let p <- List.get? params 0
      match Expr.whichType p with
      | GoGrammar.Typ.single_int => Pred.print_int <$> Expr.toPredInt64 p
      | _ => throw s!"unsupported type {repr e}"
    | "length" => do
      let p <- List.get? params 0
      match Expr.whichType p with
      | GoGrammar.Typ.list_bool => Pred.length_bools <$> Expr.toPredBools p
      | GoGrammar.Typ.list_bytes => Pred.length_bytess <$> Expr.toPredBytess p
      | GoGrammar.Typ.list_double => Pred.length_doubles <$> Expr.toPredFloat64Bitss p
      | GoGrammar.Typ.list_int => Pred.length_ints <$> Expr.toPredInt64s p
      | GoGrammar.Typ.list_string => Pred.length_strings <$> Expr.toPredStrings p
      | GoGrammar.Typ.list_uint => Pred.length_uints <$> Expr.toPredUInt64s p
      | _ => throw s!"unsupported type {repr e}"
    | _ => throw s!"expected int function {repr e}"
  | _ => throw s!"expected expr of type int {repr e}"
partial def Expr.toPredString (e: GoGrammar.Expr): Except String (TestSuiteLib.Pred String) :=
  match e with
  | GoGrammar.Expr.Terminal _ _ t => Terminal.toPredString t
  | GoGrammar.Expr.BuiltIn _ _ s e => do
    let name <- builtInToFunctionName s.Value
    let typ := whichType e
    let var <- Variable.fromType typ
    Expr.toPredString (GoGrammar.Expr.Function (Name := name) (Params := [var, e]) none none none (GoGrammar.Keyword.mk none "") (GoGrammar.Keyword.mk none ""))
  | GoGrammar.Expr.Function _ _ _ name _ params _ =>
    match name with
    | "elem" => do
      let ps <- List.get? params 0
      match Expr.whichType ps with
      | GoGrammar.Typ.list_string =>
        Pred.elem_strings <$> Expr.toPredStrings ps <*> (Expr.toPredInt64 =<< List.get? params 1)
      | _ => throw s!"elem expected Bools {repr e}"
    | "print" => do
      let p <- List.get? params 0
      match Expr.whichType p with
      | GoGrammar.Typ.single_string => Pred.print_string <$> Expr.toPredString p
      | _ => throw s!"unsupported type {repr e}"
    | "toLower" => do
      let p <- List.get? params 0
      TestSuiteLib.Pred.toLower <$> Expr.toPredString p
    | "toUpper" => do
      let p <- List.get? params 0
      TestSuiteLib.Pred.toUpper <$> Expr.toPredString p
    | _ => throw s!"expected string function {repr e}"
  | _ => throw s!"expected expr of type string {repr e}"
partial def Expr.toPredUInt64 (e: GoGrammar.Expr): Except String (TestSuiteLib.Pred UInt64) :=
  match e with
  | GoGrammar.Expr.Terminal _ _ t => Terminal.toPredUInt64 t
  | GoGrammar.Expr.BuiltIn _ _ s e => do
    let name <- builtInToFunctionName s.Value
    let typ := whichType e
    let var <- Variable.fromType typ
    Expr.toPredUInt64 (GoGrammar.Expr.Function (Name := name) (Params := [var, e]) none none none (GoGrammar.Keyword.mk none "") (GoGrammar.Keyword.mk none ""))
  | GoGrammar.Expr.Function _ _ _ name _ params _ =>
    match name with
    | "elem" => do
      let ps <- List.get? params 0
      match Expr.whichType ps with
      | GoGrammar.Typ.list_uint =>
        Pred.elem_uints <$> Expr.toPredUInt64s ps <*> (Expr.toPredInt64 =<< List.get? params 1)
      | _ => throw s!"elem expected Bools {repr e}"
    | "print" => do
      let p <- List.get? params 0
      match Expr.whichType p with
      | GoGrammar.Typ.single_uint => Pred.print_uint <$> Expr.toPredUInt64 p
      | _ => throw s!"unsupported type {repr e}"
    | _ => throw s!"expected uint function {repr e}"
  | _ => throw s!"expected expr of type uint {repr e}"
partial def Expr.toPredBools (e: GoGrammar.Expr): Except String (TestSuiteLib.Pred (List Bool)) :=
  match e with
  | GoGrammar.Expr.List _ _ _ typ _ elems _ =>
    match typ with
    | GoGrammar.Typ.list_bool => do
      let bools <- Terminals.toBools elems
      return TestSuiteLib.Pred.bools_const bools
    | _ => throw s!"expected bools list {repr e}"
  | GoGrammar.Expr.Function _ _ _ name _ params _ =>
    match name with
    | "range" => do
      let ps <- List.get? params 0
      let a <- List.get? params 1
      let b <- List.get? params 2
      match Expr.whichType ps with
      | GoGrammar.Typ.list_bool =>
        TestSuiteLib.Pred.range_bools <$> Expr.toPredBools ps <*> Expr.toPredInt64 a <*> Expr.toPredInt64 b
      | _ => throw s!"unsupported type {repr e}"
    | "print" => do
      let ps <- List.get? params 0
      match Expr.whichType ps with
      | GoGrammar.Typ.list_bool => Pred.print_bools <$> Expr.toPredBools ps
      | _ => throw s!"unsupported type {repr e}"
    | _ => throw s!"expected bools function {repr e}"
  | _ => throw s!"expected expr of type bools {repr e}"
partial def Expr.toPredBytess (e: GoGrammar.Expr): Except String (TestSuiteLib.Pred (List Bytes)) :=
  match e with
  | GoGrammar.Expr.List _ _ _ typ _ elems _ =>
    match typ with
    | GoGrammar.Typ.list_bytes => do
      let bytess <- Terminals.toBytess elems
      return TestSuiteLib.Pred.bytess_const bytess
    | _ => throw s!"expected bytess list {repr e}"
  | GoGrammar.Expr.Function _ _ _ name _ params _ =>
    match name with
    | "range" => do
      let ps <- List.get? params 0
      let a <- List.get? params 1
      let b <- List.get? params 2
      match Expr.whichType ps with
      | GoGrammar.Typ.list_bytes =>
        TestSuiteLib.Pred.range_bytes <$> Expr.toPredBytess ps <*> Expr.toPredInt64 a <*> Expr.toPredInt64 b
      | _ => throw s!"unsupported type {repr e}"
    | "print" => do
      let ps <- List.get? params 0
      match Expr.whichType ps with
      | GoGrammar.Typ.list_bytes => Pred.print_bytess <$> Expr.toPredBytess ps
      | _ => throw s!"unsupported type {repr e}"
    | _ => throw s!"expected bytess function {repr e}"
  | _ => throw s!"expected expr of type bytess {repr e}"
partial def Expr.toPredFloat64Bitss (e: GoGrammar.Expr): Except String (TestSuiteLib.Pred (List Float64Bits)) :=
  match e with
  | GoGrammar.Expr.List _ _ _ typ _ elems _ =>
    match typ with
    | GoGrammar.Typ.list_double => do
      let doubles <- Terminals.toFloat64Bitss elems
      return TestSuiteLib.Pred.doubles_const doubles
    | _ => throw s!"expected doubles list {repr e}"
  | GoGrammar.Expr.Function _ _ _ name _ params _ =>
    match name with
    | "range" => do
      let ps <- List.get? params 0
      let a <- List.get? params 1
      let b <- List.get? params 2
      match Expr.whichType ps with
      | GoGrammar.Typ.list_double =>
        TestSuiteLib.Pred.range_doubles <$> Expr.toPredFloat64Bitss ps <*> Expr.toPredInt64 a <*> Expr.toPredInt64 b
      | _ => throw s!"unsupported type {repr e}"
    | "print" => do
      let ps <- List.get? params 0
      match Expr.whichType ps with
      | GoGrammar.Typ.list_double => Pred.print_doubles <$> Expr.toPredFloat64Bitss ps
      | _ => throw s!"unsupported type {repr e}"
    | _ => throw s!"expected doubles function {repr e}"
  | _ => throw s!"expected expr of type doubles {repr e}"
partial def Expr.toPredInt64s (e: GoGrammar.Expr): Except String (TestSuiteLib.Pred (List Int64)) :=
  match e with
  | GoGrammar.Expr.List _ _ _ typ _ elems _ =>
    match typ with
    | GoGrammar.Typ.list_int => do
      let ints <- Terminals.toInt64s elems
      return TestSuiteLib.Pred.ints_const ints
    | _ => throw s!"expected ints list {repr e}"
  | GoGrammar.Expr.Function _ _ _ name _ params _ =>
    match name with
    | "range" => do
      let ps <- List.get? params 0
      let a <- List.get? params 1
      let b <- List.get? params 2
      match Expr.whichType ps with
      | GoGrammar.Typ.list_int =>
        TestSuiteLib.Pred.range_ints <$> Expr.toPredInt64s ps <*> Expr.toPredInt64 a <*> Expr.toPredInt64 b
      | _ => throw s!"unsupported type {repr e}"
    | "print" => do
      let ps <- List.get? params 0
      match Expr.whichType ps with
      | GoGrammar.Typ.list_int => Pred.print_ints <$> Expr.toPredInt64s ps
      | _ => throw s!"unsupported type {repr e}"
    | _ => throw s!"expected ints function {repr e}"
  | _ => throw s!"expected expr of type ints {repr e}"
partial def Expr.toPredStrings (e: GoGrammar.Expr): Except String (TestSuiteLib.Pred (List String)) :=
  match e with
  | GoGrammar.Expr.List _ _ _ typ _ elems _ =>
    match typ with
    | GoGrammar.Typ.list_string => do
      let strings <- Terminals.toStrings elems
      return TestSuiteLib.Pred.strings_const strings
    | _ => throw s!"expected strings list {repr e}"
  | GoGrammar.Expr.Function _ _ _ name _ params _ =>
    match name with
    | "range" => do
      let ps <- List.get? params 0
      let a <- List.get? params 1
      let b <- List.get? params 2
      match Expr.whichType ps with
      | GoGrammar.Typ.list_string =>
        TestSuiteLib.Pred.range_strings <$> Expr.toPredStrings ps <*> Expr.toPredInt64 a <*> Expr.toPredInt64 b
      | _ => throw s!"unsupported type {repr e}"
    | "print" => do
      let ps <- List.get? params 0
      match Expr.whichType ps with
      | GoGrammar.Typ.list_string => Pred.print_strings <$> Expr.toPredStrings ps
      | _ => throw s!"unsupported type {repr e}"
    | _ => throw s!"expected strings function {repr e}"
  | _ => throw s!"expected expr of type strings {repr e}"
partial def Expr.toPredUInt64s (e: GoGrammar.Expr): Except String (TestSuiteLib.Pred (List UInt64)) :=
  match e with
  | GoGrammar.Expr.List _ _ _ typ _ elems _ =>
    match typ with
    | GoGrammar.Typ.list_uint => do
      let uints <- Terminals.toUInt64s elems
      return TestSuiteLib.Pred.uints_const uints
    | _ => throw s!"expected uints list {repr e}"
  | GoGrammar.Expr.Function _ _ _ name _ params _ =>
    match name with
    | "range" => do
      let ps <- List.get? params 0
      let a <- List.get? params 1
      let b <- List.get? params 2
      match Expr.whichType ps with
      | GoGrammar.Typ.list_uint =>
        TestSuiteLib.Pred.range_uints <$> Expr.toPredUInt64s ps <*> Expr.toPredInt64 a <*> Expr.toPredInt64 b
      | _ => throw s!"unsupported type {repr e}"
    | "print" => do
      let ps <- List.get? params 0
      match Expr.whichType ps with
      | GoGrammar.Typ.list_uint => Pred.print_uints <$> Expr.toPredUInt64s ps
      | _ => throw s!"unsupported type {repr e}"
    | _ => throw s!"expected uints function {repr e}"
  | _ => throw s!"expected expr of type uints {repr e}"
end

def EmptyNode.toRule (_: GoGrammar.EmptyNode): Except String Rule :=
  return Regex.emptystr

def ZAny.toRule (_: GoGrammar.ZAny): Except String Rule :=
  return Regex.compliment (Regex.emptyset)

-- The assumption is that Ref 0 is always the emptystr regex.
def LeafNode.toRule (l: GoGrammar.LeafNode): Except String Rule :=
  Regex.symbol <$> (·,0) <$> Expr.toPredBool l.Expr

-- structure Reference where
--   At: Keyword
--   Name: String
--   deriving Repr, DecidableEq, FromJson
-- inductive Pattern where
--   | Empty (Empty: EmptyNode)
--   | ZAny (ZAny: ZAny)
--   | Reference (Reference: Reference)
--   | LeafNode (LeafNode: LeafNode)
--   | TreeNode (Name: NameExpr) (Colon: Option Keyword) (Pattern: Pattern)
--   | Or (OpenParen: Option Keyword) (LeftPattern: Pattern) (Pipe: Keyword) (RightPattern: Pattern) (OpenParen: Option Keyword)
--   | And (OpenParen: Option Keyword) (LeftPattern: Pattern) (Ampersand: Keyword) (RightPattern: Pattern) (OpenParen: Option Keyword)
--   | Xor (OpenParen: Option Keyword) (LeftPattern: Pattern) (Caret: Keyword) (RightPattern: Pattern) (OpenParen: Option Keyword)
--   | Concat (OpenBracket: Option Keyword) (LeftPattern: Pattern) (Comma: Keyword) (RightPattern: Pattern) (ExtraComma: Option Keyword) (CloseBracket: Option Keyword)
--   | Interleave (OpenCurly: Option Keyword) (LeftPattern: Pattern) (SemiColon: Keyword) (RightPattern: Pattern) (ExtraSemiColon: Option Keyword) (CloseCurly: Option Keyword)
--   | ZeroOrMore (OpenParen: Option Keyword) (Pattern: Pattern) (CloseParen: Option Keyword) (Star: Keyword)
--   | Not (Exclamation: Keyword) (OpenParen: Option Keyword) (Pattern: Pattern) (CloseParen: Option Keyword)
--   | Contains (Dot: Keyword) (Pattern: Pattern)
--   | Optional (OpenParen: Option Keyword) (Pattern: Pattern) (CloseParen: Option Keyword) (QuestionMark: Keyword)
--   deriving Repr

partial def GoPattern.toRule (g: GoGrammarMap) (p: GoGrammar.Pattern) (refn: Nat): Except String Rule :=
  match p with
  | GoGrammar.Pattern.Empty (p: GoGrammar.EmptyNode) =>
    EmptyNode.toRule p
  | GoGrammar.Pattern.ZAny (p: GoGrammar.ZAny) =>
    ZAny.toRule p
  | GoGrammar.Pattern.Reference (r: GoGrammar.Reference) =>
    match g.get? r.Name with
    | none => throw s!"unknown reference {r.Name}"
    | some rp => GoPattern.toRule g rp.1 rp.2
  | GoGrammar.Pattern.LeafNode (p: GoGrammar.LeafNode) =>
    LeafNode.toRule p
  | GoGrammar.Pattern.TreeNode (nam: GoGrammar.NameExpr) (_Colon: Option GoGrammar.Keyword) (_p: GoGrammar.Pattern) => do
    return Regex.symbol (<- NameExpr.toPred nam, refn)
  | GoGrammar.Pattern.Or (_OpenParen: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (_Pipe: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) => do
    let leftn := refn
    let rightn := treecount LeftPattern refn
    let left <- GoPattern.toRule g LeftPattern leftn
    let right <- GoPattern.toRule g RightPattern rightn
    return Regex.or left right
  | GoGrammar.Pattern.And (_OpenParen: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (_Ampersand: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) => do
    let leftn := refn
    let rightn := treecount LeftPattern refn
    let left <- GoPattern.toRule g LeftPattern leftn
    let right <- GoPattern.toRule g RightPattern rightn
    return Regex.and left right
  | GoGrammar.Pattern.Xor (_OpenParen: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (_Caret: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) => do
    let leftn := refn
    let rightn := treecount LeftPattern refn
    let left <- GoPattern.toRule g LeftPattern leftn
    let right <- GoPattern.toRule g RightPattern rightn
    return Regex.xor left right
  | GoGrammar.Pattern.Concat (_OpenBracket: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (_Comma: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (_ExtraComma: Option GoGrammar.Keyword) (_CloseBracket: Option GoGrammar.Keyword) => do
    let leftn := refn
    let rightn := treecount LeftPattern refn
    let left <- GoPattern.toRule g LeftPattern leftn
    let right <- GoPattern.toRule g RightPattern rightn
    return Regex.concat left right
  | GoGrammar.Pattern.Interleave (_OpenCurly: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (_SemiColon: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (_ExtraSemiColon: Option GoGrammar.Keyword) (_CloseCurly: Option GoGrammar.Keyword) => do
    let leftn := refn
    let rightn := treecount LeftPattern refn
    let left <- GoPattern.toRule g LeftPattern leftn
    let right <- GoPattern.toRule g RightPattern rightn
    return Regex.interleave left right
  | GoGrammar.Pattern.ZeroOrMore (_OpenParen: Option GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) (_Star: GoGrammar.Keyword) => do
    let res <- GoPattern.toRule g Pattern refn
    return Regex.star res
  | GoGrammar.Pattern.Not (_Exclamation: GoGrammar.Keyword) (_OpenParen: Option GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) => do
    let res <- GoPattern.toRule g Pattern refn
    return Regex.compliment res
  | GoGrammar.Pattern.Contains (_Dot: GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) => do
    let res <- GoPattern.toRule g Pattern refn
    return Regex.concat Regex.starAny (Regex.concat res Regex.starAny)
  | GoGrammar.Pattern.Optional (_OpenParen: Option GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) (_QuestionMark: GoGrammar.Keyword) => do
    let res <- GoPattern.toRule g Pattern refn
    return Regex.or res Regex.emptystr

def TreeNodes.toRule (g: GoGrammarMap) (p: GoGrammar.Pattern) (refn: Nat) (res: List Rule): Except String (List Rule) :=
  match p with
  | GoGrammar.Pattern.Empty (_Empty: GoGrammar.EmptyNode) =>
    return res
  | GoGrammar.Pattern.ZAny (_ZAny: GoGrammar.ZAny) =>
    return res
  | GoGrammar.Pattern.Reference (_Reference: GoGrammar.Reference) =>
    return res
  | GoGrammar.Pattern.LeafNode (_LeafNode: GoGrammar.LeafNode) =>
    return res
  | GoGrammar.Pattern.TreeNode (_Name: GoGrammar.NameExpr) (_Colon: Option GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) => do
    return (<- GoPattern.toRule g Pattern refn) :: res
  | GoGrammar.Pattern.Or (_OpenParen: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (_Pipe: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) => do
    let leftn := refn
    let leftres := res
    let rightn := treecount LeftPattern refn
    let rightres <- TreeNodes.toRule g LeftPattern leftn leftres
    TreeNodes.toRule g RightPattern rightn rightres
  | GoGrammar.Pattern.And (_OpenParen: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (_Ampersand: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) => do
    let leftn := refn
    let leftres := res
    let rightn := treecount LeftPattern refn
    let rightres <- TreeNodes.toRule g LeftPattern leftn leftres
    TreeNodes.toRule g RightPattern rightn rightres
  | GoGrammar.Pattern.Xor (_OpenParen: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (_Caret: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) => do
    let leftn := refn
    let leftres := res
    let rightn := treecount LeftPattern refn
    let rightres <- TreeNodes.toRule g LeftPattern leftn leftres
    TreeNodes.toRule g RightPattern rightn rightres
  | GoGrammar.Pattern.Concat (_OpenBracket: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (_Comma: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (_ExtraComma: Option GoGrammar.Keyword) (_CloseBracket: Option GoGrammar.Keyword) => do
    let leftn := refn
    let leftres := res
    let rightn := treecount LeftPattern refn
    let rightres <- TreeNodes.toRule g LeftPattern leftn leftres
    TreeNodes.toRule g RightPattern rightn rightres
  | GoGrammar.Pattern.Interleave (_OpenCurly: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (_SemiColon: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (_ExtraSemiColon: Option GoGrammar.Keyword) (_CloseCurly: Option GoGrammar.Keyword) => do
    let leftn := refn
    let leftres := res
    let rightn := treecount LeftPattern refn
    let rightres <- TreeNodes.toRule g LeftPattern leftn leftres
    TreeNodes.toRule g RightPattern rightn rightres
  | GoGrammar.Pattern.ZeroOrMore (_OpenParen: Option GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) (_Star: GoGrammar.Keyword) =>
    TreeNodes.toRule g Pattern refn res
  | GoGrammar.Pattern.Not (_Exclamation: GoGrammar.Keyword) (_OpenParen: Option GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) =>
    TreeNodes.toRule g Pattern refn res
  | GoGrammar.Pattern.Contains (_Dot: GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) =>
    TreeNodes.toRule g Pattern refn res
  | GoGrammar.Pattern.Optional (_OpenParen: Option GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) (_CloseParen: Option GoGrammar.Keyword) (_QuestionMark: GoGrammar.Keyword) =>
    TreeNodes.toRule g Pattern refn res

-- structure PatternDecl where
--   Hash: Keyword
--   Before: Option Space
--   Name: String
--   Eq: Keyword
--   Pattern: Pattern
--   deriving FromJson, Repr

-- structure Grammar where
--   TopPattern: Pattern
--   PatternDecls: Option (List PatternDecl)
--   After: Option Space
--   deriving FromJson, Repr

theorem max_cons
  [Max α]
  [Std.Associative (α := α) Max.max]
  [Std.IdempotentOp (α := α) Max.max]
  {x : α} {xs : List α} {h: x :: xs ≠ []} :
  (x :: xs).max h = max x ((x :: xs).max h) := by
  induction xs with
  | nil =>
    simp only [List.max_singleton]
    rw [Std.max_self]
  | cons x' xs ih =>
    simp only [List.max]
    rw [@List.foldl_cons]
    sorry

def GoGrammar_toRule (g: GoGrammar.Grammar): Except String (Σ n, (Grammar n (TestSuiteLib.Pred Bool))) := do
  let gmap: GoGrammarMap := GoGrammar.mk g
  let startRule: Rule <- GoPattern.toRule gmap g.TopPattern 1
  let mut rules: List Rule := []
  -- emptystr should be in position zero
  rules := Regex.emptystr :: rules
  rules <- TreeNodes.toRule gmap g.TopPattern 1 rules
  let decls := match g.PatternDecls with
    | none => []
    | some decls => decls
  let mut nref := treecount g.TopPattern 1
  for decl in decls do
    rules <- TreeNodes.toRule gmap decl.Pattern nref rules
    nref := treecount decl.Pattern nref
  let prodsList := rules.reverse
  let n: Nat := 1 + List.foldl max (maxRef startRule) (List.map maxRef prodsList)
  let start: Regex (TestSuiteLib.Pred Bool × Ref n) := Rule.toFin startRule n (by
      subst n
      rw [List.foldl_max]
      omega
    )
  return Sigma.mk n <|
    Grammar.mk
    (start := start)
    (prods := sorry)
