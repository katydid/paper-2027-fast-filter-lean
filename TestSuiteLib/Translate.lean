import Mathlib.Tactic.RewriteSearch
import Mathlib.Tactic
import Aesop

import TestSuiteLib.GoGrammar
import TestSuiteLib.Pred
import VerifiedFilter.Grammar
import Std
import Std.Data.HashMap

namespace TestSuiteLib

open VerifiedFilter.Regex

def maxRef (r: Regex (φ × Nat)): Nat :=
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

inductive RefPattern (n: Nat) where
  | Empty
  | ZAny
  | Reference (name: String)
  | LeafNode (expr: GoGrammar.Expr) (ref: Fin n)
  | TreeNode (name: GoGrammar.NameExpr) (ref: Fin n)
  | Or (p1: RefPattern n) (p2: RefPattern n)
  | And (p1: RefPattern n) (p2: RefPattern n)
  | Xor (p1: RefPattern n) (p2: RefPattern n)
  | Concat (p1: RefPattern n) (p2: RefPattern n)
  | Interleave (p1: RefPattern n) (p2: RefPattern n)
  | ZeroOrMore (p: RefPattern n)
  | Not (p: RefPattern n)
  | Contains (p: RefPattern n)
  | Optional (p: RefPattern n)
  deriving Repr, BEq

abbrev RefGrammarMap n := Std.HashMap String (RefPattern n)

def RefPattern.castUp (r: RefPattern n) (m: Nat) (h: n <= m): RefPattern m :=
  match r with
  | Empty =>
    Empty
  | ZAny =>
    ZAny
  | Reference (name: String) =>
    Reference name
  | LeafNode (expr: GoGrammar.Expr) (ref: Fin n) =>
    LeafNode expr (Fin.mk ref.1 (by omega))
  | TreeNode (name: GoGrammar.NameExpr) (ref: Fin n) =>
    TreeNode name (Fin.mk ref.1 (by omega))
  | Or (p1: RefPattern n) (p2: RefPattern n) =>
    Or (p1.castUp m h) (p2.castUp m h)
  | And (p1: RefPattern n) (p2: RefPattern n) =>
    And (p1.castUp m h) (p2.castUp m h)
  | Xor (p1: RefPattern n) (p2: RefPattern n) =>
    Xor (p1.castUp m h) (p2.castUp m h)
  | Concat (p1: RefPattern n) (p2: RefPattern n) =>
    Concat (p1.castUp m h) (p2.castUp m h)
  | Interleave (p1: RefPattern n) (p2: RefPattern n) =>
    Interleave (p1.castUp m h) (p2.castUp m h)
  | ZeroOrMore (p: RefPattern n) =>
    ZeroOrMore (p.castUp m h)
  | Not (p: RefPattern n) =>
    Not (p.castUp m h)
  | Contains (p: RefPattern n) =>
    Contains (p.castUp m h)
  | Optional (p: RefPattern n) =>
    Optional (p.castUp m h)

def mkRefPattern (p: GoGrammar.Pattern) (xs: Vector (RefPattern n) n): (Σ' n', n <= n' ×' RefPattern n' × Vector (RefPattern n') n') :=
  match p with
  | GoGrammar.Pattern.Empty (Empty: GoGrammar.EmptyNode) =>
    ⟨n, by omega, RefPattern.Empty, xs⟩
  | GoGrammar.Pattern.ZAny (ZAny: GoGrammar.ZAny) =>
    ⟨n, by omega, RefPattern.ZAny, xs⟩
  | GoGrammar.Pattern.Reference (Reference: GoGrammar.Reference) =>
    ⟨n, by omega, RefPattern.Reference Reference.Name, xs⟩
  | GoGrammar.Pattern.LeafNode (LeafNode: GoGrammar.LeafNode) =>
    match xs.finIdxOf? RefPattern.Empty with
    | Option.none =>
      -- insert an empty pattern if non exists yet.
      let xs' := Vector.map (xs := xs) (fun x => x.castUp (n+1) (by omega))
      ⟨n+1, by simp_all, RefPattern.LeafNode LeafNode.Expr (Fin.mk n (by simp_all)), xs'.push RefPattern.Empty⟩
    | Option.some idx =>
      ⟨n, by omega, RefPattern.LeafNode LeafNode.Expr idx, xs⟩
  | GoGrammar.Pattern.TreeNode (Name: GoGrammar.NameExpr) (Colon: Option GoGrammar.Keyword) (Pattern: GoGrammar.Pattern)  =>
    let ⟨cn, ch, cp, cxs⟩ := mkRefPattern Pattern xs
    let cxs' := Vector.map (xs := cxs) (fun x => x.castUp (cn+1) (by omega))
    ⟨cn+1, by omega, RefPattern.TreeNode Name (Fin.mk cn (by simp)), cxs'.push (cp.castUp (cn+1) (by simp))⟩
  | GoGrammar.Pattern.Or (OpenParen: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (Pipe: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (CloseParen: Option GoGrammar.Keyword) =>
    let ⟨n1, h1, p1, xs1⟩ := mkRefPattern LeftPattern xs
    let ⟨n2, h2, p2, xs2⟩ := mkRefPattern RightPattern xs1
    let p11 := p1.castUp n2 (by omega)
    ⟨n2, by omega, RefPattern.Or p11 p2, xs2⟩
  | GoGrammar.Pattern.And (OpenParen: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (Ampersand: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (CloseParen: Option GoGrammar.Keyword) =>
    let ⟨n1, h1, p1, xs1⟩ := mkRefPattern LeftPattern xs
    let ⟨n2, h2, p2, xs2⟩ := mkRefPattern RightPattern xs1
    let p11 := p1.castUp n2 (by omega)
    ⟨n2, by omega, RefPattern.And p11 p2, xs2⟩
  | GoGrammar.Pattern.Xor (OpenParen: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (Caret: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (CloseParen: Option GoGrammar.Keyword) =>
    let ⟨n1, h1, p1, xs1⟩ := mkRefPattern LeftPattern xs
    let ⟨n2, h2, p2, xs2⟩ := mkRefPattern RightPattern xs1
    let p11 := p1.castUp n2 (by omega)
    ⟨n2, by omega, RefPattern.Xor p11 p2, xs2⟩
  | GoGrammar.Pattern.Concat (OpenBracket: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (Comma: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (ExtraComma: Option GoGrammar.Keyword) (CloseBracket: Option GoGrammar.Keyword) =>
    let ⟨n1, h1, p1, xs1⟩ := mkRefPattern LeftPattern xs
    let ⟨n2, h2, p2, xs2⟩ := mkRefPattern RightPattern xs1
    let p11 := p1.castUp n2 (by omega)
    ⟨n2, by omega, RefPattern.Concat p11 p2, xs2⟩
  | GoGrammar.Pattern.Interleave (OpenCurly: Option GoGrammar.Keyword) (LeftPattern: GoGrammar.Pattern) (SemiColon: GoGrammar.Keyword) (RightPattern: GoGrammar.Pattern) (ExtraSemiColon: Option GoGrammar.Keyword) (CloseCurly: Option GoGrammar.Keyword) =>
    let ⟨n1, h1, p1, xs1⟩ := mkRefPattern LeftPattern xs
    let ⟨n2, h2, p2, xs2⟩ := mkRefPattern RightPattern xs1
    let p11 := p1.castUp n2 (by omega)
    ⟨n2, by omega, RefPattern.Interleave p11 p2, xs2⟩
  | GoGrammar.Pattern.ZeroOrMore (OpenParen: Option GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) (CloseParen: Option GoGrammar.Keyword) (Star: GoGrammar.Keyword) =>
    let ⟨n1, h1, p1, xs1⟩ := mkRefPattern Pattern xs
    ⟨n1, by omega, RefPattern.ZeroOrMore p1, xs1⟩
  | GoGrammar.Pattern.Not (Exclamation: GoGrammar.Keyword) (OpenParen: Option GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) (CloseParen: Option GoGrammar.Keyword) =>
    let ⟨n1, h1, p1, xs1⟩ := mkRefPattern Pattern xs
    ⟨n1, by omega, RefPattern.Not p1, xs1⟩
  | GoGrammar.Pattern.Contains (Dot: GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) =>
    let ⟨n1, h1, p1, xs1⟩ := mkRefPattern Pattern xs
    ⟨n1, by omega, RefPattern.Contains p1, xs1⟩
  | GoGrammar.Pattern.Optional (OpenParen: Option GoGrammar.Keyword) (Pattern: GoGrammar.Pattern) (CloseParen: Option GoGrammar.Keyword) (QuestionMark: GoGrammar.Keyword) =>
    let ⟨n1, h1, p1, xs1⟩ := mkRefPattern Pattern xs
    ⟨n1, by omega, RefPattern.Optional p1, xs1⟩

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
  match t.Variable with
  | some v =>
    match Variable.toPredString v with
    | Except.ok p => Except.ok p
    | Except.error _err => throw s!"expected variable terminal of type String {repr t}"
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
      | some v => do
        let vs <- Terminals.toStrings es'
        return (v :: vs)
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
      | _ => throw s!"unsupported type {repr e}"
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
      | GoGrammar.Typ.single_string => Pred.length_string <$> Expr.toPredString p
      | GoGrammar.Typ.single_bytes => Pred.length_bytes <$> Expr.toPredBytes p
      | _ => throw s!"unsupported type {repr e}"
    | _ => throw s!"expected int function {repr e}"
  | _ => throw s!"expected expr of type int {repr e}"
partial def Expr.toPredString (e: GoGrammar.Expr): Except String (TestSuiteLib.Pred String) :=
  match e with
  | GoGrammar.Expr.Terminal _ _ t => Terminal.toPredString t
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

partial def RefPattern.toRule (g: RefGrammarMap n) (p: RefPattern n): Except String (Regex (TestSuiteLib.Pred Bool × Fin n)) :=
  match p with
  | Empty => return Regex.emptystr
  | ZAny => return Regex.compliment (Regex.emptyset)
  | Reference (name: String) =>
    match g.get? name with
    | none => throw s!"unknown reference {name}"
    | some rp => RefPattern.toRule g rp
  | LeafNode (e: GoGrammar.Expr) (refn: Fin n) =>
    Regex.symbol <$> (·,refn) <$> Expr.toPredBool e
  | TreeNode (name: GoGrammar.NameExpr) (refn: Fin n) => do
    return Regex.symbol (<- NameExpr.toPred name, refn)
  | Or (p1: RefPattern n) (p2: RefPattern n) => do
    let left <- RefPattern.toRule g p1
    let right <- RefPattern.toRule g p2
    return Regex.or left right
  | And (p1: RefPattern n) (p2: RefPattern n) => do
    let left <- RefPattern.toRule g p1
    let right <- RefPattern.toRule g p2
    return Regex.and left right
  | Xor (p1: RefPattern n) (p2: RefPattern n) => do
    let left <- RefPattern.toRule g p1
    let right <- RefPattern.toRule g p2
    return Regex.xor left right
  | Concat (p1: RefPattern n) (p2: RefPattern n) => do
    let left <- RefPattern.toRule g p1
    let right <- RefPattern.toRule g p2
    return Regex.concat left right
  | Interleave (p1: RefPattern n) (p2: RefPattern n) => do
    let left <- RefPattern.toRule g p1
    let right <- RefPattern.toRule g p2
    return Regex.interleave left right
  | ZeroOrMore (p1: RefPattern n) => do
    let res <- RefPattern.toRule g p1
    return Regex.star res
  | Not (p1: RefPattern n) => do
    let res <- RefPattern.toRule g p1
    return Regex.compliment res
  | Contains (p1: RefPattern n) => do
    let res <- RefPattern.toRule g p1
    return Regex.concat Regex.starAny (Regex.concat res Regex.starAny)
  | Optional (p1: RefPattern n) => do
    let res <- RefPattern.toRule g p1
    return Regex.or res Regex.emptystr

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

def maxRefs (xs: List (Regex (φ × Nat))): Nat :=
  match h: xs with
  | [] => 0
  | x'::xs' => List.max (List.map maxRef xs) (by
      subst h
      simp_all only [List.map_cons, ne_eq, reduceCtorEq, not_false_eq_true]
    )

def toFin (x: (Regex (φ × Nat))) (h: n >= maxRef x): Regex (φ × Fin (n + 1)) :=
  match x with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptystr
  | Regex.star r1 => Regex.star (toFin r1 h)
  | Regex.symbol (p, n') => Regex.symbol (p, Fin.mk n' (by
      simp only [maxRef] at h
      omega
    ))
  | Regex.or r1 r2 => Regex.or
    (toFin r1 (by simp only [maxRef] at h; omega))
    (toFin r2 (by simp only [maxRef] at h; omega))
  | Regex.concat r1 r2 => Regex.concat
    (toFin r1 (by simp only [maxRef] at h; omega))
    (toFin r2 (by simp only [maxRef] at h; omega))
  | Regex.interleave r1 r2 => Regex.interleave
    (toFin r1 (by simp only [maxRef] at h; omega))
    (toFin r2 (by simp only [maxRef] at h; omega))
  | Regex.and r1 r2 => Regex.and
    (toFin r1 (by simp only [maxRef] at h; omega))
    (toFin r2 (by simp only [maxRef] at h; omega))
  | Regex.compliment r1 => Regex.compliment (toFin r1 h)
  | Regex.xor r1 r2 => Regex.xor
    (toFin r1 (by simp only [maxRef] at h; omega))
    (toFin r2 (by simp only [maxRef] at h; omega))

theorem max_cons
  {x : Nat} {xs : List Nat} {h: x :: xs ≠ []} :
  (x :: xs).max h = max x ((x :: xs).max h) := by
  induction xs with
  | nil =>
    simp only [List.max_singleton]
    rw [Std.max_self]
  | cons x' xs ih =>
    simp only [List.max]
    rw [@List.foldl_cons]
    rw [List.foldl_max]
    simp only [right_eq_sup]
    omega

theorem max_max {x: Nat} {xs: List Nat}:
  max x (xs.max?.getD x) = (x::xs).max (by simp) := by
  simp [List.max]
  rw [List.foldl_max]

theorem max_cons1
  {x : Nat} {xs : List Nat} {h: x :: xs ≠ []} :
  (x :: xs).max h = max x (xs.max?.getD 0) := by
  cases xs with
  | nil =>
    simp
  | cons x' xs =>
    simp only [List.max]
    rw [@List.foldl_cons]
    rw [List.foldl_max]
    nth_rewrite 2 [List.max?.eq_def]
    nth_rewrite 2 [Option.getD.eq_def]
    simp only
    rw [max_max]
    simp only [List.max]
    rw [@List.foldl_max]
    rw [@List.foldl_max]
    induction xs with
    | nil =>
      simp
    | cons y ys ih =>
      simp only [List.max?_cons, Option.getD_some, Nat.max_assoc]

theorem max_cons2
  {x1 x2 : Nat} {xs : List Nat} {h: x1 :: x2 :: xs ≠ []} :
  (x1 :: x2 :: xs).max h = max x1 ((x2 :: xs).max (by simp)) := by
  simp only [List.max]
  simp only [List.foldl]
  rw [List.foldl_max]
  rw [List.foldl_max]
  simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, Nat.max_assoc]
  rw [<- Nat.max_assoc]
  rw [<- Nat.max_assoc]
  induction xs with
  | nil =>
    simp
  | cons x xs ih =>
    simp

theorem max1 (h : n >= maxRefs (x :: xs')): n >= maxRef x := by
  induction xs' with
  | nil =>
    simp [maxRefs, List.max] at h
    omega
  | cons y ys ih =>
    simp [maxRefs, List.max] at h
    rw [← List.foldl_cons] at h
    rw [List.foldl_max] at h
    omega

theorem maxs (h : n >= maxRefs (x :: xs')): n >= maxRefs xs' := by
  induction hxs: xs' with
  | nil =>
    simp [maxRefs, List.max] at h
    simp [maxRefs]
  | cons y ys ih =>
    simp [maxRefs] at h
    rw [hxs] at h
    simp only [List.map] at h
    rw [max_cons2] at h
    simp only [maxRefs]
    simp only [List.map]
    omega

def listToFin (xs: List (Regex (φ × Nat))) (h: n >= maxRefs xs): List (Regex (φ × Fin (n + 1))) :=
  match xs with
  | [] => []
  | (x::xs') =>
    toFin x (by
      apply max1
      omega
    ) :: listToFin xs' (by
      apply maxs
      omega
    )

def listToVector (xs: List (Regex (φ × Fin n))): Vector (Regex (φ × Fin n)) n := Id.run do
  let mut v: Vector (Regex (φ × Fin n)) n := Vector.mk (Array.replicate n Regex.emptyset) (by
    simp only [Array.size_replicate]
  )
  let finList := List.finRange n
  let zipList := List.zip finList xs
  for item in zipList do
    v := v.set! item.1.toNat item.2
  v


def RefGrammar.mk (g: GoGrammar.Grammar): Σ n, RefGrammarMap n × Vector (RefPattern n) n := Id.run do
  -- create RefPattern for main
  let ⟨n, _hn, topRefPattern, topRefPatterns⟩ := mkRefPattern g.TopPattern #v[]
  let mut res: Σ n, RefGrammarMap n × Vector (RefPattern n) n := ⟨n, Std.HashMap.emptyWithCapacity.insert "main" topRefPattern, topRefPatterns⟩

  let decls := g.PatternDecls.getD []
  for decl in decls do
    match res with
    | ⟨_n, refMap, refPatterns'⟩ =>
      let ⟨n', hn', refPattern, newRefPatterns⟩ := mkRefPattern decl.Pattern refPatterns'
      let mut newRefMap: RefGrammarMap n' := Std.HashMap.emptyWithCapacity.insert decl.Name refPattern
      for ⟨key, value⟩ in refMap do
        newRefMap := newRefMap.insert key (value.castUp n' hn')
      res := ⟨n', newRefMap, newRefPatterns⟩

  res

abbrev Rule n := Regex (TestSuiteLib.Pred Bool × Fin n)

def GoGrammartoLeanGrammar (g: GoGrammar.Grammar): Except String (Σ n, (Grammar n (TestSuiteLib.Pred Bool))) := do
  let ⟨n, refMap, refPatterns⟩ : Σ n, RefGrammarMap n × Vector (RefPattern n) n := RefGrammar.mk g

  match refMap.get? "main" with
  | Option.none => throw "no main pattern"
  | Option.some startRefPattern =>
  let start: Rule n <- RefPattern.toRule refMap startRefPattern

  let prods : Vector (Regex (TestSuiteLib.Pred Bool × Ref n)) n <- refPatterns.mapM (RefPattern.toRule refMap)

  return Sigma.mk n <|
    Grammar.mk
    (start := start)
    (prods := prods)
