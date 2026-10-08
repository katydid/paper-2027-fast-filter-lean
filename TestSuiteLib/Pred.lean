import VerifiedFilter.Std.Bytes
import VerifiedFilter.Std.Int
import VerifiedFilter.Std.String
import VerifiedFilter.Std.Float

import VerifiedFilter.Parser.Token

import TestSuiteLib.Regexp

namespace TestSuiteLib

def decideRel (p : α → β → Prop) [d: DecidableRel p]: α → β → Bool :=
  fun a b => decide (p a b)

def List.get? {α : Type u}: (as : List α) → (index: Nat) → Except String α
  | List.nil, _ => throw "index out of bounds"
  | List.cons a _, 0 => return a
  | List.cons _ as, Nat.succ i => get? as i

def List.range {α: Type u} (xs: List α) (a b: Nat): Except String (List α) :=
  match a with
  | 0 =>
    match b with
    | 0 => return []
    | Nat.succ b' =>
      match xs with
      | [] => throw "b out of range"
      | (x::xs') => (x::·) <$> List.range xs' 0 b'
  | Nat.succ a' =>
    match xs with
    | [] => throw "a out of range"
    | (_::xs') => List.range xs' a' b

def OurList.le [LE α] [DecidableEq α] [DecidableLE α] (xs ys: List α): Bool :=
  match xs, ys with
  | [], [] => true
  | (_x::_), [] => false
  | [], (_y::_) => true
  | (x::xs), (y::ys) =>
    if x == y
    then OurList.le xs ys
    else
      if x <= y
      then true
      else false

def OurList.lt [LT α] [DecidableEq α] [DecidableLT α] (xs ys: List α): Bool :=
  match xs, ys with
  | [], [] => true
  | (_x::_), [] => false
  | [], (_y::_) => true
  | (x::xs), (y::ys) =>
    if x == y
    then OurList.lt xs ys
    else
      if x < y
      then true
      else false

set_option deriving.decEq.linear_construction_threshold 1
set_option deriving.ord.linear_construction_threshold 1
inductive Pred : (α: Type) -> Type where
  | any: Pred Bool
  | bool_const : (b: Bool) -> Pred Bool
  | bytes_const : (b:  Bytes) -> Pred Bytes
  | double_const : (d: Float64Bits) -> Pred Float64Bits
  | int_const : (d: Int64) -> Pred Int64
  | string_const : (s: String) -> Pred String
  | uint_const : (u: UInt64) -> Pred UInt64

  | bools_const : (b: List Bool) -> Pred (List Bool)
  | bytess_const : (b: List Bytes) -> Pred (List Bytes)
  | doubles_const : (d: List Float64Bits) -> Pred (List Float64Bits)
  | ints_const : (d: List Int64) -> Pred (List Int64)
  | strings_const : (s: List String) -> Pred (List String)
  | uints_const : (u: List UInt64) -> Pred (List UInt64)

  | bool_var: Pred Bool
  | bytes_var: Pred Bytes
  | double_var : Pred Float64Bits
  | int_var : Pred Int64
  | string_var : Pred String
  | uint_var : Pred UInt64
  | tag_var : Pred String

  -- func and(bool,bool) bool
  | and (p1 p2: Pred Bool): Pred Bool
  -- func or(bool,bool) bool
  | or (p1 p2: Pred Bool): Pred Bool
  -- func not(bool) bool
  | not (p: Pred Bool): Pred Bool
  -- func xor(bool,bool) bool
  | xor (p1 p2: Pred Bool): Pred Bool

  -- func contains(int,const []int) bool
  -- func contains(string,const []string) bool
  -- func contains(string,string) bool
  -- func contains(uint,const []uint) bool
  | contains_string (haystack: Pred String) (sub: Pred String): Pred Bool
  | contains_strings (s: Pred String) (ss: Pred (List String)): Pred Bool
  | contains_ints (s: Pred Int64) (ss: Pred (List Int64)): Pred Bool
  | contains_uints (s: Pred UInt64) (ss: Pred (List UInt64)): Pred Bool

  -- func elem([][]byte,int) []byte
  -- func elem([]bool,int) bool
  -- func elem([]double,int) double
  -- func elem([]int,int) int
  -- func elem([]string,int) string
  -- func elem([]uint,int) uint
  | elem_bytes (bytes: Pred (List Bytes)) (index: Pred Int64): Pred Bytes
  | elem_bools (bools: Pred (List Bool)) (index: Pred Int64): Pred Bool
  | elem_doubles (doubles: Pred (List Float64Bits)) (index: Pred Int64): Pred Float64Bits
  | elem_ints (ints: Pred (List Int64)) (index: Pred Int64): Pred Int64
  | elem_strings (string: Pred (List String)) (index: Pred Int64): Pred String
  | elem_uints (uints: Pred (List UInt64)) (index: Pred Int64): Pred UInt64

  -- func eq([]byte,[]byte) bool
  -- func eq(bool,bool) bool
  -- func eq(double,double) bool
  -- func eq(int,int) bool
  -- func eq(string,string) bool
  -- func eq(uint,uint) bool
  | eq_bool : (x y: Pred Bool) -> Pred Bool
  | eq_bytes : (x y: Pred Bytes) -> Pred Bool
  | eq_double : (x y: Pred Float64Bits) -> Pred Bool
  | eq_int : (x y: Pred Int64) -> Pred Bool
  | eq_string : (x y: Pred String) -> Pred Bool
  | eq_uint : (x y: Pred UInt64) -> Pred Bool

  -- func ne([]byte,[]byte) bool
  -- func ne(bool,bool) bool
  -- func ne(double,double) bool
  -- func ne(int,int) bool
  -- func ne(string,string) bool
  -- func ne(uint,uint) bool
  | ne_bool : (x y: Pred Bool) -> Pred Bool
  | ne_bytes : (x y: Pred Bytes) -> Pred Bool
  | ne_double : (x y: Pred Float64Bits) -> Pred Bool
  | ne_int : (x y: Pred Int64) -> Pred Bool
  | ne_string : (x y: Pred String) -> Pred Bool
  | ne_uint : (x y: Pred UInt64) -> Pred Bool

  -- func ge([]byte,[]byte) bool
  | ge_bytes : (x y: Pred Bytes) -> Pred Bool
  -- func ge(double,double) bool
  | ge_double : (x y: Pred Float64Bits) -> Pred Bool
  -- func ge(int,int) bool
  | ge_int : (x y: Pred Int64) -> Pred Bool
  -- func ge(string,string) bool
  | ge_string : (x y: Pred String) -> Pred Bool
  -- func ge(uint,uint) bool
  | ge_uint : (x y: Pred UInt64) -> Pred Bool
  -- func gt([]byte,[]byte) bool
  | gt_bytes : (x y: Pred Bytes) -> Pred Bool
  -- func gt(double,double) bool
  | gt_double : (x y: Pred Float64Bits) -> Pred Bool
  -- func gt(int,int) bool
  | gt_int : (x y: Pred Int64) -> Pred Bool
  -- func gt(string,string) bool
  | gt_string : (x y: Pred String) -> Pred Bool
  -- func gt(uint,uint) bool
  | gt_uint : (x y: Pred UInt64) -> Pred Bool
  -- func le([]byte,[]byte) bool
  | le_bytes : (x y: Pred Bytes) -> Pred Bool
  -- func le(double,double) bool
  | le_double : (x y: Pred Float64Bits) -> Pred Bool
  -- func le(int,int) bool
  | le_int : (x y: Pred Int64) -> Pred Bool
  -- func le(string,string) bool
  | le_string : (x y: Pred String) -> Pred Bool
  -- func le(uint,uint) bool
  | le_uint : (x y: Pred UInt64) -> Pred Bool
  -- func lt([]byte,[]byte) bool
  | lt_bytes : (x y: Pred Bytes) -> Pred Bool
  -- func lt(double,double) bool
  | lt_double : (x y: Pred Float64Bits) -> Pred Bool
  -- func lt(int,int) bool
  | lt_int : (x y: Pred Int64) -> Pred Bool
  -- func lt(string,string) bool
  | lt_string : (x y: Pred String) -> Pred Bool
  -- func lt(uint,uint) bool
  | lt_uint : (x y: Pred UInt64) -> Pred Bool

  -- func length([][]byte) int
  | length_bytess : (xs: Pred (List Bytes)) -> Pred Int64
  -- func length([]bool) int
  | length_bools : (xs: Pred (List Bool)) -> Pred Int64
  -- func length([]byte) int
  | length_bytes : (xs: Pred (Bytes)) -> Pred Int64
  -- func length([]double) int
  | length_doubles : (xs: Pred (List Float64Bits)) -> Pred Int64
  -- func length([]int) int
  | length_ints : (xs: Pred (List Int64)) -> Pred Int64
  -- func length([]string) int
  | length_strings : (xs: Pred (List String)) -> Pred Int64
  -- func length([]uint) int
  | length_uints : (xs: Pred (List UInt64)) -> Pred Int64
  -- func length(string) int
  | length_string : (xs: Pred (String)) -> Pred Int64

  -- func print([][]byte) [][]byte
  | print_bytess : (xs: Pred (List Bytes)) -> Pred (List Bytes)
  -- func print([]bool) []bool
  | print_bools : (xs: Pred (List Bool)) -> Pred (List Bool)
  -- func print([]double) []double
  | print_doubles : (xs: Pred (List Float64Bits)) -> Pred (List Float64Bits)
  -- func print([]int) []int
  | print_ints : (xs: Pred (List Int64)) -> Pred (List Int64)
  -- func print([]string) []string
  | print_strings : (xs: Pred (List String)) -> Pred (List String)
  -- func print([]uint) []uint
  | print_uints : (xs: Pred (List UInt64)) -> Pred (List UInt64)

  -- func print([]byte) []byte
  | print_bytes : (xs: Pred Bytes) -> Pred Bytes
  -- func print(bool) bool
  | print_bool : (xs: Pred Bool) -> Pred Bool
  -- func print(double) double
  | print_double : (xs: Pred Float64Bits) -> Pred Float64Bits
  -- func print(int) int
  | print_int : (xs: Pred Int64) -> Pred Int64
  -- func print(string) string
  | print_string : (xs: Pred String) -> Pred String
  -- func print(uint) uint
  | print_uint : (xs: Pred UInt64) -> Pred UInt64

  -- func range([][]byte,int,int) [][]byte
  -- func range([]bool,int,int) []bool
  -- func range([]double,int,int) []double
  -- func range([]int,int,int) []int
  -- func range([]string,int,int) []string
  -- func range([]uint,int,int) []uint
  | range_bytes : (xs: Pred (List Bytes)) -> (a: Pred Int64) -> (b: Pred Int64) -> Pred (List Bytes)
  | range_bools : (xs: Pred (List Bool)) -> (a: Pred Int64) -> (b: Pred Int64) -> Pred (List Bool)
  | range_doubles : (xs: Pred (List Float64Bits)) -> (a: Pred Int64) -> (b: Pred Int64) -> Pred (List Float64Bits)
  | range_ints : (xs: Pred (List Int64)) -> (a: Pred Int64) -> (b: Pred Int64) -> Pred (List Int64)
  | range_strings : (xs: Pred (List String)) -> (a: Pred Int64) -> (b: Pred Int64) -> Pred (List String)
  | range_uints : (xs: Pred (List UInt64)) -> (a: Pred Int64) -> (b: Pred Int64) -> Pred (List UInt64)

  -- func type([]byte) bool
  -- func type(bool) bool
  -- func type(double) bool
  -- func type(int) bool
  -- func type(string) bool
  -- func type(uint) bool
  | type_bytes : (xs: Pred Bytes) -> Pred Bool
  | type_bool : (xs: Pred Bool) -> Pred Bool
  | type_double : (xs: Pred Float64Bits) -> Pred Bool
  | type_int : (xs: Pred Int64) -> Pred Bool
  | type_string : (xs: Pred String) -> Pred Bool
  | type_uint : (xs: Pred UInt64) -> Pred Bool

  -- func eqFold(string,string) bool
  | eqfold : (s1 s2: Pred String) -> Pred Bool
  -- func hasPrefix(string,string) bool
  | hasPrefix : (s1 s2: Pred String) -> Pred Bool
  -- func hasSuffix(string,string) bool
  | hasSuffix : (s1 s2: Pred String) -> Pred Bool
  -- func toLower(string) string
  | toLower : (s: Pred String) -> Pred String
  -- func toUpper(string) string
  | toUpper : (s: Pred String) -> Pred String
  -- func regex(const string,string) bool
  | regex : (p: Pred String) -> (s: Pred String) -> Pred Bool

  deriving DecidableEq, Ord, Repr, Hashable

def Pred.eval (p: Pred α) (x: Token): Except String α :=
  match p with
  | Pred.any => return true

  | Pred.bool_const v => return v
  | Pred.bytes_const v => return v
  | Pred.double_const v => return v
  | Pred.int_const v => return v
  | Pred.string_const v => return v
  | Pred.uint_const v => return v

  | Pred.bools_const v => return v
  | Pred.bytess_const v => return v
  | Pred.doubles_const v => return v
  | Pred.ints_const v => return v
  | Pred.strings_const v => return v
  | Pred.uints_const v => return v

  | Pred.bool_var =>
    match x with
    | Token.bool b => return b
    | _ => throw "token is not a bool var"
  | Pred.bytes_var =>
    match x with
    | Token.bytes b => return b
    | _ => throw "token is not a bytes var"
  | Pred.double_var =>
    match x with
    | Token.int64 i => return Float64Bits.fromFloat <| i.toFloat
    | Token.float64 b => return b
    | _ => throw "token is not a double var"
  | Pred.int_var =>
    match x with
    | Token.int64 v => return v
    | Token.nanoseconds v => return v
    | _ => throw "token is not a int var"
  | Pred.string_var =>
    match x with
    | Token.string b => return b
    | _ => throw "token is not a string var"
  | Pred.uint_var =>
    match x with
    | Token.int64 v =>
      if v < 0
      then throw "token is not a uint var, it is a negative number"
      else return v.toUInt64
    | Token.decimal s => Float.toUInt64 <$> Float.fromString? s
    | _ => throw "token is not a uint var"
  | Pred.tag_var =>
    match x with
    | Token.tag s => return s
    | _ => throw "token is not a uint var"

  | Pred.and p1 p2 => Bool.and <$> p1.eval x <*> p2.eval x
  | Pred.or p1 p2 => Bool.or <$> p1.eval x <*> p2.eval x
  | Pred.not p1 => Bool.not <$> p1.eval x
  | Pred.xor p1 p2 => Bool.xor <$> p1.eval x <*> p2.eval x

  | Pred.contains_string haystack sub => do
    let h <- haystack.eval x
    let s <- sub.eval x
    return String.contains h s
  | Pred.contains_strings s ss => List.contains <$> ss.eval x <*> s.eval x
  | Pred.contains_ints s ss => List.contains <$> ss.eval x <*> s.eval x
  | Pred.contains_uints s ss => List.contains <$> ss.eval x <*> s.eval x

  | elem_bools xs index => do
    let elems <- xs.eval x
    let i <- index.eval x
    List.get? elems i.toInt.toNat
  | elem_bytes xs index => do
    let elems <- xs.eval x
    let i <- index.eval x
    List.get? elems i.toInt.toNat
  | elem_doubles xs index => do
    let elems <- xs.eval x
    let i <- index.eval x
    List.get? elems i.toInt.toNat
  | elem_ints xs index => do
    let elems <- xs.eval x
    let i <- index.eval x
    List.get? elems i.toInt.toNat
  | elem_strings xs index => do
    let elems <- xs.eval x
    let i <- index.eval x
    List.get? elems i.toInt.toNat
  | elem_uints xs index => do
    let elems <- xs.eval x
    let i <- index.eval x
    List.get? elems i.toInt.toNat

  | Pred.eq_bool p1 p2 => BEq.beq <$> p1.eval x <*> p2.eval x
  | Pred.eq_bytes p1 p2 => BEq.beq <$> p1.eval x <*> p2.eval x
  | Pred.eq_double p1 p2 => BEq.beq <$> p1.eval x <*> p2.eval x
  | Pred.eq_int p1 p2 => BEq.beq <$> p1.eval x <*> p2.eval x
  | Pred.eq_string p1 p2 => BEq.beq <$> p1.eval x <*> p2.eval x
  | Pred.eq_uint p1 p2 => BEq.beq <$> p1.eval x <*> p2.eval x

  | Pred.ne_bool p1 p2 => Bool.not <$> (BEq.beq <$> p1.eval x <*> p2.eval x)
  | Pred.ne_bytes p1 p2 => Bool.not <$> (BEq.beq <$> p1.eval x <*> p2.eval x)
  | Pred.ne_double p1 p2 => Bool.not <$> (BEq.beq <$> p1.eval x <*> p2.eval x)
  | Pred.ne_int p1 p2 => Bool.not <$> (BEq.beq <$> p1.eval x <*> p2.eval x)
  | Pred.ne_string p1 p2 => Bool.not <$> (BEq.beq <$> p1.eval x <*> p2.eval x)
  | Pred.ne_uint p1 p2 => Bool.not <$> (BEq.beq <$> p1.eval x <*> p2.eval x)

  | Pred.le_bytes p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return OurList.le v1.toList v2.toList
  | Pred.le_double p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return decideRel _ (d := UInt64.decLe) v1 v2
  | Pred.le_int p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return decideRel _ (d := Int64.decLe) v1 v2
  | Pred.le_string p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return OurList.le v1.toList v2.toList
  | Pred.le_uint p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return decideRel _ (d := UInt64.decLe) v1 v2

  | Pred.lt_bytes p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return OurList.lt v1.toList v2.toList
  | Pred.lt_double p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return decideRel _ (d := UInt64.decLt) v1 v2
  | Pred.lt_int p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return decideRel _ (d := Int64.decLt) v1 v2
  | Pred.lt_string p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return OurList.lt v1.toList v2.toList
  | Pred.lt_uint p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return decideRel _ (d := UInt64.decLt) v1 v2

  | Pred.ge_bytes p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return Bool.not <| OurList.le v1.toList v2.toList
  | Pred.ge_double p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return Bool.not <| decideRel _ (d := UInt64.decLt) v1 v2
  | Pred.ge_int p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return Bool.not <| decideRel _ (d := Int64.decLt) v1 v2
  | Pred.ge_string p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return Bool.not <| OurList.le v1.toList v2.toList
  | Pred.ge_uint p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return Bool.not <| decideRel _ (d := UInt64.decLt) v1 v2

  | Pred.gt_bytes p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return Bool.not <| OurList.lt v1.toList v2.toList
  | Pred.gt_double p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return Bool.not <| decideRel _ (d := UInt64.decLe) v1 v2
  | Pred.gt_int p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return Bool.not <| decideRel _ (d := Int64.decLe) v1 v2
  | Pred.gt_string p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return Bool.not <| OurList.lt v1.toList v2.toList
  | Pred.gt_uint p1 p2 => do
    let v1 <- p1.eval x
    let v2 <- p2.eval x
    return Bool.not <| decideRel _ (d := UInt64.decLe) v1 v2

  | length_bytess (xs: Pred (List Bytes)) =>
    Nat.toInt64 <$> List.length <$> xs.eval x
  | length_bools (xs: Pred (List Bool)) =>
    Nat.toInt64 <$> List.length <$> xs.eval x
  | length_bytes (xs: Pred (Bytes)) =>
    Nat.toInt64 <$> List.length <$> Array.toList <$> xs.eval x
  | length_doubles (xs: Pred (List Float64Bits)) =>
    Nat.toInt64 <$> List.length <$> xs.eval x
  | length_ints (xs: Pred (List Int64)) =>
    Nat.toInt64 <$> List.length <$> xs.eval x
  | length_strings (xs: Pred (List String)) =>
    Nat.toInt64 <$> List.length <$> xs.eval x
  | length_uints (xs: Pred (List UInt64)) =>
    Nat.toInt64 <$> List.length <$> xs.eval x
  | length_string (xs: Pred (String)) =>
    Nat.toInt64 <$> List.length <$> String.toList <$> xs.eval x

  | print_bytess (xs: Pred (List Bytes)) =>
    xs.eval x
  | print_bools (xs: Pred (List Bool)) =>
    xs.eval x
  | print_doubles (xs: Pred (List Float64Bits)) =>
    xs.eval x
  | print_ints (xs: Pred (List Int64)) =>
    xs.eval x
  | print_strings (xs: Pred (List String)) =>
    xs.eval x
  | print_uints (xs: Pred (List UInt64)) =>
    xs.eval x

  | print_bytes (xs: Pred Bytes) =>
    xs.eval x
  | print_bool (xs: Pred Bool) =>
    xs.eval x
  | print_double (xs: Pred Float64Bits) =>
    xs.eval x
  | print_int (xs: Pred Int64) =>
    xs.eval x
  | print_string (xs: Pred String) =>
    xs.eval x
  | print_uint (xs: Pred UInt64) =>
    xs.eval x

  | range_bytes (xs: Pred (List Bytes)) (a: Pred Int64) (b: Pred Int64) => do
    let xs' <- xs.eval x
    let a' <- a.eval x
    let b' <- b.eval x
    List.range xs' a'.toInt.toNat b'.toInt.toNat
  | range_bools (xs: Pred (List Bool)) (a: Pred Int64) (b: Pred Int64) => do
    let xs' <- xs.eval x
    let a' <- a.eval x
    let b' <- b.eval x
    List.range xs' a'.toInt.toNat b'.toInt.toNat
  | range_doubles (xs: Pred (List Float64Bits)) (a: Pred Int64) (b: Pred Int64) => do
    let xs' <- xs.eval x
    let a' <- a.eval x
    let b' <- b.eval x
    List.range xs' a'.toInt.toNat b'.toInt.toNat
  | range_ints (xs: Pred (List Int64)) (a: Pred Int64) (b: Pred Int64) => do
    let xs' <- xs.eval x
    let a' <- a.eval x
    let b' <- b.eval x
    List.range xs' a'.toInt.toNat b'.toInt.toNat
  | range_strings (xs: Pred (List String)) (a: Pred Int64) (b: Pred Int64) => do
    let xs' <- xs.eval x
    let a' <- a.eval x
    let b' <- b.eval x
    List.range xs' a'.toInt.toNat b'.toInt.toNat
  | range_uints (xs: Pred (List UInt64)) (a: Pred Int64) (b: Pred Int64) => do
    let xs' <- xs.eval x
    let a' <- a.eval x
    let b' <- b.eval x
    List.range xs' a'.toInt.toNat b'.toInt.toNat

  | type_bytes (xs: Pred Bytes) =>
    match xs.eval x with
    | Except.ok _ => return true
    | Except.error _ => return false
  | type_bool (xs: Pred Bool) =>
    match xs.eval x with
    | Except.ok _ => return true
    | Except.error _ => return false
  | type_double (xs: Pred Float64Bits) =>
    match xs.eval x with
    | Except.ok _ => return true
    | Except.error _ => return false
  | type_int (xs: Pred Int64) =>
    match xs.eval x with
    | Except.ok _ => return true
    | Except.error _ => return false
  | type_string (xs: Pred String) =>
    match xs.eval x with
    | Except.ok _ => return true
    | Except.error _ => return false
  | type_uint (xs: Pred UInt64) =>
    match xs.eval x with
    | Except.ok _ => return true
    | Except.error _ => return false

  | Pred.eqfold s1 s2 => do
    let ss1 <- s1.eval x
    let ss2 <- s2.eval x
    return BEq.beq ss1.toLower ss2.toLower

  | hasPrefix (s1: Pred String) (s2: Pred String) =>
    String.isPrefixOf <$> s1.eval x <*> s2.eval x
  | hasSuffix (s1: Pred String) (s2: Pred String) => do
    let s1' <- s1.eval x
    let s2' <- s2.eval x
    return String.endsWith s1' s2'
  | toLower (s: Pred String) =>
    String.toLower <$> s.eval x
  | toUpper (s: Pred String) =>
    String.toUpper <$> s.eval x
  | regex (p: Pred String) (s2: Pred String) => do
    let p' <- p.eval x
    let s2' <- s2.eval x
    Regexp.check p' s2'

def Pred.evalb (p: Pred Bool) (x: Token): Bool :=
  match Pred.eval p x with
  | Except.error _ => false
  | Except.ok k => k

#guard Pred.evalb (Pred.ge_string (Pred.string_var) (Pred.string_const "10")) (Token.string "11")
  = true

#guard Pred.evalb (Pred.ge_string (Pred.string_var) (Pred.string_const "11")) (Token.string "10")
  = false

#guard Pred.evalb (Pred.hasSuffix Pred.string_var (Pred.string_const "omen")) (Token.string "Abdomen")
  = true

#guard Pred.evalb (Pred.contains_string Pred.string_var (Pred.string_const "art")) (Token.string "Dart")
  = true
