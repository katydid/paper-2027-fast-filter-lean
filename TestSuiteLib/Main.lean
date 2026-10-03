import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson

import VerifiedFilter.Std.Hedge
import VerifiedFilter.Parser.Token
import TestSuiteLib.Hedge
import TestSuiteLib.GoGrammar

open Lean

namespace TestSuiteLib

structure Test where
  name: String
  grammar: GoGrammar.Grammar
  valid: Bool
  input: Hedge Token

def parseHedge (s: String): IO (Hedge Token) := do
  match Lean.Json.parse s with
  | Except.error err => EIO.throw err
  | Except.ok j =>
  match Hedge.fromJson? j with
  | Except.error err => EIO.throw err
  | Except.ok node => return node

def parseGrammar (s: String): IO GoGrammar.Grammar := do
  match Lean.Json.parse s with
  | Except.error err => EIO.throw s!"{err}: {s}"
  | Except.ok j =>
  match FromJson.fromJson? j with
  | Except.error err => EIO.throw s!"{err}: {s}"
  | Except.ok g => return g

def main (args : List String): IO Unit := do
  -- https://lean-lang.org/doc/reference/latest/IO/Files___-File-Handles___-and-Streams/#IO___FS___readFile
  let cur: System.FilePath := System.FilePath.toString args.head!
  let hedge_test_dir := cur / "validator" / "tests" / "hedge"
  let hedge_test_dirs <- hedge_test_dir.readDir
  let mut tests: Array Test := #[]
  for direntry in hedge_test_dirs do
    let test_files <- direntry.path.readDir
    let name := direntry.fileName
    let mut inputStr := ""
    let mut grammarStr := ""
    let mut valid := false
    for test_file in test_files do
      match test_file.fileName with
      | "valid.hedge" =>
        valid := true
        inputStr <- IO.FS.readFile test_file.path
      | "invalid.hedge" =>
        valid := false
        inputStr <- IO.FS.readFile test_file.path
      | "validator.json" =>
        grammarStr <- IO.FS.readFile test_file.path
      | _ =>
        valid := valid
    let input <- parseHedge inputStr
    let grammar <- parseGrammar grammarStr
    tests := tests ++ [Test.mk (name := name) (grammar := grammar) (valid := valid) (input := input)]
  let testList := tests.toList.mergeSort (fun x y => compare x.name y.name == Ordering.eq || Ord.compare x.name y.name == Ordering.lt)
  for test in testList do
    IO.println test.name
  IO.println tests.size
