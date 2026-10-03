module

import Regex
import Regex.Syntax.Parser.Error

import Init.Control.Except

namespace TestSuiteLib.Regexp

private def parse (s: String) : Except String Regex :=
  match Regex.parse s with
  | Except.ok r => Except.ok r
  | Except.error e => Except.error (toString e)

public def check (p s: String): Except String Bool := do
  let r <- parse p
  return r.test s

-- Thank you Brandon Rozek - https://brandonrozek.com/blog/writing-unit-tests-lean-4/
instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := by
  unfold DecidableEq
  intro a b
  cases a <;> cases b <;>
  -- Get rid of obvious cases where .ok != .err
  try { apply isFalse ; intro h ; injection h }
  case error.error c d =>
    match decEq c d with
      | isTrue h => apply isTrue (by rw [h])
      | isFalse _ => apply isFalse (by intro h; injection h; contradiction)
  case ok.ok c d =>
    match decEq c d with
      | isTrue h => apply isTrue (by rw [h])
      | isFalse _ => apply isFalse (by intro h; injection h; contradiction)

-- #guard (check ".*B.*" "ABC")
--   = Except.ok true
