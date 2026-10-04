-- Examples of a symbolic regular hedge grammars using the predicate type AnyPred.

import VerifiedFilter.Std.Hedge
import VerifiedFilter.Std.List
import VerifiedFilter.Std.Vector

import VerifiedFilter.Pred.AnyEq
import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Lang
import VerifiedFilter.Grammar.Grammar

namespace Grammar

open VerifiedFilter.Regex

example: Grammar 2 String := Grammar.mk
  (start := Regex.symbol ("title", 0))
  (prods := #v[
    Regex.symbol ("verified derivatives", 1),
    Regex.emptystr,
  ])

open Pred

example : Grammar 5 (AnyEq.Pred String) := Grammar.mk
  -- start := ("html", Html)
  (start := Regex.symbol (AnyEq.Pred.eq "html", 0))
  -- production rules
  (prods := #v[
    -- Html → ("head", Head) · ("body", Body)
    Regex.concat
      (Regex.symbol (AnyEq.Pred.eq "head", 1))
      (Regex.symbol (AnyEq.Pred.eq "body", 2))
    -- Head → ("title", Text) | ε
    , Regex.or
      (Regex.symbol (AnyEq.Pred.eq "title", 3))
      Regex.emptystr
    -- Body → ("p", Text)*
    , Regex.star (Regex.symbol (AnyEq.Pred.eq "p", 3))
    -- Text → (., Empty)
    , Regex.symbol (AnyEq.Pred.any, 4)
    -- Empty → ε
    , Regex.emptystr
  ])

private def example_grammar: Grammar 1 (AnyEq.Pred Char) :=
  Grammar.mk
    (Regex.or Regex.emptystr (Regex.symbol (AnyEq.Pred.eq 'a', 0)))
    #v[Regex.emptystr]

#guard
  example_grammar.lookup (Fin.mk 0 (by omega))
  = Regex.emptystr
