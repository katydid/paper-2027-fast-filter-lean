import VerifiedFilter.Std.Hedge
import VerifiedFilter.Std.List
import VerifiedFilter.Std.Vector

import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Lang

import VerifiedFilter.Parser.Token
import VerifiedFilter.Pred.JSONSchema

import VerifiedFilter.Grammar.Grammar
import VerifiedFilter.Grammar.Katydid

namespace VerifiedFilter.JSONSchema

open VerifiedFilter.Regex
open Regex
open Pred.JSONSchema

-- We originally copied this schema from https://json-schema.org/learn/json-schema-examples#blog-post.
-- We made a smaller version to use as an example:

-- ```json
-- { "type": "object", "additionalProperties": false, "required": ["content"],
--   "properties": {
--     "content": { "type": "string" },
--     "author": { "$ref": "#/definitions/user-profile" } },
--   "definitions": { "user-profile": {
--     "type": "object", "additionalProperties": false, "required": ["username"],
--     "properties": {
--       "username": { "type": "string" },
--       "email": { "type": "string", "format": "email" } } } } }
-- ```

-- This might be translated to:

def example_untagged_grammar_blogpost : Grammar 5 Pred := Grammar.mk
  (start := (interleave
      (symbol (Pred.strEq "content", 2))
      (optional (symbol (Pred.strEq "author", 4)))))
  (prods := #v[emptystr, starAny, symbol (Pred.string, 0), symbol (Pred.email, 0),
               interleave (symbol (Pred.strEq "username", 2))
                          (optional (symbol (Pred.strEq "email", 3)))])

-- Given how we parse JSON using a pull-based parser, we have to add tags, so it is translated to:

open Pred

def example_translated_jsonschema : Grammar 7 Pred := Grammar.mk
  (start := (symbol (tagEq "object", 4)))
  (prods := #v[emptystr, starAny, symbol (string, 0), symbol (email, 0)
    , (interleave (symbol (strEq "content", 2))
                  (optional (symbol (strEq "author", 5))))
    , (symbol (tagEq "object", 6))
    , (interleave (symbol (strEq "username", 2))
                  (optional (symbol (strEq "email", 3))))])

def example_additional_properties :=
  star (symbol (not (or (strEq "content") (strEq "author")), 1))
