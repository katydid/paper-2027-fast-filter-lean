import Lake
open Lake DSL

package verifiedFilter

abbrev packageLinters : Array LeanOption := #[]

abbrev packageLeanOptions :=
  packageLinters

@[default_target]
lean_lib VerifiedFilter where
  leanOptions := packageLeanOptions
  moreServerOptions := packageLinters

lean_lib TestSuiteLib where

lean_exe TestSuite

require "base64-lean" from git "https://github.com/Quoteme/base64-lean" @ "main"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.29.0"
require Regex from git "https://github.com/pandaman64/lean-regex" @ "v4.29.0" / "regex"
