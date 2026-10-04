-- Regex.derive2 shows how a normal derivative function can be uncurried and memoized.
-- This is a claim made in the Introduction of the paper and we backup by defining the instance.

import VerifiedFilter.Std.Memoize.Memoize

import VerifiedFilter.Regex.Regex

namespace VerifiedFilter.Regex.Memoize

def Regex.derive2 (Φ: σ → α → Bool) (ra: Regex σ × α): Regex σ :=
  Regex.derive Φ ra.1 ra.2

def MemTable.derive2 (Φ: σ → α → Bool) [DecidableEq σ] [Hashable σ] [DecidableEq α] [Hashable α]
  [Monad m] [monadState: MonadState (MemTable (Regex.derive2 Φ)) m]
  (param: Regex σ × α): m { res // res = Regex.derive2 Φ param } :=
  MemTable.call (Regex.derive2 Φ) param

instance [DecidableEq σ] [Hashable σ] [DecidableEq α] [Hashable α] (Φ: σ → α → Bool)
  [Monad m] [MonadState (MemTable (Regex.derive2 Φ)) m]: Memoize (Regex.derive2 Φ) m where
  call param := MemTable.derive2 Φ param
