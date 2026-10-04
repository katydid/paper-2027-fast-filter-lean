-- IfExpr.enter using IfExpr to return a combination of all possible outcomes of Vector.map Φ (enter r)
-- IfExpr.eval Φ then returns the appropriate Vector.
-- If this function is memoized rather than the normal enter, then heap allocations can be avoided.
-- Unfortunately this does result in an exponentially large usage of memory.

import VerifiedFilter.Std.Vector

import VerifiedFilter.Regex.Extract
import VerifiedFilter.Regex.IfExpr.IfExpr
import VerifiedFilter.Regex.SymCount
import VerifiedFilter.Regex.Regex

namespace VerifiedFilter.Regex.Regex

def IfExpr.enter (r: Regex σ): IfExpr σ (symcount r) := IfExpr.mk (extract r).2

#guard IfExpr.enter (or (symbol 'a') (symbol 'b'))
  = IfExpr.expr 'a'
      (IfExpr.expr 'b' (IfExpr.res  #v[true, true]) (IfExpr.res  #v[true, false]))
      (IfExpr.expr 'b' (IfExpr.res  #v[false, true]) (IfExpr.res  #v[false, false]))

#guard (IfExpr.enter (or (symbol 'a') (symbol 'b'))).eval (· == 'a')
  = #v[true, false]
