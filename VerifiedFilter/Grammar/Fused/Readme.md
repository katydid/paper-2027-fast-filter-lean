# Fused

This folder contains the Fused Katydid algorithm with parsing and memoization.
This implementation has not been proved correct.
We leave this as future work.

* [Fused](./Fused.lean) contains the algorithm used by derive, validate and filter.
* [FusedNoAlloc](./FusedNoAlloc.lean) contains the algorithm that avoids all heap allocation, used by derive, validate and filter.