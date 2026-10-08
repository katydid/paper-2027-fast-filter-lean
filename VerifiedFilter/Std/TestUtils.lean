def assert [DecidableEq α] (x y: α) [MonadExcept String m] [Monad m]: m Unit := do
  if x == y then pure () else throw "not equal"
