@[extern "lean_string_dec_lt", implicit_reducible]
def String.decLt (a b : String) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toList < b.toList))

@[extern "lean_string_dec_le", implicit_reducible]
def String.decLe (a b : String) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toList ≤ b.toList))

attribute [instance] String.decLt String.decLe
