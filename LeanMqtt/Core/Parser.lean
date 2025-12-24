abbrev Parser (α : Type) := StateT (List UInt8) Option α

theorem parser_app_is_run {α} {l : List UInt8} (p : Parser α) :
  p l = p.run l :=
  rfl
