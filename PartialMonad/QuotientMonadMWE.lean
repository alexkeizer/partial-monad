
/-- The `Raw` type, let's just take `Option` for the `MWE` -/
def Raw := Option

def Raw.bind : Raw α → (α → Raw β) → Raw β :=
  Option.bind

/-- For simplicity, we're just quotienting through equality -/
def Raw.setoid α : Setoid (Raw α) where
  r := Eq
  iseqv := {
    refl := fun _ => rfl
    symm := Eq.symm
    trans := Eq.trans
  }

/-- Define `Q` as a quotient over `Raw` -/
def Q (α : Type) := Quotient (Raw.setoid α)

/-- Now, how do I actually define `bind` over `Q`? -/
def Q.bind (x : Q α) (f : α → Q β) : Q β :=
  let fx (x : Raw α) : Q β :=
    _
  Quotient.liftOn x fx _
--                     ^ `application type mismatch` (i.e., `f` is not a quotient)
