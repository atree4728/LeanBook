theorem one_add_one_eq_two : 1 + 1 = 2 := by
  rfl

#check one_add_one_eq_two

def idOnNat : Nat → Nat := by?
  intro n
  exact n

example (P Q : Prop) (p : P) : Q → P := fun _ => p
