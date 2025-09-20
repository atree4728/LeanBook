import LeanBook.NatCommMonoid.Induction

example : 0 + (n + 0) = n := by
  fail_if_success simp
  rw [MyNat.add_zero, MyNat.zero_add]

attribute [simp] MyNat.add_zero MyNat.zero_add

example : 0 + (n + 0) = n := by
  simp

attribute [simp] MyNat.add_succ
