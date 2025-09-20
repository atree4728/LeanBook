import LeanBook.FirstProof.NaturalNumber

def MyNat.ofNat (n : Nat) : MyNat :=
  match n with
  | 0 => zero
  | n + 1 => succ (ofNat n)

@[default_instance]
instance (n : Nat) : OfNat MyNat n where
  ofNat := MyNat.ofNat n

#check 0

instance : Add MyNat where
  add := .add

#check 1 + 1

#eval 2 + 0

def MyNat.toNat (n : MyNat) : Nat :=
  match n with
  | zero => 0
  | succ n => 1 + toNat n

instance : Repr MyNat where
  reprPrec n _ := repr n.toNat

#eval 2 + 0

example (n : MyNat) : n + 0 = n := by rfl
