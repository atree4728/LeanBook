#check Nat.add_zero

#check Nat.add_zero 0
#check Nat.add_zero 42

#check (Nat.add_zero : (n : Nat) → n + 0 = n)

example : (∀ n : Nat, n + 0 = n) = ((n : Nat) → n + 0 = n) := by rfl

inductive Vect (α : Type) : Nat → Type where
  | nil : Vect α 0
  | cons (a : α) (v : Vect α n) : Vect α (n + 1)

example : (α : Type) × α := ⟨Nat, 1⟩

example : List ((α : Type) × α) := [⟨Nat, 42⟩, ⟨Bool, false⟩]

example : {α : Type} → {n : Nat} → (a : α) → (v : Vect α n) → Vect α (n + 1) := by
  intro α n a v
  exact (.cons a v)
