example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  intro hor hp
  cases hor with
  | inl hnp =>
    contradiction
  | inr hq =>
    exact hq

example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor <;> intro h
  case mp =>
    constructor <;> intro <;> apply h
    case left hp =>
      left
      exact hp
    case right hq =>
      right
      exact hq
  case mpr =>
    intro h'
    cases h' with
    | inl hp =>
      exact h.left hp
    | inr hq =>
      exact h.right hq

example : ¬ (P ↔ ¬ P) := by
  -- intro h
  suffices nn : ¬¬(P ∨ ¬ P) from by
    intro hiff
    apply nn
    intro hor
    cases hor with
    | inl hp =>
      have : ¬ P := by
        rw [← hiff]
        exact hp
      contradiction
    | inr hnp =>
      apply hnp
      rw [hiff]
      exact hnp

  intro hn
  suffices hnp : ¬ P from by
    have : P ∨ ¬ P := by
      right
      exact hnp
    contradiction
  intro hp
  apply hn
  left
  exact hp
