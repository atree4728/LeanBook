example : ¬¬P → P := by
  intro nnp
  by_cases h : P
  · exact h
  · contradiction

example : ¬ (P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  case mp =>
    intro h
    by_cases pornp : P
    case pos =>
      right
      intro hq
      exact h ⟨pornp, hq⟩
    case neg =>
      left
      exact pornp
  case mpr =>
    intro hor hand
    cases hor with
    | inl np => exact np hand.left
    | inr nq => exact nq hand.right

example : (P → Q) ↔ (¬ Q → ¬ P) := by
  constructor
  case mp =>
    intro h nq p
    exact nq (h p)
  case mpr =>
    intro h p
    by_cases qnq : Q
    case pos => exact qnq
    case neg =>
      exfalso
      exact (h qnq p)
