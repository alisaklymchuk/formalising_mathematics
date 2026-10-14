module

import Mathlib.Tactic

example (P Q : Prop) (hP : P) (hQ : P → Q) : P ∧ Q := by
  specialize hQ hP
  constructor
  · exact hP
  · exact hQ

example (P Q : Prop) (hP : P ∨ Q) (hQ : P → Q) : Q := by
  rcases hP with hP | hQ
  · apply hQ
    exact hP
  · exact hQ

example (P Q : Prop) (hP : P ∧ Q) : P ∨ Q := by
  rcases hP with ⟨hP, hQ⟩
  left
  exact hP

example (h : ¬ True) : False := by
  apply h
  exact trivial

example (P : Prop) (hP : P) : ¬ ¬ P := by
  by_contra nP
  apply nP
  exact hP
