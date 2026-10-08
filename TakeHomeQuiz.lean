/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

/-
Replace each sorry with a complete Lean proof, and reupload this file by 1pm Friday October 9.

You may only use the tactics from the first two lectures (`exact`, `intro`, `apply`, `specialize`,
`have`, `suffices`, `left`, `right`, `constructor`, `rcases`, `by_contra`, `by_cases`).
Do not use other tactics or term mode (if you know what that is).
-/

example (P Q : Prop) (hP : P) (hQ : P → Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ hP

example (P Q : Prop) (hP : P ∨ Q) (hQ : P → Q) : Q := by
  rcases hP with hp | hq
  · exact hQ hp
  · exact hq

example (P Q : Prop) (hP : P ∧ Q) : P ∨ Q := by
  rcases hP with ⟨hp, hq⟩
  left
  exact hp

example (h : ¬ True) : False := by
  by_contra T
  trivial

example (P : Prop) (hP : P) : ¬ ¬ P := by
  by_contra nP
  exact nP hP
