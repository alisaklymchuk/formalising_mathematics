module

public import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.BigOperators

#check Finset.sum_pos_iff

open scoped ENNReal
set_option linter.unusedSectionVars false

structure EMModel (θ E Y: Type*) [Fintype E] where
  joint {Θ} : Θ → PMF (E × Y)
  joint_pos: ∀ (θ : Θ) (x : E) (y : Y), joint θ (x, y) > 0
