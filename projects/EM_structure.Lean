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

variable {Θ E Y : Type*} [Fintype E] [Nonempty E]

-- I define joint as the function from the parameter space
-- to a particular PMF parameterised by that theta
-- We will assume that joint is positive everywhere
--(i. e. non-zero, since PMFs are already non-negatives
structure EMModel (Θ E Y : Type*) [Fintype E] [Nonempty E] where
  joint : Θ → PMF (E × Y)
  joint_pos : ∀ (θ : Θ) (x : E) (y : Y), joint θ (x, y) > 0

noncomputable def EMModel.marginal (M : EMModel Θ E Y)
(θ : Θ) (y : Y) : ENNReal :=
∑ x : E, M.joint θ (x, y)

noncomputable def EMModel.posterior (M : EMModel Θ E Y)
(θ : Θ) (x : E) (y : Y) : ENNReal :=
M.joint θ (x, y) / M.marginal θ y

noncomputable def EMmodel.Q (M : EMModel Θ E Y)
(θ θ_t : Θ) (y : Y) :=
∑ x : E, (M.posterior θ_t x y).toReal * Real.log (M.joint θ (x, y)).toReal

theorem EMModel.pos_marginal (M : EMModel Θ E Y)
(θ : Θ) (y : Y) : M.marginal θ y > 0 := by
  unfold EMModel.marginal
  change 0 < ∑ x ∈ Finset.univ, M.joint θ (x, y)
  rw [Finset.sum_pos_iff]
  have hE : Nonempty E := inferInstance
  rcases hE with ⟨x0⟩
  use x0
  constructor
  · exact Finset.mem_univ x0
  · exact M.joint_pos θ x0 y

theorem EMModel.noninf_marginal (M : EMModel Θ E Y) : ∀ θ y, M.marginal θ y ≠ ∞ := by
  unfold EMModel.marginal
  intro θ y
  rw [ENNReal.sum_ne_top]
  intro x hx
  exact PMF.apply_ne_top (M.joint θ) (x, y)

theorem EMModel.pos_posterior (M : EMModel Θ E Y) : ∀ θ x y, M.posterior θ x y > 0 := by
  intro θ x y
  unfold EMModel.posterior
  apply ENNReal.div_pos
  · apply ne_of_gt
    exact M.joint_pos θ x y
  · exact M.noninf_marginal θ y
