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

/-- A finite latent-variable model with a strictly positive joint probability mass function. -/
structure EMModel (Θ E Y : Type*) [Fintype E] [Nonempty E] where
  /-- joint defines the joint probability mass function for a given parameter θ -/
  joint : Θ → PMF (E × Y)
  /-- I assume that the PMFs are always positive (i. e. non-zero) -/
  joint_pos : ∀ (θ : Θ) (x : E) (y : Y), 0 < joint θ (x, y)

/-- Marginal likelihood of observing data y under the model parameter θ -/
noncomputable def EMModel.marginal (M : EMModel Θ E Y)
(θ : Θ) (y : Y) : ENNReal :=
∑ x : E, M.joint θ (x, y)

/-- The posterior distribution of the latent variable x given the obervation y
under the model parameter θ -/
noncomputable def EMModel.posterior (M : EMModel Θ E Y)
(θ : Θ) (x : E) (y : Y) : ENNReal :=
M.joint θ (x, y) / M.marginal θ y

/-- The Q function is the expectation wrt to the posterior under parameter θ_t (current best)
of the marginal log-likelihood under parameter θ
(next iteration of the algorithm finds the θ that maximizes Q) -/
noncomputable def EMModel.Q (M : EMModel Θ E Y)
(θ θ_t : Θ) (y : Y) :=
∑ x : E, (M.posterior θ_t x y).toReal * Real.log (M.joint θ (x, y)).toReal

/-- IsQMaximizingStep defines what it means for a θ update to maximize the Q-function. -/
def EMModel.IsQMaximizer (M : EMModel Θ E Y)
(y : Y) (θ_new θ_old : Θ) : Prop :=
  ∀ θ : Θ, M.Q θ θ_old y ≤ M.Q θ_new θ_old y

/-- IsQMaximizingSeq defines what it means for a sequence of θs to be a sequence of Q-maximizers -/
def EMModel.IsQMaximizingSeq (M : EMModel Θ E Y)
(y : Y) (θs : ℕ → Θ) : Prop :=
  ∀ t : ℕ, M.IsQMaximizer y (θs t) (θs (t+1))

theorem EMModel.pos_marginal (M : EMModel Θ E Y)
(θ : Θ) (y : Y) : 0 < M.marginal θ y := by
  unfold EMModel.marginal
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

theorem EMModel.pos_posterior (M : EMModel Θ E Y) : ∀ θ x y, 0 < M.posterior θ x y := by
  intro θ x y
  unfold EMModel.posterior
  apply ENNReal.div_pos
  · apply ne_of_gt
    exact M.joint_pos θ x y
  · exact M.noninf_marginal θ y
