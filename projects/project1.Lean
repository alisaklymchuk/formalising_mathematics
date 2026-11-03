/-
Copyright (c) 2026 Alisa Klymchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alisa Klymchuk
-/

module

public import Mathlib.Tactic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

/-!
# EM Algorithm

This file formalises the monotonicity of the marginal log-likelihood
under the Expectation-Maximisation algorithm for finite discrete
latent-variable models.

## Mathematical setting

We consider a finite, nonempty latent state space `E`, an observation
space `Y`, and a parameter space `Θ`.

For each parameter, the model specifies a joint probability mass
function over `E × Y`. We assume strict positivity of the joint
probability mass function, which ensures the marginal and posterior
probabilities are also strictly positive.

The marginal likelihood is obtained by summing over the latent states,
and the posterior distribution is defined using Bayes' rule.

## Main result

We prove that the marginal log-likelihood is non-decreasing along
a sequence of parameter updates that maximise the Q-function.
-/

variable {Θ E Y : Type*} [Fintype E] [Nonempty E]

/-- A finite latent-variable model with a strictly positive joint probability mass function. -/
structure EMModel (Θ E Y : Type*) [Fintype E] [Nonempty E] where
  /-- joint defines the joint probability mass function for a given parameter θ -/
  jointennreal : Θ → PMF (E × Y)
  /-- I assume that the PMFs are always positive (i. e. non-zero) -/
  joint_pos_ennreal : ∀ (θ : Θ) (x : E) (y : Y), 0 < jointennreal θ (x, y)

/-- Real-valued joint -/
noncomputable def EMModel.joint (M : EMModel Θ E Y)
(θ : Θ) (x : E) (y : Y) : ℝ :=
(M.jointennreal θ (x, y)).toReal

/-- Marginal likelihood of observation y under the model parameter θ -/
noncomputable def EMModel.marginal (M : EMModel Θ E Y)
(θ : Θ) (y : Y) : ℝ :=
∑ x : E, M.joint θ x y

/-- The marginal log-likelihood of observation y under parameter θ. -/
noncomputable def EMModel.loglik (M : EMModel Θ E Y)
    (θ : Θ) (y : Y) : ℝ :=
  Real.log (M.marginal θ y)

/-- The posterior distribution of the latent variable x given the obervation y
under the model parameter θ -/
noncomputable def EMModel.posterior (M : EMModel Θ E Y)
(θ : Θ) (x : E) (y : Y) : ℝ :=
M.joint θ x y / M.marginal θ y

/-- The Q function is the expectation wrt to the posterior under parameter θ_t (current best)
of the marginal log-likelihood under parameter θ
(next iteration of the algorithm finds the θ that maximizes Q)
Q(θ, θ_old)=∑ (x ∈ E) p_{θ_old}(x | y) log p_θ(x,y). -/
noncomputable def EMModel.Q (M : EMModel Θ E Y)
(θ θ_old : Θ) (y : Y) : ℝ :=
∑ x : E, M.posterior θ_old x y * Real.log (M.joint θ x y)

/-- IsQMaximizingStep defines what it means for a θ update to maximize the Q-function. -/
def EMModel.IsQMaximizer (M : EMModel Θ E Y)
(y : Y) (θ_new θ_old : Θ) : Prop :=
  ∀ θ : Θ, M.Q θ θ_old y ≤ M.Q θ_new θ_old y

/-- IsQMaximizingSeq defines what it means for a sequence of θs to be a sequence of Q-maximizers -/
def EMModel.IsQMaximizingSeq (M : EMModel Θ E Y)
(y : Y) (θs : ℕ → Θ) : Prop :=
  ∀ t : ℕ, M.IsQMaximizer y (θs (t + 1)) (θs t)

/-- The real-valued joint probability is strictly positive. -/
theorem EMModel.pos_joint (M : EMModel Θ E Y)
  (θ : Θ) (x : E) (y : Y) :
  0 < M.joint θ x y := by
  unfold EMModel.joint
  apply ENNReal.toReal_pos
  · exact ne_of_gt (M.joint_pos_ennreal θ x y)
  · exact PMF.apply_ne_top (M.jointennreal θ) (x, y)

/-- Marginal distribution is strictly positive -/
theorem EMModel.pos_marginal (M : EMModel Θ E Y)
(θ : Θ) (y : Y) : 0 < M.marginal θ y := by
  unfold EMModel.marginal
  apply Finset.sum_pos
  · intro x hx
    exact M.pos_joint θ x y
  · exact Finset.univ_nonempty

/-- Posterior distribution is strictly positive -/
theorem EMModel.pos_posterior (M : EMModel Θ E Y)
(θ : Θ) (x : E) (y : Y) : 0 < M.posterior θ x y := by
  unfold EMModel.posterior
  apply div_pos
  · exact M.pos_joint θ x y
  · exact M.pos_marginal θ y

/-- The sum over x ∈ E of posterior distribution is 1
(Since posterior is a probability distribution of x, and PMF sum to one) -/
theorem EMModel.posterior_sum_to_one (M : EMModel Θ E Y)
(θ : Θ) (y : Y) : ∑ x : E, M.posterior θ x y = 1 := by
  unfold EMModel.posterior
  rw [← Finset.sum_div]
  unfold EMModel.marginal
  rw [div_self]
  · rw [← EMModel.marginal]
    exact ne_of_gt (M.pos_marginal θ y)

/-- The joint distribution that be multiplied and divided by posterior
(This is needed at the begginning of the proof) -/
theorem EMModel.mul_div_posterior (M : EMModel Θ E Y)
(θ θ_old : Θ) (x : E) (y : Y) :
M.joint θ x y = M.posterior θ_old  x y *
(M.joint θ x y / M.posterior θ_old x y) := by
  symm
  rw [mul_comm]
  apply div_mul_cancel₀
  apply ne_of_gt
  exact M.pos_posterior θ_old x y

/-- By definition of posterior (equivalent to Bayes rule) and property of log,
log p(x | y) = log (p(x, y) / p(y)) = log p(x, y) - logp(y) -/
theorem EMModel.log_bayes (M : EMModel Θ E Y)
(θ : Θ) (x : E) (y : Y) :
Real.log (M.posterior θ x y) =
Real.log (M.joint θ x y) - M.loglik θ y := by
  unfold EMModel.posterior EMModel.loglik
  rw [Real.log_div]
  · exact ne_of_gt (M.pos_joint θ x y)
  · exact ne_of_gt (M.pos_marginal θ y)

/-- Weighted Jensen's inequality applied to the concave log function,
weights p_{θ_old}(x | y) and  argument p_θ(x, y) / p_{θ_old}(x | y) -/
theorem EMModel.jensen_log_posterior (M : EMModel Θ E Y)
(θ θ_old : Θ) (y : Y) :
(∑ x : E, M.posterior θ_old x y
* Real.log (M.joint θ x y / M.posterior θ_old x y)) ≤
Real.log (∑ x : E, M.posterior θ_old x y
* (M.joint θ x y / M.posterior θ_old x y)) := by
  have hf : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log :=
  StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi
  apply hf.le_map_sum (t := Finset.univ)
    (w := fun x : E => M.posterior θ_old x y)
    (p := fun x : E => M.joint θ x y / M.posterior θ_old x y)
  · intro x hx
    exact le_of_lt (M.pos_posterior θ_old x y)
  · exact M.posterior_sum_to_one θ_old y
  · intro x hx
    rw [Set.mem_Ioi]
    apply div_pos
    · exact M.pos_joint θ x y
    · exact M.pos_posterior θ_old x y

/-- Main result: The marginal log-likelihood is non-decreasing under an EM sequence of θ updates -/
theorem EMModel.loglik_mono (M : EMModel Θ E Y)
(y : Y) (θs : ℕ → Θ) (hseq : M.IsQMaximizingSeq y θs) {t : ℕ} :
M.loglik (θs t) y ≤ M.loglik (θs (t+1)) y := by
  unfold EMModel.loglik
  unfold EMModel.marginal
  have hfactor : (∑ x : E, M.joint (θs (t + 1)) x y) =
  ∑ x : E, M.posterior (θs t) x y * (M.joint (θs (t + 1)) x y /
    M.posterior (θs t) x y) := by
    apply Finset.sum_congr
    · rfl
    · intro x hx
      exact M.mul_div_posterior (θs (t+1)) (θs t) x y
  rw [hfactor]
  grw [← M.jensen_log_posterior (θs (t+1)) (θs t) y]
  have hlogdiv (x : E) :
  Real.log (M.joint (θs (t + 1)) x y / M.posterior (θs t) x y) =
  Real.log (M.joint (θs (t + 1)) x y) -
  Real.log (M.posterior (θs t) x y) := by
    rw [Real.log_div (ne_of_gt (M.pos_joint (θs (t + 1)) x y))
    (ne_of_gt (M.pos_posterior (θs t) x y))]
  simp_rw [hlogdiv, mul_sub, M.log_bayes (θs t) _ y]
  simp_rw [mul_sub, ← sub_add]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, M.posterior_sum_to_one (θs t) y, one_mul]
  conv_rhs =>
    lhs
    lhs
    change M.Q (θs (t+1)) (θs t) y
  conv_rhs =>
    lhs
    rhs
    change M.Q (θs t) (θs t) y
  conv_lhs =>
    change Real.log (M.marginal (θs t) y)
    change M.loglik (θs t) y
  have hQ : M.Q (θs t) (θs t) y ≤ M.Q (θs (t+1)) (θs t) y :=
    hseq t (θs t)
  linarith

#lint
