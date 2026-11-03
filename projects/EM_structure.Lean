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
-/

open scoped ENNReal
--set_option linter.unusedSectionVars false

variable {Θ E Y : Type*} [Fintype E] [Nonempty E]

/-- A finite latent-variable model with a strictly positive joint probability mass function. -/
structure EMModel (Θ E Y : Type*) [Fintype E] [Nonempty E] where
  /-- joint defines the joint probability mass function for a given parameter θ -/
  joint_ennreal : Θ → PMF (E × Y)
  /-- I assume that the PMFs are always positive (i. e. non-zero) -/
  joint_pos_ennreal : ∀ (θ : Θ) (x : E) (y : Y), 0 < joint_ennreal θ (x, y)

/-- Real-valued joint -/
noncomputable def EMModel.joint (M : EMModel Θ E Y)
(θ : Θ) (x : E) (y : Y) : ℝ :=
(M.joint_ennreal θ (x, y)).toReal

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
(θ θ_old : Θ) (y : Y) :=
∑ x : E, M.posterior θ_old x y * Real.log (M.joint θ x y)

/-- IsQMaximizingStep defines what it means for a θ update to maximize the Q-function. -/
def EMModel.IsQMaximizer (M : EMModel Θ E Y)
(y : Y) (θ_new θ_old : Θ) : Prop :=
  ∀ θ : Θ, M.Q θ θ_old y ≤ M.Q θ_new θ_old y

/-- IsQMaximizingSeq defines what it means for a sequence of θs to be a sequence of Q-maximizers -/
def EMModel.IsQMaximizingSeq (M : EMModel Θ E Y)
(y : Y) (θs : ℕ → Θ) : Prop :=
  ∀ t : ℕ, M.IsQMaximizer y (θs t) (θs (t+1))

#check Finset.sum_pos_iff

#check inferInstance

/-- Below I use the positive joint assumption and finiteness of E to prove that
the marginal is positive and finite and the posterior is positive, finite and
∑ (x : E) p_θ(x | y) = 1, i. e. the posterior is a valid probability distribution
 The real-valued joint probability is strictly positive. -/
theorem EMModel.pos_joint (M : EMModel Θ E Y)
  (θ : Θ) (x : E) (y : Y) :
  0 < M.joint θ x y := by
  unfold EMModel.joint
  apply ENNReal.toReal_pos
  · exact ne_of_gt (M.joint_pos_ennreal θ x y)
  · exact PMF.apply_ne_top (M.joint_ennreal θ) (x, y)


theorem EMModel.pos_marginal (M : EMModel Θ E Y)
(θ : Θ) (y : Y) : 0 < M.marginal θ y := by
  unfold EMModel.marginal
  apply Finset.sum_pos
  · intro x hx
    exact M.pos_joint θ x y
  · exact Finset.univ_nonempty

theorem EMModel.pos_posterior (M : EMModel Θ E Y)
(θ : Θ) (x : E) (y : Y) : 0 < M.posterior θ x y := by
  unfold EMModel.posterior
  apply div_pos
  · exact M.pos_joint θ x y
  · exact M.pos_marginal θ y

theorem EMModel.posterior_sum_to_one (M : EMModel Θ E Y)
(θ : Θ) (y : Y) : ∑ x : E, M.posterior θ x y = 1 := by
  unfold EMModel.posterior
  rw [← Finset.sum_div]
  unfold EMModel.marginal
  rw [div_self]
  · rw [← EMModel.marginal]
    exact ne_of_gt (M.pos_marginal θ y)

theorem EMModel.mul_div_posterior (M : EMModel Θ E Y) (θ θ_old : Θ) (x : E) (y : Y) :
M.joint θ x y =  M.posterior θ_old  x y * (M.joint θ x y / M.posterior θ_old x y) := by
  symm
  rw [mul_comm]
  apply div_mul_cancel₀
  apply ne_of_gt
  exact M.pos_posterior θ_old x y

theorem EMModel.log_posterior_eq (M : EMModel Θ E Y) (θ : Θ) (x : E) (y : Y) :
Real.log (M.posterior θ x y) = Real.log (M.joint θ x y) - M.loglik θ y := by
  unfold EMModel.posterior EMModel.loglik
  rw [Real.log_div]
  · exact ne_of_gt (M.pos_joint θ x y)
  · exact ne_of_gt (M.pos_marginal θ y)

theorem EMModel.jensen_log_posterior (M : EMModel Θ E Y) (θ θ_old : Θ) (y : Y) :
(∑ x : E, M.posterior θ_old x y * Real.log (M.joint θ x y / M.posterior θ_old x y)) ≤
Real.log (∑ x : E, M.posterior θ_old x y * (M.joint θ x y / M.posterior θ_old x y)) := by
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
theorem EMModel.loglik_mono (M: EMModel Θ E Y)
(y : Y) (θs : ℕ → Θ) (hseq : M.IsQMaximizingSeq y θs) (t : ℕ) :
M.loglik (θs t) y ≤ M.loglik (θs (t+1)) y := by
  unfold EMModel.loglik
  unfold EMModel.marginal
  have hfactor : (∑ x : E, M.joint (θs (t + 1)) x y) =
  ∑ x : E, M.posterior (θs t) x y * (M.joint (θs (t + 1)) x y /
    M.posterior (θs t) x y) := by
    apply Finset.sum_congr
    rfl
    intro x hx
    exact M.mul_div_posterior (θs (t+1)) (θs t) x y

  let w : E → ℝ := fun x =>M.posterior (θs t) x y
  let a : E → ℝ := fun x =>
    ((M.joint (θs (t + 1))) x y) / (M.posterior (θs t) x y)

  have h0 : ∀ x ∈ Finset.univ, 0 ≤ w x := by
    intro x hx
    positivity


  have h1 : ∑ x : E, w x = 1 := by
    unfold w
    rw [← ENNReal.toReal_sum (fun x hx => M.finite_posterior (θs t) x y)]
    rw [M.posterior_sum_to_one (θs t) y]
    rfl

  have hf : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log :=
    StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi

  have hmem : ∀ x ∈ Finset.univ, a x ∈ Set.Ioi (0 : ℝ) := by
    intro x hx
    unfold a
    rw [Set.mem_Ioi]
    apply div_pos
    · exact M.joint_toReal_pos (θs (t + 1)) x y
    · exact M.posterior_toReal_pos (θs t) x y


  conv_rhs =>
    rw [hfactor, ENNReal.toReal_sum]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div]











#check Finset.sum_congr
#check Real.strictConcaveOn_log_Ioi
#check ConcaveOn.le_map_sum

#lint
