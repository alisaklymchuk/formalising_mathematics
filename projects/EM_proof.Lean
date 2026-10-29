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

-- PROBABILITY MEASURES DEFINITIONS AND LEMMAS

-- Θ is the parameter space of θ, E is the latent state space of x
--and Y is the fixed observation space of y
variable {Θ E Y : Type*}
variable [Fintype E] [Nonempty E]

-- I define joint as the function from the parameter space
-- to a particular PMF parameterised by that theta
variable (joint : Θ → PMF (E × Y))

-- We will assume that joint is non-zero everywhere-
variable (hpos : ∀ θ x y, joint θ (x, y) > 0)

/- Marginal distribution of y, parameterised by θ -/
noncomputable def marginal (joint : Θ → PMF (E × Y)) (θ : Θ) (y : Y) : ℝ≥0∞ :=
∑ x, joint θ (x, y)

/- Posterior distribution of x given y, parameterised by θ -/
noncomputable def posterior (joint : Θ → PMF (E × Y)) (θ : Θ) (x : E) (y : Y) : ℝ≥0∞ :=
  joint θ (x, y) / marginal joint θ y

#check posterior (joint : Θ → PMF (E × Y))

/- If joint is nowhere negative, the marginal is also nowhere negative-/
theorem pos_marginal (joint : Θ → PMF (E × Y))
(hjpos : ∀ θ x y, joint θ (x, y) > 0)
(hE : Nonempty E)
(θ : Θ) (y : Y) : marginal joint θ y > 0 := by
  unfold marginal
  change 0 < ∑ x ∈ Finset.univ, joint θ (x, y)
  rw [Finset.sum_pos_iff]
  rcases hE with ⟨x0⟩
  use x0
  constructor
  · exact Finset.mem_univ x0
  · exact hjpos θ x0 y

theorem noninf_marginal (joint : Θ → PMF (E × Y))
(θ : Θ) (y : Y) : marginal joint θ y ≠ ∞ := by
  unfold marginal
  rw [ENNReal.sum_ne_top]
  intro x hx
  exact PMF.apply_ne_top (joint θ) (x, y)


#check PMF.apply_ne_top


theorem pos_posterior (joint : Θ → PMF (E × Y))
(hjpos : ∀ θ x y, joint θ (x, y) > 0)
(hE : Nonempty E)
(θ : Θ) (x : E) (y : Y) : posterior joint θ x y > 0 := by
  unfold posterior
  apply ENNReal.div_pos
  · apply ne_of_gt
    exact hjpos θ x y
  · exact noninf_marginal (joint : Θ → PMF (E × Y)) θ y

noncomputable def Q (θ θ_t : Θ) (y : Y) : ℝ :=
  ∑ x : E,
  (posterior joint θ_t x y).toReal * Real.log (joint θ (x, y)).toReal



-- Q-FUNCTION AND EM SEQUENCE DEFINITIONS

/- The Q-function is defined as
Q(θ', θ)=∑ (x ∈ E) p_θ(x | y) log p_θ'(x,y).
where θ is is the current parameter, used to calculate the posterior
and θ' is the candidate next parameter
(the EM algorithm then takes the argmax over θ' as the next parameter in the sequence) -/
