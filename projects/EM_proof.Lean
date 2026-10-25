module

public import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction
public import Mathlib.Analysis.Convex.Jensen

-- Θ is the parameter space of θ, E is the latent state space of x
--and Y is the fixed observation space of y
variable {Θ E Y: Type*}
variable [Fintype E] [Nonempty E]

-- I define joint as the function from the parameter space
-- to a particular PMF parameterised by that theta
variable (joint: Θ → PMF (E × Y))

-- We will assume that joint is non-zero everywhere-
variable (hpos: ∀ θ x y, joint θ (x, y) > 0)

/- Marginal distribution of y, parameterised by θ -/
def marginal (θ: Θ) (y: Y): ENNReal :=
∑ x joint θ (x, y)

/- Posterior distribution of x given y, parameterised by θ -/
def posterior (θ: Θ) (x: E) (y: Y): ENNReal :=
joint θ (x, y) / marginal θ y

/- If joint is nowhere negative, the marginal is also nowhere negative-/
theorem pos_marginal (θ: Θ) (y: Y) (h: hpos) : marginal θ y > 0 := by
sorry
