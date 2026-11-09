/-
Copyright (c) 2026 Illia Derevianko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Illia Derevianko
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Dominated convergence theorem

We prove the dominated convergence theorem for real-valued functions: if `fₙ → F` a.e. and
`|fₙ| ≤ g` with `g` integrable, then `∫ |fₙ - F| → 0` and `∫ fₙ → ∫ F`.

## Main results

* `integrable_of_dominated`: the `fₙ` and `F` are integrable.
* `fatou_lemma`: Fatou's lemma for `ℝ≥0∞`-valued functions.
* `limit_of_dominated`: `∫ |fₙ - F| ∂μ → 0`.
* `inequality_of_dominated`: `|∫ fₙ ∂μ - ∫ F ∂μ|≤ ∫ |fₙ - F| ∂μ`.
* `dom_conv`: the dominated convergence theorem.
-/

open scoped ENNReal
open MeasureTheory
open Filter Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  {g : X → ℝ≥0∞} {F : X → ℝ} {f : ℕ → X → ℝ}

/-- If `|fₙ| ≤ g` for all `n` and `fₙ → F` almost everywhere, then the limit is also
dominated: `‖F‖ₑ ≤ g` almost everywhere. -/
theorem ae_F_bound_of_dominated
    (hfg : ∀ n : ℕ, ∀ x : X, ENNReal.ofReal |f n x| ≤ g x)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    ∀ᵐ x ∂μ, ‖F x‖ₑ ≤ g x := by
  filter_upwards [hc] with x hc'
  have hlim : Tendsto (fun n ↦ ‖f n x‖ₑ) atTop (𝓝 ‖F x‖ₑ) :=
    hc'.enorm
  refine le_of_tendsto' hlim fun n ↦ ?_
  rw [Real.enorm_eq_ofReal_abs]
  specialize hfg n x
  exact hfg

/-- If `|fₙ| ≤ g` for all `n` and `fₙ → F` almost everywhere, then `‖fₙ - F‖ₑ ≤ 2g`
almost everywhere, for every `n`. -/
theorem ae_fnF_bound_of_dominated
    (hc : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x)))
    (hfg : ∀ n : ℕ, ∀ x : X, ENNReal.ofReal |f n x| ≤ g x) :
    ∀ n, ∀ᵐ x ∂μ, ‖(f n - F) x‖ₑ ≤ 2 * g x := by
  -- F dominated by g a.e.
  have hFg : ∀ᵐ x ∂μ, ‖F x‖ₑ ≤ g x := ae_F_bound_of_dominated hfg hc
  intro n
  filter_upwards [hFg] with x hx
  specialize hfg n x
  rw [← Real.enorm_eq_ofReal_abs] at hfg
  calc ‖(f n - F) x‖ₑ ≤ ‖f n x‖ₑ + ‖F x‖ₑ := enorm_sub_le
  _ ≤ g x + g x := add_le_add hfg hx
  _ = 2 * g x := (two_mul (g x)).symm

/-- If each `fₙ` and `F` are measurable, `|fₙ| ≤ g` with `g` integrable, and `fₙ → F`
almost everywhere, then every `fₙ` and the limit `F` are integrable. -/
theorem integrable_of_dominated
    (hF : Measurable F)
    (hfn : ∀ n, Measurable (f n))
    (hfg : ∀ n : ℕ, ∀ x : X, ENNReal.ofReal |f n x| ≤ g x)
    (hg_int : Integrable g μ)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    (∀ n : ℕ, Integrable (f n) μ) ∧ Integrable F μ := by
  rcases hg_int with ⟨_, hg_fin⟩
  constructor
  · intro m
    refine ⟨?_, ?_⟩
    · specialize hfn m
      exact Measurable.aestronglyMeasurable hfn
    · specialize hfg m
      have hae : ∀ᵐ x ∂μ, ‖f m x‖ₑ ≤ g x := by
        apply Eventually.of_forall
        intro x
        rw [Real.enorm_eq_ofReal_abs]
        specialize hfg x
        exact hfg
      exact HasFiniteIntegral.mono'_enorm hg_fin hae
  · refine ⟨?_, ?_⟩
    · exact Measurable.aestronglyMeasurable hF
    · exact HasFiniteIntegral.mono'_enorm hg_fin (ae_F_bound_of_dominated hfg hc)

/-- If `g` has finite integral, then so does `2g`: `∫⁻ 2g ∂μ ≠ ∞`. -/
theorem lintegral_two_mul_ne_top
    (hg_fin : HasFiniteIntegral g μ) :
    ∫⁻ x, 2 * g x ∂μ ≠ ∞ := by
  rw [lintegral_const_mul' 2 g ENNReal.ofNat_ne_top]
  have hg_int_ninf : ∫⁻ x, g x ∂μ ≠ ∞ := LT.lt.ne_top hg_fin
  exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top hg_int_ninf

/-- **Fatou's lemma**: for a sequence of measurable functions `fₙ : X → ℝ≥0∞`,
`∫⁻ liminf fₙ ∂μ ≤ liminf ∫⁻ fₙ ∂μ`. -/
theorem fatou_lemma
    (f : ℕ → X → ℝ≥0∞)
    (hfn : ∀ n, Measurable (f n)) :
    ∫⁻ x, liminf (fun n ↦ f n x) atTop ∂μ ≤ liminf (fun n ↦ ∫⁻ x, f n x ∂μ) atTop := by
  let G : ℕ → X → ℝ≥0∞ := fun n x ↦ ⨅ k ≥ n, f k x
  have hg : ∀ n : ℕ, Measurable (G n) := by
    intro n
    apply Measurable.iInf
    intro k
    apply Measurable.iInf
    intro _
    specialize hfn k
    exact hfn
  have hi : ∀ n : ℕ, ∀ k ≥ n, ∀ x : X, G n x ≤ f k x := by
    intro n k hkn x
    exact iInf₂_le k hkn
  have hg_int : ∀ n : ℕ, ∫⁻ x, G n x ∂μ ≤ ⨅ k ≥ n, ∫⁻ x, f k x ∂μ := by
    intro n
    apply le_iInf₂
    intro i hin
    specialize hi n i hin
    exact lintegral_mono hi
  have hgm : Monotone G := by
    intro m n hmn x
    apply biInf_mono
    intro k hkn
    exact Nat.le_trans hmn hkn
  -- Replacing sequence limit with its limit as we know that
  -- the limit of an increasing sequence in ℝ≥0∞ is it's supremum.
  -- This also matches Mathlib's statement of monotone convergence
  calc ∫⁻ x, liminf (fun n ↦ f n x) atTop ∂μ
      = ∫⁻ x, ⨆ n, G n x ∂μ := by simp only [liminf_eq_iSup_iInf_of_nat, G]
    _ = ⨆ n, ∫⁻ x, G n x ∂μ := lintegral_iSup hg hgm
    _ ≤ ⨆ n, ⨅ k ≥ n, ∫⁻ x, f k x ∂μ := iSup_mono hg_int
    _ = liminf (fun n ↦ ∫⁻ x, f n x ∂μ) atTop := by rw [liminf_eq_iSup_iInf_of_nat]

/-- If each `fₙ` and `F` are integrable, then `|∫ fₙ - ∫ F| ≤ ∫ |fₙ - F|` for every `n`. -/
theorem inequality_of_dominated
    (hf_int : ∀ n : ℕ, Integrable (f n) μ)
    (hF_int : Integrable F μ) :
    ∀ n : ℕ, |∫ x, f n x ∂μ - ∫ x, F x ∂μ| ≤ ∫ x, |f n x - F x| ∂μ := by
  intro n
  specialize hf_int n
  calc |∫ x, f n x ∂μ - ∫ x, F x ∂μ|
    = |∫ x, f n x - F x ∂μ| := by rw [integral_sub hf_int hF_int]
  _ = |∫ x, (f n - F) x ∂μ| := by simp only [Pi.sub_apply]
  _ ≤ ∫ x, |f n - F| x ∂μ := abs_integral_le_integral_abs

/-- Under the hypotheses of the dominated convergence theorem,
`∫ |fₙ - F| ∂μ → 0`. -/
theorem limit_of_dominated
    (hg_meas : Measurable g)
    (hF_meas : Measurable F)
    (hfn_meas : ∀ n, Measurable (f n))
    (hg_dom : ∀ n : ℕ, ∀ x : X, ENNReal.ofReal |f n x| ≤ g x)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x)))
    (hg_int : Integrable g μ) :
    Tendsto (fun n ↦ ∫ x, |(f n - F) x| ∂μ) atTop (𝓝 0) := by
  have hid : (∀ n : ℕ, Integrable (f n) μ) ∧ Integrable F μ :=
    integrable_of_dominated hF_meas hfn_meas hg_dom hg_int hc
  rcases hid with ⟨hf_int, hF_int⟩
  -- ‖fₙ - F‖ₑ ≤ 2g a.e.
  have h2g_dom : ∀ n, ∀ᵐ x ∂μ, ‖(f n - F) x‖ₑ ≤ 2 * g x :=
    ae_fnF_bound_of_dominated hc hg_dom
  -- ∫ 2g ∂μ ≠ ∞
  have h2g_fin : ∫⁻ x, 2 * g x ∂μ ≠ ∞ := lintegral_two_mul_ne_top hg_int.hasFiniteIntegral
  -- C = ∫ 2g ∂μ, Dₙ = ∫ fₙ - F ∂μ for convenience
  set C : ℝ≥0∞ := ∫⁻ x, 2 * g x ∂μ
  set D : ℕ → ℝ≥0∞ := fun n ↦ ∫⁻ x, ‖(f n - F) x‖ₑ ∂μ
  -- ‖fₙ - F‖ₑ is measurable
  have hfnF : ∀ n, Measurable fun x ↦ ‖(f n - F) x‖ₑ := by
    intro n
    apply Measurable.enorm
    apply Measurable.sub
    · exact hfn_meas n
    · exact hF_meas
  -- ∫ fₙ - F ∂μ ≤ ∫ 2g ∂μ
  have hD_le : ∀ n, D n ≤ C := by
    intro n
    apply lintegral_mono_ae
    exact h2g_dom n
  -- liminf (2g - ‖fₙ - F‖ₑ) = 2g a.e.
  have hlim_pt : ∀ᵐ x ∂μ, liminf (fun n ↦ 2 * g x - ‖(f n - F) x‖ₑ) atTop = 2 * g x := by
    filter_upwards [hc] with x hx
    -- lim ‖fₙ - F‖ₑ = 0
    have h0 : Tendsto (fun n ↦ ‖(f n - F) x‖ₑ) atTop (𝓝 0) := by
      have h : Tendsto (fun n ↦ ‖f n x - F x‖ₑ) atTop (𝓝 ‖(0 : ℝ)‖ₑ) := by
        apply Tendsto.enorm
        apply tendsto_sub_nhds_zero_iff.mpr
        exact hx
      rw [enorm_zero] at h
      exact h
    -- lim (2g - ‖fₙ - F‖ₑ) = 2g - 0
    have h2 : Tendsto (fun n ↦ 2 * g x - ‖(f n - F) x‖ₑ) atTop (𝓝 (2 * g x - 0)) := by
      apply ENNReal.Tendsto.sub
      · exact tendsto_const_nhds
      · exact h0
      · right
        exact ENNReal.zero_ne_top
    rw [h2.liminf_eq]
    exact tsub_zero (2 * g x)
  -- Fatou's lemma applied to 2g - ‖fₙ - F‖ₑ
  have hfatou : ∫⁻ x, liminf (fun n ↦ 2 * g x - ‖(f n - F) x‖ₑ) atTop ∂μ
      ≤ liminf (fun n ↦ ∫⁻ x, 2 * g x - ‖(f n - F) x‖ₑ ∂μ) atTop := by
    apply fatou_lemma
    intro n
    exact (hg_meas.const_mul 2).sub (hfnF n)
  -- ∫ 2g - ‖fₙ - F‖ₑ ∂μ = ∫ 2g ∂μ - ∫ ‖fₙ - F‖ₑ ∂μ (integral linearity)
  have hsub : ∀ n, ∫⁻ x, 2 * g x - ‖(f n - F) x‖ₑ ∂μ = C - D n := by
    intro n
    apply lintegral_sub
    · exact hfnF n
    · exact ne_top_of_le_ne_top h2g_fin (hD_le n)
    · exact h2g_dom n
  rw [lintegral_congr_ae hlim_pt] at hfatou
  simp only [hsub] at hfatou
  rw [ENNReal.liminf_const_sub atTop D h2g_fin] at hfatou
  -- Technicality needed to work with subtraction in ℝ≥0∞
  have hL_le : limsup D atTop ≤ C := by
    apply limsup_le_of_le
    · isBoundedDefault
    · exact Eventually.of_forall hD_le
  -- limsup ∫ ‖fₙ - F‖ₑ ∂μ ≤ 0
  have hL : limsup D atTop ≤ 0 := by
    have h1 : C + limsup D atTop ≤ C + 0 := by
      calc C + limsup D atTop ≤ (C - limsup D atTop) + limsup D atTop := add_le_add hfatou le_rfl
      _ = C := tsub_add_cancel_of_le hL_le
      _ = C + 0 := (add_zero C).symm
    exact (ENNReal.add_le_add_iff_left h2g_fin).mp h1
  -- lim ‖fₙ - F‖ₑ ∂μ = 0
  have hlim : Tendsto D atTop (𝓝 0) := tendsto_of_le_liminf_of_limsup_le zero_le hL
  -- Convert the ∫⁻ integral over ℝ≥0∞ to integral ∫ over ℝ
  have heq : ∀ n, ∫ x, |(f n - F) x| ∂μ = (D n).toReal := by
    intro n
    have h : ∫ x, ‖(f n - F) x‖ ∂μ = (∫⁻ x, ‖(f n - F) x‖ₑ ∂μ).toReal := by
      apply integral_norm_eq_lintegral_enorm
      apply Integrable.aestronglyMeasurable
      exact (hf_int n).sub hF_int
    simp only [Real.norm_eq_abs] at h
    exact h
  simp only [heq]
  -- Convert the integral sequence from ℝ≥0∞ to ℝ
  have h : Tendsto (fun n ↦ (D n).toReal) atTop (𝓝 (ENNReal.toReal 0)) := by
    apply Tendsto.comp (ENNReal.tendsto_toReal ENNReal.zero_ne_top)
    exact hlim
  rw [ENNReal.toReal_zero] at h
  exact h

/-- **Dominated convergence theorem**: let `(X, μ)` be a measure space, let `fₙ : X → ℝ` and
`F : X → ℝ` be measurable with `fₙ → F` almost everywhere, and suppose `|fₙ| ≤ g` for an
integrable `g : X → ℝ≥0∞`. Then `|∫ fₙ - ∫ F| ≤ ∫ |fₙ - F|` for every `n`, and `∫ |fₙ - F| → 0`. -/
theorem dom_conv
    (hg : Measurable g)
    (hg_int : Integrable g μ)
    (hF : Measurable F)
    (hfn : ∀ n, Measurable (f n))
    (hfg : ∀ n : ℕ, ∀ x : X, ENNReal.ofReal |f n x| ≤ g x)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    (∀ n : ℕ, |∫ x, f n x ∂μ - ∫ x, F x ∂μ| ≤ ∫ x, |f n x - F x| ∂μ) ∧
    Tendsto (fun n ↦ ∫ x, |f n x - F x| ∂μ) atTop (𝓝 0) := by
  have hid : (∀ n : ℕ, Integrable (f n) μ) ∧ Integrable F μ :=
    integrable_of_dominated hF hfn hfg hg_int hc
  rcases hid with ⟨hf_int, hF_int⟩
  constructor
  · exact inequality_of_dominated hf_int hF_int
  · exact limit_of_dominated hg hF hfn hfg hc hg_int
