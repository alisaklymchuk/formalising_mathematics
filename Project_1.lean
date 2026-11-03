module

public import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Defs

variable {p : ℕ} {a : ZMod p}
variable {hanot0 : a ≠ 0}
variable [Fact (Nat.Prime p)]

-- Elaborate set builder notation for Finset. {x | p x} is elaborated as Finset.filter
-- (fun x ↦ p x) Finset.univ if the expected type is Finset ?α.

def S : Finset (ZMod p) :=
  Finset.filter (fun x => x ≠ 0) Finset.univ

lemma hnot0 (x : ZMod p) (hx : x ∈ S) : x ≠ 0 := by
  exact (Finset.mem_filter.mp hx).2

def f : ZMod p → ZMod p :=
  fun x => a * x

theorem injective_f {hanot0 : a ≠ 0} : ∀ x y : ZMod p, f (a := a) x = f (a := a) y → x = y := by
  intro x y hfxfy
  unfold f at hfxfy
  exact mul_left_cancel₀ hanot0 hfxfy

theorem bijective_f {hanot0 : a ≠ 0} : Function.Bijective (f (a := a)) := by
  apply Finite.injective_iff_bijective.mp
  exact injective_f (hanot0 := hanot0)

theorem surjective_f {hanot0 : a ≠ 0} : Function.Surjective (f (a := a)) := by
  exact bijective_f (hanot0 := hanot0).2

lemma f_x_in_S {hanot0 : a ≠ 0} (x : ZMod p) (hx : x ∈ S) : f (a := a) x ∈ S := by
  unfold f
  have hxnot0 : x ≠ 0 := by
    exact (Finset.mem_filter.mp hx).2
  have haxnot0 : a * x ≠ 0 := by
    exact mul_ne_zero hanot0 hxnot0
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_univ _
  · exact haxnot0

def P : ZMod p := ∏ x ∈ S, x

lemma P_not_zero : P (p := p) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro x hx
  exact (Finset.mem_filter.mp hx).2

theorem reindexing_prod {hanot0 : a ≠ 0} : ∏ x ∈ S, a * x = P := by
  rw [P]
  apply Finset.prod_bij (fun x _ => f (a := a) x)
  · intro x hx
    exact f_x_in_S (hanot0 := hanot0) x hx
  · intro x hx y hy hfxfy
    apply injective_f (a := a) (hanot0 := hanot0)
    exact hfxfy
  · intro x hx
    have hxnot0 : x ≠ 0 := by
      exact (Finset.mem_filter.mp hx).2
    rcases surjective_f (a := a) (hanot0 := hanot0) x with ⟨y, hy⟩
    use y
    constructor
    · exact hy
    · have hynot0 : y ≠ 0 := by
        by_contra hyzero
        rw [hyzero] at hy
        unfold f at hy
        simp only [mul_zero] at hy
        apply hxnot0
        rw [hy]
      unfold S
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · exact hynot0
  · intro x hx
    rfl

lemma prod_eq_pow_mul_P : (∏ x ∈ S, a * x) = a ^ S (p := p).card * P := by
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  rfl

lemma S_eq : S = Finset.univ \ ({0} : Finset (ZMod p)) := by
  unfold S
  ext x
  simp

lemma card_S : S (p := p).card = p - 1 := by
  rw [S_eq, Finset.card_sdiff]
  simp

lemma main_eq {hanot0 : a ≠ 0} : P = a ^ (p - 1) * P := by
  rw [← card_S, ← prod_eq_pow_mul_P]
  exact reindexing_prod (hanot0 := hanot0).symm

theorem Fermats_little_theorem {hanot0 : a ≠ 0} : a ^ (p - 1) = 1 := by
  suffices hP : a ^ (p - 1) * P = P by
    apply mul_right_cancel₀ P_not_zero
    rw [one_mul]
    exact hP
  exact main_eq (hanot0 := hanot0).symm

#lint
