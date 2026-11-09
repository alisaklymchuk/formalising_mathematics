/-
Copyright (c) 2026 Danylo Dubas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Danylo Dubas
-/
module

public import Mathlib.Tactic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.GroupWithZero.Defs

@[expose] public section

/-!
# Fermat’s Little Theorem

In this file we formalise Fermat’s little theorem
using the finite field ZMod p.

The theorem states that if `p` is prime number and `a`
is not divisible by `p`, then

  a ^ (p - 1) = 1  (mod p)

In this formalisation, elements of `ZMod p` represent
integers modulo `p`. Since `p` is prime, `ZMod p` has
the structure of a finite field.

## Main results

1. `f_x_in_S` : defining a function which multiplies every element by `a` and
showing that this function is a bijection on the non-zero elements.
2. `reindexing_product` : use this function to reindex the product of all non-zero elements.
3. `main_eq` : express the reindexed product as a power of `a` multiplied by the original product.
4. `fermats_little_theorem` : cancel out the product, which is non-zero.
-/

variable {p : ℕ} {a : ZMod p}
variable {hanot0 : a ≠ 0}
variable [Fact (Nat.Prime p)]

/-- A set that contains all elements mod p except 0. -/
def S : Finset (ZMod p) :=
  Finset.filter (fun x => x ≠ 0) Finset.univ

/-- Multiplication by `a`, considered as a function on `ZMod p`.
This function will be used to construct a permutation of the non-zero elements of the field. -/
def f : ZMod p → ZMod p :=
  fun x => a * x

/-- The product of all non-zero elements of `ZMod p`. -/
def P : ZMod p := ∏ x ∈ S, x

/-- Multiplication by `a` is injective on `ZMod p`. -/
theorem injective_f {hanot0 : a ≠ 0} : ∀ x y : ZMod p, f (a := a) x = f (a := a) y → x = y := by
  intro x y hfxfy
  unfold f at hfxfy
  exact mul_left_cancel₀ hanot0 hfxfy

/-- Multiplication by `a` is bijective on `ZMod p`. -/
theorem bijective_f {hanot0 : a ≠ 0} : Function.Bijective (f (a := a)) := by
  apply Finite.injective_iff_bijective.mp
  exact injective_f (hanot0 := hanot0)

/-- Multiplication by `a` is surjective on `ZMod p`. -/
lemma surjective_f {hanot0 : a ≠ 0} : Function.Surjective (f (a := a)) := by
  exact bijective_f (hanot0 := hanot0).2

/-- Multiplication by `a` maps non-zero elements to non-zero elements. -/
theorem f_x_in_S {hanot0 : a ≠ 0} (x : ZMod p) (hx : x ∈ S) : f (a := a) x ∈ S := by
  unfold f
  have hxnot0 : x ≠ 0 := by
    exact (Finset.mem_filter.mp hx).2
  have haxnot0 : a * x ≠ 0 := by
    exact mul_ne_zero hanot0 hxnot0
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_univ _
  · exact haxnot0

/-- The product `P` is non-zero, since every element in the product is non-zero. -/
lemma P_not_zero : P (p := p) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro x hx
  exact (Finset.mem_filter.mp hx).2

/-- Reindexing the product of all non-zero elements after multiplication by `a` does not change its
value. More precisely : ∏ x ∈ S, a * x = P. -/
theorem reindexing_product {hanot0 : a ≠ 0} : ∏ x ∈ S, a * x = P := by
  rw [P]
  apply Finset.prod_bij (fun x _ => f (a := a) x)
  · intro x hx
    exact f_x_in_S (hanot0 := hanot0) x hx
  · intro x hx y hy hfxfy
    apply injective_f (hanot0 := hanot0)
    exact hfxfy
  · intro x hx
    have hxnot0 : x ≠ 0 := by
      exact (Finset.mem_filter.mp hx).2
    rcases surjective_f (hanot0 := hanot0) x with ⟨y, hy⟩
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

/-- The product of the elements `a * x` over `S` can be rewritten as `a` raised to the cardinality
of `S`, multiplied by the original product `P`. -/
lemma prod_eq_pow_mul_P : (∏ x ∈ S, a * x) = a ^ S (p := p).card * P := by
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  rfl
/-- The set of non-zero elements of `ZMod p` is the set of all `ZMod p` elements with the singleton
containing zero removed. This lemma is useful for calculating the cardinality of `S`. -/
lemma S_eq : S = Finset.univ \ ({0} : Finset (ZMod p)) := by
  unfold S
  ext x
  simp

/-- The cardinality of `S` is `p - 1`. -/
lemma card_S : S (p := p).card = p - 1 := by
  rw [S_eq, Finset.card_sdiff]
  simp

/-- The original product `P` is equal to the product obtained by multiplying each factor by `a`. -/
theorem main_eq {hanot0 : a ≠ 0} : P = a ^ (p - 1) * P := by
  rw [← card_S, ← prod_eq_pow_mul_P]
  exact reindexing_product (hanot0 := hanot0).symm

/-- Fermat's Little Theorem. We use the equality established in `main_eq` and cancel
the non-zero product `P` from both sides. -/
theorem fermats_little_theorem {hanot0 : a ≠ 0} : a ^ (p - 1) = 1 := by
  suffices hP : a ^ (p - 1) * P = P by
    apply mul_right_cancel₀ P_not_zero
    rw [one_mul]
    exact hP
  exact main_eq (hanot0 := hanot0).symm

section Euler

variable {n : ℕ} {a : (ZMod n)ˣ}

/-- Multiplication by `a` is bijective on `ZMod p`. -/
def fEuler {a : (ZMod n)ˣ} : (ZMod n)ˣ → (ZMod n)ˣ :=
  fun x => a * x

theorem injective_fEuler : Function.Injective (fEuler (a := a)) := by
  intro x y h
  exact mul_left_cancel h

/-- Multiplication by `a` is bijective on `ZMod p`. -/
theorem bijective_fEuler : Function.Bijective (fEuler (a := a)) := by
  apply Finite.injective_iff_bijective.mp
  exact injective_fEuler

/-- Multiplication by `a` is surjective on `ZMod p`. -/
lemma surjective_fEuler : Function.Surjective (fEuler (a := a)) := by
  exact bijective_fEuler.2

variable [Fact (1 < n)]

/-- Multiplication by `a` is bijective on `ZMod p`. -/
def PEuler : (ZMod n)ˣ := ∏ x : (ZMod n)ˣ, x

/-- The product `P` is non-zero, since every element in the product is non-zero. -/
lemma PEuler_not_zero : (PEuler (n := n) : ZMod n) ≠ 0 := by
  exact Units.ne_zero (PEuler (n := n))

theorem reindexing_product_euler : ∏ x : (ZMod n)ˣ, fEuler (a := a) x = PEuler := by
  rw [PEuler]
  apply Finset.prod_bij (fun x _ => fEuler (a := a) x)
  · intro x hx
    exact Finset.mem_univ _
  · intro x hx y hy hfxfy
    apply injective_fEuler
    exact hfxfy
  · intro x hx
    rcases surjective_fEuler x with ⟨y, hy⟩
    use y
    constructor
    · exact hy
    · exact Finset.mem_univ _
  · intro x hx
    rfl

lemma prod_eq_pow_mul_PEuler : (∏ x : (ZMod n)ˣ, a * x) = a ^ (Nat.totient n) * PEuler := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← ZMod.card_units_eq_totient]
  rfl

theorem main_eq_euler : PEuler = a ^ Nat.totient n * PEuler := by
  rw [← prod_eq_pow_mul_PEuler]
  exact reindexing_product_euler.symm

theorem euler_theorem : a ^ Nat.totient n = 1 := by
  suffices hP : a ^ Nat.totient n * PEuler = PEuler by
    apply mul_right_cancel
    rw [one_mul]
    exact hP
  exact main_eq_euler (a := a).symm

end Euler

#lint
