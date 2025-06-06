import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

open BigOperators

theorem mathd_numbertheory_552
  (f g h : ℕ+ → ℕ)
  (h₀ : ∀ x, f x = 12 * x + 7)
  (h₁ : ∀ x, g x = 5 * x + 2)
  (h₂ : ∀ x, h x = Nat.gcd (f x) (g x))
  (h₃ : Fintype (Set.range h)) :
  ∑ k in (Set.range h).toFinset, k = 12 :=
by
  have h₄ : ∀ x, h x = 1 := by
    intro x
    rw [h₂, h₀, h₁]
    apply Nat.gcd_eq_one_iff_coprime.mpr
    apply Nat.coprime_of_dvd
    intro a ha₁ ha₂
    have ha₃ : a ∣ 12 * x + 7 := ha₁
    have ha₄ : a ∣ 5 * x + 2 := ha₂
    have ha₅ : a ∣ (12 * x + 7) - 2 * (5 * x + 2) := Nat.dvd_sub ha₃ (Nat.dvd_mul_of_dvd_right ha₄ 2)
    rw [mul_comm 5 x, mul_comm 2 x, mul_assoc, mul_assoc, ← mul_sub] at ha₅
    rw [mul_comm 2 5, mul_comm 2 2, mul_sub, mul_sub, mul_comm 2 5, mul_comm 2 2, mul_assoc, mul_assoc] at ha₅
    have ha₆ : a ∣ 2 * x + 3 := ha₅
    have ha₇ : a ∣ (5 * x + 2) - 5 * (2 * x + 3) := Nat.dvd_sub ha₄ (Nat.dvd_mul_of_dvd_right ha₆ 5)
    rw [mul_comm 5 (2 * x + 3), mul_assoc, ← mul_sub] at ha₇
    rw [mul_comm 5 2, mul_comm 5 3, mul_sub, mul_sub, mul_comm 5 2, mul_comm 5 3, mul_assoc, mul_assoc] at ha₇
    have ha₈ : a ∣ 1 := ha₇
    exact Nat.dvd_one.mp ha₈
  have h₅ : Set.range h = {1} := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, hx⟩
      rw [h₄ x] at hx
      exact Set.mem_singleton 1
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact ⟨1, h₄ 1⟩
  rw [h₅, Finset.sum_singleton]
  norm_num