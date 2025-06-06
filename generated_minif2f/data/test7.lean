import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric

open Real
open Finset

theorem imo_1969_p2
  (m n : ℝ)
  (k : ℕ)
  (a : ℕ → ℝ)
  (y : ℝ → ℝ)
  (h₀ : 0 < k)
  (h₁ : ∀ x, y x = ∑ i in range k, (cos (a i + x) / (2^i)))
  (h₂ : y m = 0)
  (h₃ : y n = 0) :
  ∃ t : ℤ, m - n = t * π :=
begin
  have h₄ : ∀ x, y x = ∑ i in range k, (cos (a i) * cos x - sin (a i) * sin x) / (2^i),
  { intro x,
    rw h₁,
    congr,
    ext i,
    rw cos_add },
  have h₅ : ∀ x, y x = (∑ i in range k, cos (a i) / (2^i)) * cos x - (∑ i in range k, sin (a i) / (2^i)) * sin x,
  { intro x,
    rw h₄,
    simp only [sum_mul],
    congr,
    { ext i,
      rw mul_div_assoc },
    { ext i,
      rw mul_div_assoc } },
  have h₆ : ∀ x, y x = A * cos x - B * sin x,
  { intro x,
    rw h₅,
    set A := ∑ i in range k, cos (a i) / (2^i) with hA,
    set B := ∑ i in range k, sin (a i) / (2^i) with hB,
    rw [hA, hB] },
  have h₇ : A * cos m - B * sin m = 0,
  { rw [←h₆ m, h₂] },
  have h₈ : A * cos n - B * sin n = 0,
  { rw [←h₆ n, h₃] },
  have h₉ : A ≠ 0 ∨ B ≠ 0,
  { intro h,
    rw [not_or_distrib] at h,
    cases h with hA hB,
    rw [hA, hB] at h₇,
    simp only [zero_mul, sub_zero] at h₇,
    exact zero_ne_one h₇ },
  have h₁₀ : cos m * sin n = cos n * sin m,
  { apply (sub_eq_zero.mp _).symm,
    rw [←sub_eq_zero, ←sub_mul, ←sub_mul, h₇, h₈],
    ring },
  use (m - n) / π,
  rw [eq_div_iff_mul_eq, sub_eq_iff_eq_add],
  { apply eq_of_cos_eq_cos,
    { rw [cos_add, cos_add, h₁₀],
      ring },
    { exact h₉ } },
  { exact pi_ne_zero }
end