import data.real.basic
import data.finset
import data.rat.basic
import analysis.special_functions.trigonometric

open_locale big_operators
open finset

theorem aime_1999_p11
  (m : ℚ)
  (h₀ : ∑ k in Icc (1 : ℕ) 35, real.sin (5 * k * π / 180) = real.tan (m * π / 180))
  (h₁ : (m.denom:ℝ) / m.num < 90) :
  ↑m.denom + m.num = 177 :=
begin
  have h₂ : ∑ k in Icc (1 : ℕ) 35, real.sin (5 * k * π / 180) = 0,
  { rw sum_range_succ,
    have : ∀ k ∈ Icc (1 : ℕ) 35, real.sin (5 * k * π / 180) = -real.sin (5 * (36 - k) * π / 180),
    { intros k hk,
      rw [real.sin_sub, real.sin_pi, real.cos_pi, zero_mul, sub_zero, neg_zero, neg_neg],
      congr' 1,
      field_simp,
      ring },
    rw sum_congr rfl this,
    simp },
  rw h₂ at h₀,
  have h₃ : real.tan (m * π / 180) = 0,
  { rw h₀ },
  have h₄ : m * π / 180 = 0 ∨ m * π / 180 = π,
  { rw real.tan_eq_zero_iff,
    exact h₃ },
  cases h₄,
  { have : m = 0,
    { field_simp at h₄,
      linarith },
    rw this,
    norm_num },
  { have : m = 180,
    { field_simp at h₄,
      linarith },
    rw this,
    norm_num }
end