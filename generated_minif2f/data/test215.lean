import data.real.basic
import data.rat.basic
import data.finset
import analysis.special_functions.trigonometric

open_locale big_operators
open finset

theorem aime_1999_p11
(m : ℚ)
(h₀ : ∑ k in Icc (1 : ℕ) 35, real.sin (5 * k * real.pi / 180) = real.tan (m * real.pi / 180))
(h₁ : (m.denom:ℝ) / m.num < 90) :
↑m.denom + m.num = 177 :=
begin
  -- Convert the sum of sines into a known value
  have h_sum : ∑ k in Icc (1 : ℕ) 35, real.sin (5 * k * real.pi / 180) = 0,
  { -- The sum of sines from 5° to 175° in 5° increments is zero
    -- This is a known result due to symmetry and periodicity of sine
    simp [real.sin_add, real.sin_sub, real.sin_pi, real.cos_pi],
    have : ∀ k ∈ Icc (1 : ℕ) 35, real.sin (5 * k * real.pi / 180) = -real.sin (5 * (36 - k) * real.pi / 180),
    { intros k hk,
      rw [← real.sin_add_pi, add_sub_cancel', mul_sub, mul_one, mul_comm, mul_assoc],
      congr' 1,
      norm_num },
    rw sum_congr rfl this,
    simp },

  -- Use the given hypothesis h₀
  rw h_sum at h₀,
  have h_tan_zero : real.tan (m * real.pi / 180) = 0 := h₀,

  -- Tangent is zero when the angle is a multiple of π
  have h_m : ∃ n : ℤ, m * real.pi / 180 = n * real.pi,
  { rw real.tan_eq_zero_iff at h_tan_zero,
    exact h_tan_zero },

  -- Solve for m
  rcases h_m with ⟨n, hn⟩,
  have : m = n * 180,
  { field_simp [hn],
    ring },
  rw this at h₁,

  -- m is a rational number, so n * 180 must be rational
  have : (n * 180 : ℚ) = m,
  { rw this },
  have : (n * 180).denom = 1,
  { rw rat.denom_eq_one_iff,
    exact_mod_cast this },

  -- Calculate the sum of numerator and denominator
  have : m.num = n * 180,
  { rw this,
    exact rat.num_denom' m },
  have : m.denom = 1,
  { rw this,
    exact_mod_cast this },

  -- Use the inequality to find n
  have : (1:ℝ) / (n * 180) < 90,
  { rw [this, rat.coe_int_mul, rat.coe_int_one, rat.coe_int_mul, rat.coe_int_one] at h₁,
    exact h₁ },
  have : n * 180 > 0,
  { linarith },
  have : n = 1,
  { linarith },

  -- Conclude the proof
  rw [this, mul_one, rat.coe_int_one, rat.coe_int_mul, rat.coe_int_one] at *,
  norm_cast,
  exact_mod_cast this,
end