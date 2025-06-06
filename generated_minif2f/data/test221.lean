import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Real

theorem problem_statement
  (x : ℝ)
  (m : ℚ)
  (h₀ : 1 / cos x + tan x = 22 / 7)
  (h₁ : 1 / sin x + 1 / tan x = m) :
  ↑m.denom + m.num = 44 :=
begin
  have h₂ : 1 / sin x + cos x / sin x = m,
  { rw [←div_eq_mul_one_div, ←tan_eq_sin_div_cos, div_div_eq_div_mul, mul_comm, ←add_div] at h₁,
    exact h₁ },
  have h₃ : 1 / cos x + sin x / cos x = 22 / 7,
  { rw [←div_eq_mul_one_div, ←tan_eq_sin_div_cos, div_div_eq_div_mul, mul_comm, ←add_div] at h₀,
    exact h₀ },
  have h₄ : 1 / sin x + cos x / sin x = 1 / cos x + sin x / cos x,
  { rw [h₂, h₃] },
  have h₅ : 1 / sin x = 1 / cos x,
  { linarith },
  have h₆ : sin x = cos x,
  { rw [eq_div_iff_mul_eq, eq_div_iff_mul_eq] at h₅,
    { exact h₅ },
    { exact cos_ne_zero x },
    { exact sin_ne_zero x } },
  have h₇ : sin x = 1 / sqrt 2,
  { rw [h₆, cos_eq_sqrt_one_sub_sin_sq, sub_eq_iff_eq_add, add_self_eq_one] at h₆,
    norm_num at h₆,
    exact h₆ },
  have h₈ : cos x = 1 / sqrt 2,
  { rw [h₆, h₇] },
  have h₉ : m = 2,
  { rw [h₂, h₇, h₈],
    norm_num },
  rw [h₉],
  norm_num,
end