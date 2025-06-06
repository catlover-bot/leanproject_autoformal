import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Int

theorem aime_1997_p9
  (a : ℝ)
  (h₀ : 0 < a)
  (h₁ : 1 / a - floor (1 / a) = a^2 - floor (a^2))
  (h₂ : 2 < a^2)
  (h₃ : a^2 < 3) :
  a^12 - 144 * (1 / a) = 233 :=
begin
  have h₄ : 1 / a = floor (1 / a) + (a^2 - floor (a^2)), from eq_add_of_sub_eq h₁,
  have h₅ : 2 < floor (a^2) + (1 / a), by linarith,
  have h₆ : floor (a^2) ≤ 2, from floor_le_of_le h₃,
  have h₇ : floor (a^2) = 2, by linarith,
  have h₈ : 2 ≤ a^2, from le_of_lt h₂,
  have h₉ : a^2 < 3, from h₃,
  have h₁₀ : a^2 = 2, by linarith,
  have h₁₁ : a = real.sqrt 2, from eq_of_pow_eq_pow 2 (by norm_num) h₁₀,
  have h₁₂ : a^12 = (real.sqrt 2)^12, by rw h₁₁,
  have h₁₃ : (real.sqrt 2)^12 = 2^6, by norm_num,
  have h₁₄ : 2^6 = 64, by norm_num,
  have h₁₅ : 1 / a = 1 / real.sqrt 2, by rw h₁₁,
  have h₁₆ : 144 * (1 / a) = 144 / real.sqrt 2, by rw h₁₅,
  have h₁₇ : 144 / real.sqrt 2 = 144 * real.sqrt 2 / 2, by rw [←mul_div_assoc, mul_comm, real.mul_self_sqrt (le_of_lt h₀)],
  have h₁₈ : 144 * real.sqrt 2 / 2 = 72 * real.sqrt 2, by ring,
  have h₁₉ : a^12 - 144 * (1 / a) = 64 - 72 * real.sqrt 2, by rw [h₁₂, h₁₃, h₁₄, h₁₆, h₁₇, h₁₈],
  have h₂₀ : 64 - 72 * real.sqrt 2 = 233, by norm_num,
  exact h₂₀,
end