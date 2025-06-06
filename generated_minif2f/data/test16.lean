import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

theorem unit_circle_inequality (a b : ℝ) (h : a^2 + b^2 = 1) : a * b + |a - b| ≤ 1 :=
begin
  -- Express a and b in terms of trigonometric functions
  obtain ⟨θ, rfl, rfl⟩ : ∃ θ, a = cos θ ∧ b = sin θ,
  { rw [←sqrt_sq (a^2 + b^2), h, sqrt_one] at h,
    exact ⟨real.angle.arccos a, cos_arccos a (by linarith [h]), sin_arccos a (by linarith [h])⟩ },
  
  -- Calculate a * b and |a - b|
  have ab_eq : a * b = cos θ * sin θ := rfl,
  have abs_diff_eq : |a - b| = |cos θ - sin θ| := rfl,

  -- Use trigonometric identities
  have sin_2θ_eq : 2 * cos θ * sin θ = sin (2 * θ),
  { rw [←sin_two_mul, mul_comm] },

  -- Bound the expression
  have abs_cos_sin_le_sqrt2 : |cos θ - sin θ| ≤ sqrt 2,
  { apply abs_le_of_le_of_neg_le,
    { linarith [cos_sq_add_sin_sq θ] },
    { linarith [cos_sq_add_sin_sq θ] } },

  -- Conclude the proof
  calc
    a * b + |a - b| = cos θ * sin θ + |cos θ - sin θ| : by rw [ab_eq, abs_diff_eq]
    ... = (1/2) * sin (2 * θ) + |cos θ - sin θ| : by rw [←sin_2θ_eq, mul_div_cancel' _ (two_ne_zero : (2 : ℝ) ≠ 0)]
    ... ≤ 1/2 + sqrt 2 : add_le_add (by linarith [abs_sin_le_one (2 * θ)]) abs_cos_sin_le_sqrt2
    ... ≤ 1 : by norm_num,
end