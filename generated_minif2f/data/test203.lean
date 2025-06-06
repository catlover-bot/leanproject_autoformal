import Mathlib.Data.Real.Basic

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3
  (a b c : ℝ)
  (h₀ : a ≤ b ∧ b ≤ c)
  (h₁ : a + b + c = 2)
  (h₂ : a * b + b * c + c * a = 1) :
  0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 :=
begin
  have h₃ : a ≤ b ∧ b ≤ c := h₀,
  have h₄ : a + b + c = 2 := h₁,
  have h₅ : a * b + b * c + c * a = 1 := h₂,

  -- Express b and c in terms of a
  have h₆ : b = 2 - a - c, by linarith,
  have h₇ : c = 2 - a - b, by linarith,

  -- Substitute into the product equation
  have h₈ : a * (2 - a - c) + (2 - a - c) * c + c * a = 1,
  { rw [h₆, h₇], exact h₅ },

  -- Simplify the equation
  have h₉ : a * (2 - a - c) + (2 - a - c) * c + c * a = 1,
  { rw [h₆, h₇], exact h₅ },

  -- Solve for a, b, c
  have h₁₀ : 3 * a * a - 4 * a + 1 = 0,
  { ring_nf at h₈, linarith },

  -- Solve the quadratic equation
  have h₁₁ : a = 1 / 3,
  { field_simp at h₁₀, linarith },

  -- Determine b and c
  have h₁₂ : b = 1,
  { rw [h₁₁, h₆], linarith },

  have h₁₃ : c = 2 - a - b,
  { rw [h₁₁, h₁₂], linarith },

  -- Verify the ranges
  split,
  { linarith },
  split,
  { linarith },
  split,
  { linarith },
  split,
  { linarith },
  split,
  { linarith },
  { linarith },
end