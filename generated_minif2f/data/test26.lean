import Mathlib.Data.Nat.Basic

theorem mathd_numbertheory_430
(a b c : ℕ)
(h₀ : 1 ≤ a ∧ a ≤ 9)
(h₁ : 1 ≤ b ∧ b ≤ 9)
(h₂ : 1 ≤ c ∧ c ≤ 9)
(h₃ : a ≠ b)
(h₄ : a ≠ c)
(h₅ : b ≠ c)
(h₆ : a + b = c)
(h₇ : 10 * a + a - b = 2 * c)
(h₈ : c * b = 10 * a + a + a) :
a + b + c = 8 :=
begin
  -- From h₆, we have c = a + b
  rw [h₆] at h₇ h₈,
  -- Simplify h₇: 11a - b = 2(a + b)
  have h₇' : 11 * a - b = 2 * a + 2 * b := h₇,
  linarith,
  -- Simplify h₈: (a + b) * b = 13a
  have h₈' : (a + b) * b = 13 * a := h₈,
  -- Solve for b in terms of a
  have h₉ : b * b + a * b = 13 * a := by linarith,
  have h₁₀ : b * b = 13 * a - a * b := by linarith,
  -- Check possible values for a, b, c
  have : a = 2 ∧ b = 3 ∧ c = 5,
  { use [2, 3, 5],
    split; norm_num,
    split; norm_num,
    split; norm_num,
    split; norm_num,
    split; norm_num,
    split; norm_num,
    split; norm_num,
    norm_num },
  rcases this with ⟨rfl, rfl, rfl⟩,
  norm_num,
end