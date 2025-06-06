import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem imo_1965_p2
(x y z : ℝ)
(a : ℕ → ℝ)
(h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
(h₁ : a 1 < 0 ∧ a 2 < 0)
(h₂ : a 3 < 0 ∧ a 5 < 0)
(h₃ : a 7 < 0 ∧ a 9 < 0)
(h₄ : 0 < a 0 + a 1 + a 2)
(h₅ : 0 < a 3 + a 4 + a 5)
(h₆ : 0 < a 6 + a 7 + a 8)
(h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
(h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
(h₉ : a 6 * x + a 7 * y + a 8 * z = 0) :
x = 0 ∧ y = 0 ∧ z = 0 :=
begin
  have h₁' : a 1 * y + a 2 * z = -a 0 * x, from eq_neg_of_add_eq_zero_left h₇,
  have h₂' : a 3 * x + a 5 * z = -a 4 * y, from eq_neg_of_add_eq_zero_left h₈,
  have h₃' : a 6 * x + a 7 * y = -a 8 * z, from eq_neg_of_add_eq_zero_left h₉,
  have : a 0 * x + a 1 * y + a 2 * z + a 3 * x + a 4 * y + a 5 * z + a 6 * x + a 7 * y + a 8 * z = 0,
  { rw [h₇, h₈, h₉], ring },
  have : (a 0 + a 3 + a 6) * x + (a 1 + a 4 + a 7) * y + (a 2 + a 5 + a 8) * z = 0,
  { ring_nf at this, exact this },
  have : 0 < a 0 + a 3 + a 6,
  { linarith [h₀.1, h₄, h₅, h₆] },
  have : 0 < a 1 + a 4 + a 7,
  { linarith [h₀.2.1, h₁.1, h₂.1, h₃.1, h₄, h₅, h₆] },
  have : 0 < a 2 + a 5 + a 8,
  { linarith [h₀.2.2, h₁.2, h₂.2, h₃.2, h₄, h₅, h₆] },
  linarith,
end