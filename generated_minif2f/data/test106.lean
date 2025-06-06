import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace RealTheorem

theorem problem_statement (m a : ℕ) (h : 0 < m ∧ 0 < a) (h_div : (↑m / ↑a : ℝ) = 3 / 4) : 
  (84 * ↑m + 70 * ↑a) / (↑m + ↑a) = 76 := 
by
  have h1 : 4 * (↑m : ℝ) = 3 * (↑a : ℝ) := by
    field_simp [h_div]
    ring
  have h2 : 84 * ↑m + 70 * ↑a = 76 * (↑m + ↑a) := by
    linarith [h1]
  field_simp [h.1, h.2]
  exact h2

end RealTheorem