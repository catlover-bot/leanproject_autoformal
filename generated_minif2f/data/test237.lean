import Mathlib.Data.Real.Basic

namespace RealTheorems

theorem solve_for_m_and_b : ∀ (m b : ℝ), (m * 7 + b = -1) ∧ (m * (-1) + b = 7) → m + b = 5 :=
begin
  intros m b h,
  cases h with h1 h2,
  have eq1 : b = -1 - 7 * m, from eq_sub_of_add_eq h1,
  have eq2 : b = 7 + m, from eq_sub_of_add_eq h2,
  rw eq1 at eq2,
  linarith,
end

end RealTheorems