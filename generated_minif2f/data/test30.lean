import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Proof

theorem solve_for_x : ∀ (x : ℕ), ↑x + (4:ℝ) / (100:ℝ) * ↑x = 598 → x = 575 :=
begin
  intro x,
  intro h,
  have h1 : (1 + 4 / 100) * (x : ℝ) = 598,
  { rw [←add_mul, mul_comm, ←mul_assoc, ←add_mul, mul_comm (4 / 100)], exact h },
  norm_num at h1,
  have h2 : (104 / 100) * (x : ℝ) = 598 := h1,
  norm_num at h2,
  have h3 : (26 / 25) * (x : ℝ) = 598 := h2,
  norm_num at h3,
  have h4 : x = 575,
  { apply_fun (λ y, y * (25 / 26)) at h3,
    norm_num at h3,
    norm_num,
    exact h3 },
  exact h4,
end

end Proof