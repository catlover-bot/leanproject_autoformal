import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Basic

namespace Proof

theorem unique_solution (a b c : ℚ) (m n : ℝ) :
  0 < m ∧ 0 < n → m^3 = 2 → n^3 = 4 → (a:ℝ) + b * m + c * n = 0 → a = 0 ∧ b = 0 ∧ c = 0 :=
begin
  intros hmn hm hn h,
  have h1 : (a:ℝ) = - (b * m + c * n), by linarith,
  have h2 : (a:ℝ) = 0, {
    have : b * m + c * n = 0, {
      rw [h1, neg_eq_zero],
      exact h,
    },
    have : b * m = - c * n, by linarith,
    have : b * m * m^2 = - c * n * m^2, by rw [this],
    rw [hm] at this,
    have : b * 2 = - c * n * m^2, by linarith,
    rw [hn] at this,
    have : b * 2 = - c * 4 * m^2, by linarith,
    have : b * 2 = - c * 4 * 2^(2/3), by rw [hm],
    have : b * 2 = - c * 4 * 2^(2/3), by linarith,
    have : b = 0, {
      have : 2 ≠ 0, by norm_num,
      linarith,
    },
    have : c = 0, {
      have : 4 ≠ 0, by norm_num,
      linarith,
    },
    linarith,
  },
  have h3 : b = 0, {
    have : b * m = 0, by linarith,
    exact eq_zero_of_mul_eq_zero_left this,
  },
  have h4 : c = 0, {
    have : c * n = 0, by linarith,
    exact eq_zero_of_mul_eq_zero_left this,
  },
  exact ⟨h2, h3, h4⟩,
end

end Proof