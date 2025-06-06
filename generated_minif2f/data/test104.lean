import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem unique_solution (x : ℕ) (h1 : x < 100) (h2 : x * 9 % 100 = 1) : x = 89 := by
  have h3 : 9 * 89 % 100 = 1 := by norm_num
  have h4 : x * 9 % 100 = 9 * 89 % 100 := by rw [h2, h3]
  have h5 : x * 9 = 9 * 89 + 100 * (x * 9 / 100) := by
    rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 9)]
  have h6 : 9 * (x - 89) = 100 * (x * 9 / 100) := by
    rw [← h5, ← Nat.mul_sub_left_distrib, h4]
  have h7 : 9 ∣ 100 * (x * 9 / 100) := ⟨x - 89, h6⟩
  have h8 : 9 ∣ x - 89 := by
    apply Nat.dvd_of_dvd_mul_right
    exact h7
  have h9 : x - 89 = 0 := by
    linarith [h1, h8]
  exact Nat.eq_of_sub_eq_zero h9