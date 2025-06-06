import Mathlib.Data.Real.Basic

theorem solve_for_x (x : ℕ) : (↑x + (4:ℝ) / (100:ℝ) * ↑x = 598) → x = 575 := by
  intro h
  have h' : (1.04 : ℝ) * ↑x = 598 := by
    rw [←add_mul, mul_comm, ←mul_assoc, ←mul_div_assoc, div_self (by norm_num : (100:ℝ) ≠ 0), mul_one] at h
    exact h
  have : ↑x = 575 := by
    apply eq_of_mul_eq_mul_left (by norm_num : (1.04 : ℝ) ≠ 0)
    rw [h']
    norm_num
  exact Nat.cast_inj.mp this