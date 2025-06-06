import Mathlib.Data.Nat.Basic

theorem problem_solution : ∀ (m n : ℕ), 1 < m → 1 < n → m * n = 2005 → m + n = 406 := by
  intros m n hm hn hmn
  have h1 : m ≤ 2005 := Nat.le_of_dvd (Nat.succ_pos 2004) (dvd_of_mul_eq hmn)
  have h2 : n ≤ 2005 := Nat.le_of_dvd (Nat.succ_pos 2004) (dvd_of_mul_eq (by rw [Nat.mul_comm, hmn]))
  have h3 : m ≤ 2005 / 2 := Nat.le_div_of_mul_le (Nat.succ_pos 1) (by rw [hmn]; exact Nat.le_refl 2005)
  have h4 : n ≤ 2005 / 2 := Nat.le_div_of_mul_le (Nat.succ_pos 1) (by rw [Nat.mul_comm, hmn]; exact Nat.le_refl 2005)
  have h5 : m = 5 ∨ m = 401 := by
    have : m * n = 2005 := hmn
    have : m * n = 5 * 401 := by norm_num
    have : m = 5 ∨ m = 401 := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos 1) this
    exact this
  cases h5 with
  | inl h5m =>
    have h5n : n = 401 := by
      rw [h5m] at hmn
      exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos 1) (by norm_num at hmn; exact hmn)
    rw [h5m, h5n]
    norm_num
  | inr h5m =>
    have h5n : n = 5 := by
      rw [h5m] at hmn
      exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos 1) (by norm_num at hmn; exact hmn)
    rw [h5m, h5n]
    norm_num