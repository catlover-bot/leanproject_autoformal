import Mathlib.Data.Nat.Prime

theorem product_sum_bound (i m o : ℕ) (h : i ≠ 0 ∧ m ≠ 0 ∧ o ≠ 0) (h_prod : i * m * o = 2001) : i + m + o ≤ 671 := 
begin
  -- Factor 2001 as 3 * 23 * 29
  have h2001 : 2001 = 3 * 23 * 29 := by norm_num,
  rw h2001 at h_prod,

  -- Use the fact that i, m, o are non-zero and their product is 2001
  have h_factors : i = 3 ∨ i = 23 ∨ i = 29 ∨ i = 3 * 23 ∨ i = 3 * 29 ∨ i = 23 * 29 ∨ i = 3 * 23 * 29,
  { have : i ∣ 2001 := nat.dvd_of_mul_dvd_mul_right h.1 (by rw [mul_assoc, mul_comm m o, ←h_prod]; exact dvd_refl _),
    rcases this with ⟨k, hk⟩,
    have : k ∣ 3 * 23 * 29 := by rw ←h2001; exact ⟨i, h_prod.symm⟩,
    rcases nat.dvd_prime_factors this with ⟨a, b, c, ha, hb, hc, hk'⟩,
    rw [hk, hk'] at h_prod,
    have : i = a * b * c := by rw [mul_assoc, mul_comm b c, ←hk'],
    rw this,
    repeat { right },
    exact or.inl rfl },

  -- Check all possible values of i
  rcases h_factors with rfl | rfl | rfl | rfl | rfl | rfl | rfl;
  { -- Calculate m and o based on the value of i
    rcases nat.dvd_of_mul_dvd_mul_left h.1 (by rw [mul_assoc, mul_comm m o, ←h_prod]; exact dvd_refl _) with ⟨k, hk⟩,
    rw hk at h_prod,
    have : m * o = k := by rw [mul_assoc, mul_comm m o, ←h_prod, hk],
    rcases nat.dvd_prime_factors (by rw ←h2001; exact ⟨m, this.symm⟩) with ⟨a, b, ha, hb, hk'⟩,
    rw [hk, hk'] at h_prod,
    have : m = a * b := by rw [mul_comm, ←hk'],
    rw this,
    repeat { right },
    exact or.inl rfl,
    -- Calculate the sum i + m + o
    calc i + m + o ≤ 3 + 23 + 29 : by norm_num
               ... ≤ 671 : by norm_num }
end