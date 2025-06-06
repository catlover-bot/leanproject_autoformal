import Mathlib.Data.Int.Basic

theorem no_integer_solutions (x y : ℤ) : x^5 ≠ y^2 + 4 := by
  by_cases hx : x % 2 = 0
  · -- Case: x is even
    obtain ⟨k, rfl⟩ := Int.mod_eq_zero.mp hx
    have : x^5 = (2 * k)^5 := by rfl
    have : x^5 % 2 = 0 := by
      rw [this, Int.pow_mul, Int.pow_mul, Int.pow_mul, Int.pow_mul, Int.pow_mul]
      norm_num
    by_cases hy : y % 2 = 0
    · -- Subcase: y is even
      obtain ⟨m, rfl⟩ := Int.mod_eq_zero.mp hy
      have : y^2 + 4 = (2 * m)^2 + 4 := by rfl
      have : y^2 + 4 % 2 = 0 := by
        rw [this, Int.pow_mul, Int.pow_mul]
        norm_num
      contradiction
    · -- Subcase: y is odd
      obtain ⟨m, rfl⟩ := Int.mod_eq_one.mp hy
      have : y^2 + 4 = (2 * m + 1)^2 + 4 := by rfl
      have : y^2 + 4 % 2 = 1 := by
        rw [this, Int.pow_add, Int.pow_add, Int.pow_add, Int.pow_add]
        norm_num
      contradiction
  · -- Case: x is odd
    obtain ⟨k, rfl⟩ := Int.mod_eq_one.mp hx
    have : x^5 = (2 * k + 1)^5 := by rfl
    have : x^5 % 2 = 1 := by
      rw [this, Int.pow_add, Int.pow_add, Int.pow_add, Int.pow_add, Int.pow_add]
      norm_num
    by_cases hy : y % 2 = 0
    · -- Subcase: y is even
      obtain ⟨m, rfl⟩ := Int.mod_eq_zero.mp hy
      have : y^2 + 4 = (2 * m)^2 + 4 := by rfl
      have : y^2 + 4 % 2 = 0 := by
        rw [this, Int.pow_mul, Int.pow_mul]
        norm_num
      contradiction
    · -- Subcase: y is odd
      obtain ⟨m, rfl⟩ := Int.mod_eq_one.mp hy
      have : y^2 + 4 = (2 * m + 1)^2 + 4 := by rfl
      have : y^2 + 4 % 2 = 1 := by
        rw [this, Int.pow_add, Int.pow_add, Int.pow_add, Int.pow_add]
        norm_num
      contradiction