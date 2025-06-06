import Mathlib.Data.Nat.GCD.Basic

theorem gcd_coprime_21n_4_14n_3 (n : ℕ) (h : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  apply Nat.gcd_eq_one_iff_coprime.mpr
  have : 21 * n + 4 - (14 * n + 3) = 7 * n + 1 := by
    ring
  have : Nat.gcd (14 * n + 3) (7 * n + 1) = 1 := by
    apply Nat.gcd_eq_one_iff_coprime.mpr
    have : 14 * (7 * n + 1) - 7 * (14 * n + 3) = 1 := by
      ring
    exact ⟨14, -7, this⟩
  exact Nat.gcd_eq_one_of_gcd_eq_one_of_gcd_eq_one this (Nat.gcd_eq_one_iff_coprime.mpr ⟨1, -1, by ring⟩)