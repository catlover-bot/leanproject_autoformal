import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset
import Mathlib.Tactic

open Finset

lemma not_divisible_by_5 (n : ℕ) : ¬ 5 ∣ ∑ k in range n, (Nat.choose (2 * n + 1) (2 * k + 1)) * (2^(3 * k)) := by
  intro h
  have h_mod : (∑ k in range n, (Nat.choose (2 * n + 1) (2 * k + 1)) * (2^(3 * k))) % 5 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  have : (∑ k in range n, (Nat.choose (2 * n + 1) (2 * k + 1)) * (2^(3 * k))) % 5 ≠ 0 := by
    induction n with n ih
    · simp
    · rw [sum_range_succ, Nat.add_mod, ih]
      have : (Nat.choose (2 * n + 3) (2 * n + 1) * 2^(3 * n)) % 5 ≠ 0 := by
        norm_num [Nat.choose, Nat.factorial, Nat.choose_eq_factorial_div_factorial]
        linarith
      linarith
  contradiction