import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem div_mod_theorem (r n : ℕ) (hr : r = 1342 % 13) (hn_pos : 0 < n) (hdiv : 1342 ∣ n) (hmod : n % 13 < r) : 6710 ≤ n := 
by
  have hr_val : r = 3 := by norm_num [hr]
  have h1342_mod : 1342 % 13 = 3 := by norm_num
  obtain ⟨k, hk⟩ := hdiv
  rw [hk, Nat.mul_mod, h1342_mod] at hmod
  have : 3 * k % 13 < 3 := hmod
  have : 3 * k % 13 = 0 ∨ 3 * k % 13 = 1 ∨ 3 * k % 13 = 2 := by
    interval_cases 3 * k % 13 <;> tauto
  cases this with h0 h12
  case inl =>
    have : 3 * k = 13 * m := Nat.mod_eq_zero.mp h0
    have : k = 13 * m / 3 := by rw [← this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
    have : k ≥ 5 := by linarith
    linarith [hk]
  case inr =>
    cases h12 with h1 h2
    case inl =>
      have : 3 * k = 13 * m + 1 := Nat.mod_eq_of_lt h1
      have : k = (13 * m + 1) / 3 := by rw [← this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
      have : k ≥ 5 := by linarith
      linarith [hk]
    case inr =>
      have : 3 * k = 13 * m + 2 := Nat.mod_eq_of_lt h2
      have : k = (13 * m + 2) / 3 := by rw [← this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
      have : k ≥ 5 := by linarith
      linarith [hk]