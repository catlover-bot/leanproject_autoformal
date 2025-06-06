import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

lemma div_12_pow4_add_20 (n : ℕ) : 12 ∣ 4^(n+1) + 20 := by
  have h : 4^(n+1) = 4 * 4^n := by rw [Nat.pow_succ]
  rw [h]
  have : 4 * 4^n + 20 = 4 * (4^n + 5) := by ring
  rw [this]
  apply dvd_mul_right