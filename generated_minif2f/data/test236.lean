import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Proof

theorem cube_and_fourth_root_bound (n : ℕ) (h1 : 2 ≤ n) (h2 : ∃ x, x^3 = n) (h3 : ∃ t, t^4 = n) : 4096 ≤ n := by
  obtain ⟨x, hx⟩ := h2
  obtain ⟨t, ht⟩ := h3
  have : x^3 = t^4 := by rw [hx, ht]
  have : x^3 ≤ t^3 := by
    rw [this]
    exact Nat.pow_le_pow_of_le_right (Nat.zero_le t) (by norm_num)
  have : t^3 ≤ t^4 := by
    apply Nat.pow_le_pow_of_le_right (Nat.zero_le t)
    exact Nat.le_of_lt (Nat.lt_of_lt_of_le (by norm_num) h1)
  have : x^3 ≤ t^4 := by
    transitivity t^3
    assumption
    assumption
  have : 8 ≤ t := by
    apply Nat.le_of_pow_le_pow 3
    norm_num
    exact this
  have : 4096 ≤ t^4 := by
    apply Nat.pow_le_pow_of_le_right (Nat.zero_le t)
    exact this
  exact this

end Proof