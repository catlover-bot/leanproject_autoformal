import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Proof

theorem expression_bound (a m c : ℕ) (h : a + m + c = 12) : 
  a * m * c + a * m + m * c + a * c ≤ 112 := 
by
  have h1 : a ≤ 12 := Nat.le_add_right a (m + c)
  have h2 : m ≤ 12 := Nat.le_add_right m (a + c)
  have h3 : c ≤ 12 := Nat.le_add_right c (a + m)
  have h4 : a * m * c ≤ 4 * 4 * 4 := by
    apply Nat.mul_le_mul
    apply Nat.mul_le_mul
    apply Nat.le_trans h1
    linarith
    apply Nat.le_trans h2
    linarith
    apply Nat.le_trans h3
    linarith
  have h5 : a * m + m * c + a * c ≤ 3 * 4 * 4 := by
    apply Nat.add_le_add
    apply Nat.add_le_add
    apply Nat.mul_le_mul
    apply Nat.le_trans h1
    linarith
    apply Nat.le_trans h2
    linarith
    apply Nat.mul_le_mul
    apply Nat.le_trans h2
    linarith
    apply Nat.le_trans h3
    linarith
    apply Nat.mul_le_mul
    apply Nat.le_trans h1
    linarith
    apply Nat.le_trans h3
    linarith
  calc
    a * m * c + a * m + m * c + a * c
        ≤ 4 * 4 * 4 + 3 * 4 * 4 := Nat.add_le_add h4 h5
    _ = 64 + 48 := by norm_num
    _ = 112 := by norm_num

end Proof