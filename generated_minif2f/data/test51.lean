import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace PositiveNat

open Real

theorem n_eq_5 (x y n : ℕ+) : (↑x / (4:ℝ) + ↑y / 6 = (↑x + ↑y) / n) → n = 5 := by
  intro h
  have h' : 6 * n * (↑x / 4 + ↑y / 6) = 6 * n * ((↑x + ↑y) / n) := by rw [h]
  field_simp at h'
  ring_nf at h'
  have : 6 * n * (x * 6 + y * 4) = 6 * (x + y) * 4 := by
    rw [mul_add, mul_add, mul_assoc, mul_assoc, mul_comm 6 n, mul_comm 6 n]
  rw [this] at h'
  have : 6 * n * x * 6 + 6 * n * y * 4 = 6 * x * 4 + 6 * y * 4 := by
    linarith
  rw [this] at h'
  have : 6 * n * x * 6 = 6 * x * 4 := by
    linarith
  have : 6 * n * x = 6 * x * 4 := by
    linarith
  have : n = 4 := by
    linarith
  contradiction

end PositiveNat