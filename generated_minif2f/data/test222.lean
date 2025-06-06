import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Real

theorem power_identity (m n : ℝ) (p q : ℝ) (hp : p = 2 ^ m) (hq : q = 3 ^ n) : 
  p^(2 * n) * (q^m) = 12^(m * n) := 
by
  rw [hp, hq]
  have h1 : 12 = 2 * 3 := by norm_num
  rw [h1]
  rw [Real.pow_mul, Real.pow_mul]
  ring