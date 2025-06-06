import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators.Basic

open Finset

theorem amc12a_2020_p7
(a : ℕ → ℕ)
(h₀ : (a 0)^3 = 1)
(h₁ : (a 1)^3 = 8)
(h₂ : (a 2)^3 = 27)
(h₃ : (a 3)^3 = 64)
(h₄ : (a 4)^3 = 125)
(h₅ : (a 5)^3 = 216)
(h₆ : (a 6)^3 = 343) :
↑∑ k in finset.range 7, (6 * (a k)^2) - ↑(2 * ∑ k in finset.range 6, (a k)^2) = (658:ℤ) :=
by
  have a0 : a 0 = 1 := Nat.eq_of_mul_eq_mul_left (by norm_num) (by rw [pow_succ, pow_succ, h₀]; norm_num)
  have a1 : a 1 = 2 := Nat.eq_of_mul_eq_mul_left (by norm_num) (by rw [pow_succ, pow_succ, h₁]; norm_num)
  have a2 : a 2 = 3 := Nat.eq_of_mul_eq_mul_left (by norm_num) (by rw [pow_succ, pow_succ, h₂]; norm_num)
  have a3 : a 3 = 4 := Nat.eq_of_mul_eq_mul_left (by norm_num) (by rw [pow_succ, pow_succ, h₃]; norm_num)
  have a4 : a 4 = 5 := Nat.eq_of_mul_eq_mul_left (by norm_num) (by rw [pow_succ, pow_succ, h₄]; norm_num)
  have a5 : a 5 = 6 := Nat.eq_of_mul_eq_mul_left (by norm_num) (by rw [pow_succ, pow_succ, h₅]; norm_num)
  have a6 : a 6 = 7 := Nat.eq_of_mul_eq_mul_left (by norm_num) (by rw [pow_succ, pow_succ, h₆]; norm_num)
  have sum1 : ∑ k in range 7, 6 * (a k)^2 = 6 * (1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 + 7^2) := by
    rw [a0, a1, a2, a3, a4, a5, a6]
  have sum2 : ∑ k in range 6, (a k)^2 = 1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 := by
    rw [a0, a1, a2, a3, a4, a5]
  norm_num at sum1 sum2
  rw [sum1, sum2]
  norm_num
  ring
  norm_num