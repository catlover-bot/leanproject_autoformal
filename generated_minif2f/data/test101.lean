import data.finset
import data.nat.basic
import algebra.big_operators.basic

open finset

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
begin
  -- Determine the values of a(k) from the given cubes
  have a0 : a 0 = 1, from nat.eq_of_mul_eq_mul_left (nat.zero_lt_succ 0) (by rw [pow_succ, pow_two, mul_one, h₀]),
  have a1 : a 1 = 2, from nat.eq_of_mul_eq_mul_left (nat.zero_lt_succ 1) (by rw [pow_succ, pow_two, mul_one, h₁]),
  have a2 : a 2 = 3, from nat.eq_of_mul_eq_mul_left (nat.zero_lt_succ 2) (by rw [pow_succ, pow_two, mul_one, h₂]),
  have a3 : a 3 = 4, from nat.eq_of_mul_eq_mul_left (nat.zero_lt_succ 3) (by rw [pow_succ, pow_two, mul_one, h₃]),
  have a4 : a 4 = 5, from nat.eq_of_mul_eq_mul_left (nat.zero_lt_succ 4) (by rw [pow_succ, pow_two, mul_one, h₄]),
  have a5 : a 5 = 6, from nat.eq_of_mul_eq_mul_left (nat.zero_lt_succ 5) (by rw [pow_succ, pow_two, mul_one, h₅]),
  have a6 : a 6 = 7, from nat.eq_of_mul_eq_mul_left (nat.zero_lt_succ 6) (by rw [pow_succ, pow_two, mul_one, h₆]),

  -- Calculate the sums
  let s1 := ∑ k in range 7, 6 * (a k)^2,
  let s2 := ∑ k in range 6, 2 * (a k)^2,

  -- Substitute the values of a(k)
  have s1_val : s1 = 6 * (1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 + 7^2),
  { simp [a0, a1, a2, a3, a4, a5, a6] },

  have s2_val : s2 = 2 * (1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2),
  { simp [a0, a1, a2, a3, a4, a5] },

  -- Calculate the individual sums of squares
  have sum_squares_7 : 1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 + 7^2 = 140,
  { norm_num },

  have sum_squares_6 : 1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 = 91,
  { norm_num },

  -- Substitute back into s1 and s2
  rw [s1_val, s2_val, sum_squares_7, sum_squares_6],
  norm_num,
end