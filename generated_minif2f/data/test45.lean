import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem pow_mod_seven : (5^999999) % 7 = 6 := by
  -- Step 1: Apply Fermat's Little Theorem
  have fermat : 5^6 % 7 = 1 := by norm_num

  -- Step 2: Express 999999 in terms of 6
  have h : 999999 = 6 * 166666 + 3 := by norm_num

  -- Step 3: Simplify using modular arithmetic
  have step3 : (5^999999) % 7 = ((5^6)^166666 * 5^3) % 7 := by
    rw [h, Nat.pow_add, Nat.pow_mul]

  -- Step 4: Calculate 5^3 mod 7
  have pow3 : 5^3 % 7 = 6 := by norm_num

  -- Step 5: Conclude the proof
  rw [step3]
  rw [Nat.mul_mod, Nat.pow_mod, fermat, one_pow, one_mul, pow3]