```lean
import data.nat.basic
import data.finset
import algebra.big_operators

open finset
open_locale big_operators

theorem sum_powers_of_two_mod_7 : (∑ k in range 101, 2^k) % 7 = 3 :=
begin
  -- Recognize the periodicity of 2^k mod 7
  have h_period : ∀ k, 2^k % 7 = [1, 2, 4].cycle.nth k,
  { intro k,
    induction k with k ih,
    { simp },
    { rw [pow_succ, nat.mul_mod, ih],
      cases (nat.mod_add_div k 3).symm with m hm,
      rw [hm, nat.add_mul_mod_self_left, nat.add_mod],
      cases m,
      { simp },
      { cases m,
        { simp },
        { cases m,
          { simp },
          { simp } } } } },
  
  -- Calculate the sum of one complete cycle
  have h_cycle_sum : (1 + 2 + 4) % 7 = 0,
  { norm_num },

  -- Calculate the number of complete cycles and the remainder
  have h_num_cycles : 101 / 3 = 33,
  { norm_num },
  have h_remainder : 101 % 3 = 2,
  { norm_num },

  -- Sum up all complete cycles and the remaining terms
  have h_sum_cycles : (∑ k in range (33 * 3), 2^k) % 7 = 0,
  { rw [sum_range_mul, h_period],
    simp [h_cycle_sum] },

  have h_sum_remainder : (∑ k in range (33 * 3, 101), 2^k) % 7 = (1 + 2) % 7,
  { rw [sum_range_succ, sum_range_succ, sum_range_zero, zero_add],
    simp [h_period] },

  -- Combine the results
  rw [sum_range_add, h_sum_cycles, h_sum_remainder],
  norm_num,
end
```