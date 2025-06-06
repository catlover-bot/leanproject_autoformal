import data.nat.basic
import data.finset

open finset

theorem sum_range_101_mod_6 : (∑ k in range 101, k) % 6 = 4 :=
begin
  -- Calculate the sum of integers from 0 to 100
  have h_sum : ∑ k in range 101, k = 5050,
  { rw sum_range,
    norm_num },
  
  -- Calculate 5050 mod 6
  have h_mod : 5050 % 6 = 4,
  { norm_num },
  
  -- Conclude the proof
  rw h_sum,
  exact h_mod,
end