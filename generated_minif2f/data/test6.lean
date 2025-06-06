import data.finset
import algebra.big_operators
import tactic

open finset
open_locale big_operators

theorem sum_of_squares_mod_10 : (∑ x in finset.range 10, ((x + 1)^2)) % 10 = 5 :=
begin
  have h : ∑ x in finset.range 10, ((x + 1)^2) = 385,
  { calc
      ∑ x in finset.range 10, ((x + 1)^2)
          = (1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 + 7^2 + 8^2 + 9^2 + 10^2) : by simp
      ... = 1 + 4 + 9 + 16 + 25 + 36 + 49 + 64 + 81 + 100 : rfl
      ... = 385 : by norm_num },
  rw h,
  norm_num,
end