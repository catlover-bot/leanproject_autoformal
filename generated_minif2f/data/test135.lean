```lean
import data.finset
import data.nat.pow

open finset

lemma prod_range_7_eq : ∏ k in range 7, (2^(2^k) + 3^(2^k)) = 3^128 - 2^128 :=
begin
  have h : ∏ k in range 7, (2^(2^k) + 3^(2^k)) = (3^128 - 2^128),
  { rw [prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_zero],
    norm_num,
    ring_exp },
  exact h,
end
```