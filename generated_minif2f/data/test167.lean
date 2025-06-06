import algebra.big_operators.basic
import data.real.nnreal
import analysis.mean_inequalities

open_locale big_operators
open finset

theorem am_gm_inequality (a : ℕ → nnreal) (n : ℕ) (h : ∑ x in range n, a x = n) : 
  ∏ x in range n, a x ≤ 1 :=
begin
  cases n,
  { simp, },
  have h_am_gm := real.geom_mean_le_arith_mean_weighted (λ i, a i) (λ i, (1 : nnreal)) (range n.succ) _,
  { simp only [sum_const, nsmul_eq_mul, one_mul, card_range, cast_succ] at h_am_gm,
    rw [h, nsmul_eq_mul, one_mul] at h_am_gm,
    exact h_am_gm, },
  { intros i hi,
    exact zero_le (a i), },
  { simp, },
end