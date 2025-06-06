import data.real.basic
import data.finset
import algebra.big_operators

open_locale big_operators
open finset

theorem product_bound (n : ℕ) (h : 0 < n) : ∏ k in Icc 1 n, (1 + (1:ℝ) / 2^k) < 5 / 2 :=
begin
  induction n with m ih,
  { exfalso, exact nat.not_lt_zero 0 h },
  { cases m,
    { simp, norm_num },
    { have h₁ : 0 < m.succ := nat.succ_pos m,
      specialize ih h₁,
      rw prod_Icc_succ_top m.succ_pos,
      have : 1 + (1:ℝ) / 2^(m.succ + 1) < 2,
      { apply lt_of_le_of_lt,
        { apply add_le_add_left,
          apply one_div_le_one_div_of_le,
          { norm_num, apply pow_pos, norm_num },
          { apply pow_le_pow, norm_num, apply nat.succ_le_succ, apply nat.zero_le } },
        { norm_num } },
      calc ∏ (k : ℕ) in Icc 1 m.succ, (1 + (1:ℝ) / 2^k)
          = (∏ (k : ℕ) in Icc 1 m, (1 + (1:ℝ) / 2^k)) * (1 + (1:ℝ) / 2^(m.succ + 1)) : by rw prod_Icc_succ_top m.succ_pos
      ... < (5 / 2) * 2 : mul_lt_mul' ih this (by norm_num) (by norm_num)
      ... = 5 : by norm_num } }
end