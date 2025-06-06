import Mathlib.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Real

theorem AM_GM_inequality (a b c d : ℝ) (h : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) : 
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d :=
begin
  have h1 : a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ 4 * (a * b * c * d) ^ (1/4),
  { apply add_four_geometric_mean,
    exact h.1, exact h.2.1, exact h.2.2.1, exact h.2.2.2 },
  have h2 : 4 * (a * b * c * d) ^ (1/4) ≥ a + b + c + d,
  { apply four_geometric_mean_le_sum,
    exact h.1, exact h.2.1, exact h.2.2.1, exact h.2.2.2 },
  linarith,
end

lemma add_four_geometric_mean (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ 4 * (a * b * c * d) ^ (1/4) :=
begin
  have h1 : a^2 / b ≥ 2 * (a * b) ^ (1/2),
  { apply div_ge_two_mul_sqrt,
    exact ha, exact hb },
  have h2 : b^2 / c ≥ 2 * (b * c) ^ (1/2),
  { apply div_ge_two_mul_sqrt,
    exact hb, exact hc },
  have h3 : c^2 / d ≥ 2 * (c * d) ^ (1/2),
  { apply div_ge_two_mul_sqrt,
    exact hc, exact hd },
  have h4 : d^2 / a ≥ 2 * (d * a) ^ (1/2),
  { apply div_ge_two_mul_sqrt,
    exact hd, exact ha },
  linarith,
end

lemma div_ge_two_mul_sqrt (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x^2 / y ≥ 2 * (x * y) ^ (1/2) :=
begin
  have h : (x^2 / y) * y ≥ 2 * (x * y) ^ (1/2) * y,
  { apply mul_le_mul_of_nonneg_right,
    { apply sq_div_ge_two_mul_sqrt,
      exact hx, exact hy },
    exact le_of_lt hy },
  rw [div_mul_cancel _ (ne_of_gt hy)] at h,
  exact h,
end

lemma sq_div_ge_two_mul_sqrt (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x^2 ≥ 2 * x * y :=
begin
  have h : x^2 - 2 * x * y + y^2 ≥ 0,
  { apply sq_nonneg },
  linarith,
end

lemma four_geometric_mean_le_sum (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
  4 * (a * b * c * d) ^ (1/4) ≤ a + b + c + d :=
begin
  apply AM_GM_inequality_four,
  exact ha, exact hb, exact hc, exact hd,
end

lemma AM_GM_inequality_four (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
  (a * b * c * d) ^ (1/4) ≤ (a + b + c + d) / 4 :=
begin
  have h : (a * b * c * d) ^ (1/4) ≤ ((a + b + c + d) / 4) ^ (1/4),
  { apply real.geom_mean_le_arith_mean4,
    exact ha, exact hb, exact hc, exact hd },
  rw [div_pow, pow_one_div, pow_one_div] at h,
  exact h,
end