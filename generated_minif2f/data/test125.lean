import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Defs

open Real

theorem abs_inequality (a b : ℝ) : abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) :=
begin
  set x := abs a / (1 + abs a),
  set y := abs b / (1 + abs b),
  set z := abs (a + b) / (1 + abs (a + b)),
  have h1 : 0 ≤ x, from div_nonneg (abs_nonneg a) (add_nonneg zero_le_one (abs_nonneg a)),
  have h2 : 0 ≤ y, from div_nonneg (abs_nonneg b) (add_nonneg zero_le_one (abs_nonneg b)),
  have h3 : 0 ≤ z, from div_nonneg (abs_nonneg (a + b)) (add_nonneg zero_le_one (abs_nonneg (a + b))),
  have h4 : x ≤ 1, from div_le_one_of_le (by linarith [abs_nonneg a]) (add_pos zero_lt_one (abs_pos_of_ne_zero (ne_of_gt (abs_nonneg a)))),
  have h5 : y ≤ 1, from div_le_one_of_le (by linarith [abs_nonneg b]) (add_pos zero_lt_one (abs_pos_of_ne_zero (ne_of_gt (abs_nonneg b)))),
  have h6 : z ≤ 1, from div_le_one_of_le (by linarith [abs_nonneg (a + b)]) (add_pos zero_lt_one (abs_pos_of_ne_zero (ne_of_gt (abs_nonneg (a + b))))),
  have h7 : abs (a + b) ≤ abs a + abs b, from abs_add a b,
  have h8 : abs (a + b) / (1 + abs (a + b)) ≤ (abs a + abs b) / (1 + abs (a + b)), from div_le_div_of_le (add_pos zero_lt_one (abs_pos_of_ne_zero (ne_of_gt (abs_nonneg (a + b))))) h7,
  have h9 : (abs a + abs b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b),
  { apply add_le_add,
    { apply div_le_div_of_le (add_pos zero_lt_one (abs_pos_of_ne_zero (ne_of_gt (abs_nonneg a)))),
      linarith },
    { apply div_le_div_of_le (add_pos zero_lt_one (abs_pos_of_ne_zero (ne_of_gt (abs_nonneg b)))),
      linarith } },
  exact le_trans h8 h9,
end