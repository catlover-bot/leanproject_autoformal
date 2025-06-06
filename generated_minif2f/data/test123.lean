import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

open Real

theorem inequality_am_gm (x y z : ℝ) (h : 0 < x ∧ 0 < y ∧ 0 < z) :
  9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) :=
begin
  have hxyz : 0 < x + y + z := add_pos (add_pos h.1 h.2.1) h.2.2,
  have hxy : 0 < x + y := add_pos h.1 h.2.1,
  have hyz : 0 < y + z := add_pos h.2.1 h.2.2,
  have hzx : 0 < z + x := add_pos h.2.2 h.1,
  
  -- Apply AM-GM inequality
  have am_gm_ineq : 3 * (2 / (x + y) + 2 / (y + z) + 2 / (z + x)) ≥ 9 / (x + y + z),
  { apply mul_le_mul_of_nonneg_left,
    { linarith [hxy, hyz, hzx] },
    { norm_num } },

  -- Simplify and rearrange
  have : 9 / (x + y + z) ≤ 3 * (2 / (x + y) + 2 / (y + z) + 2 / (z + x)) / 3,
  { rw [div_eq_mul_one_div, mul_div_assoc, mul_one],
    exact am_gm_ineq },

  -- Conclude with direct comparison
  linarith,
end