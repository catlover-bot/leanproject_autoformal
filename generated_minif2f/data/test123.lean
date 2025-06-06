import Mathlib.Data.Real.Basic

open Real

theorem inequality_example (x y z : ℝ) (h : 0 < x ∧ 0 < y ∧ 0 < z) : 
  9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) :=
by
  have hxyz : 0 < x + y + z := add_pos (add_pos h.1 h.2.1) h.2.2
  have hxy : 0 < x + y := add_pos h.1 h.2.1
  have hyz : 0 < y + z := add_pos h.2.1 h.2.2
  have hzx : 0 < z + x := add_pos h.2.2 h.1
  have h1 : 9 * (x + y) * (y + z) * (z + x) ≤ 2 * (x + y + z) * (x + y) * (y + z) + 2 * (x + y + z) * (y + z) * (z + x) + 2 * (x + y + z) * (z + x) * (x + y) :=
    by ring_nf; linarith
  have h2 : (x + y + z) * (x + y) * (y + z) * (z + x) ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    exact hxyz.ne'
    exact hxy.ne'
    exact hyz.ne'
    exact hzx.ne'
  field_simp [h2]
  exact h1