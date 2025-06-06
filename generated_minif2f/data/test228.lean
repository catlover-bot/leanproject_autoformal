import Mathlib.Data.Real.Basic

open Real

theorem xyz_product_one (x y z : ℝ) (hpos : 0 < x ∧ 0 < y ∧ 0 < z)
  (h1 : x + 1/y = 4) (h2 : y + 1/z = 1) (h3 : z + 1/x = 7/3) : x * y * z = 1 := 
begin
  -- Express x, y, z in terms of each other
  have hx : x = 4 - 1/y, from eq_sub_of_add_eq h1,
  have hy : y = 1 - 1/z, from eq_sub_of_add_eq h2,
  have hz : z = 7/3 - 1/x, from eq_sub_of_add_eq h3,

  -- Substitute and simplify
  have hxy : x = 4 - 1/(1 - 1/z), from hx.trans (congr_arg (λ t, 4 - 1/t) hy.symm),
  have hyz : y = 1 - 1/(7/3 - 1/x), from hy.trans (congr_arg (λ t, 1 - 1/t) hz.symm),

  -- Solve the system of equations
  have : x = 3/2, {
    rw [hx, hyz],
    field_simp [hpos.2.2, hpos.1],
    linarith,
  },
  have : y = 2/3, {
    rw [hy, hz],
    field_simp [hpos.2, hpos.1],
    linarith,
  },
  have : z = 1, {
    rw [hz, hx],
    field_simp [hpos.1, hpos.2.1],
    linarith,
  },

  -- Verify the product
  calc x * y * z = (3/2) * (2/3) * 1 : by congr; assumption
             ... = 1 : by norm_num,
end