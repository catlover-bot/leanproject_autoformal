import Mathlib.Data.Real.Basic
import Mathlib.Data.Nnreal.Basic

open Real

theorem nnreal_arithmetic_geometric_mean (x y : ℝ≥0) :
  (x + y) / 2 = 7 → sqrt (x * y) = sqrt 19 → x^2 * y^2 = 158 :=
begin
  intros h_avg h_geom,
  have h1 : x + y = 14,
  { linarith, },
  have h2 : x * y = 19,
  { rw [sqrt_eq_iff_sq_eq, sq_sqrt] at h_geom,
    { exact h_geom, },
    { exact mul_nonneg x.2 y.2, }, },
  have h3 : (x * y)^2 = 19^2,
  { rw h2, },
  have h4 : x^2 * y^2 = (x * y)^2,
  { ring, },
  rw [h4, h3],
  norm_num,
end