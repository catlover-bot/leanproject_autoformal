import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Real

theorem problem_statement (x y : ℝ) (n : nnreal) :
  (x < 0 ∧ y < 0) →
  (abs x = 6) →
  (sqrt ((x - 8)^2 + (y - 3)^2) = 15) →
  (sqrt (x^2 + y^2) = sqrt n) →
  n = 52 :=
begin
  intros hxy hx_abs hdist hnorm,
  have hx : x = -6,
  { rw abs_eq_neg_self at hx_abs,
    exact hx_abs },
  rw hx at hdist,
  have h1 : sqrt ((-6 - 8)^2 + (y - 3)^2) = 15 := hdist,
  norm_num at h1,
  have h2 : sqrt (256 + (y - 3)^2) = 15 := h1,
  rw sqrt_eq_iff_sq_eq at h2,
  norm_num at h2,
  have hy : (y - 3)^2 = 169,
  { linarith },
  have hy' : y - 3 = -13,
  { rw pow_two at hy,
    linarith },
  have hy_val : y = -10,
  { linarith },
  rw [hx, hy_val] at hnorm,
  have h3 : sqrt ((-6)^2 + (-10)^2) = sqrt n := hnorm,
  norm_num at h3,
  rw sqrt_eq_iff_sq_eq at h3,
  norm_num at h3,
  exact_mod_cast h3,
end