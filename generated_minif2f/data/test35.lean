import Mathlib.Data.Real.Basic

lemma div_eq_iff_eq_mul {x y z : ℝ} (hz : z ≠ 0) : x / z = y ↔ x = y * z :=
  ⟨λ h, by rw [←h, mul_div_cancel' _ hz], λ h, by rw [h, mul_div_cancel' _ hz]⟩

theorem solve_for_x (x : ℝ) : x / 50 = 40 → x = 2000 :=
begin
  intro h,
  apply (div_eq_iff_eq_mul (by norm_num : (50 : ℝ) ≠ 0)).mp h,
  norm_num,
end