import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MyNamespace

theorem problem_statement : ∀ (x : ℤ), x < 0 → (24 * x) % 1199 = 15 → x ≤ -449 :=
begin
  intros x hx hmod,
  have h1 : 24 * x = 1199 * k + 15, from Int.mod_eq_of_lt (24 * x) 1199 hmod,
  have h2 : 24 * x < 0, from mul_neg_of_pos_of_neg (by norm_num) hx,
  have h3 : 1199 * k + 15 < 0, from h1 ▸ h2,
  have h4 : 1199 * k < -15, from sub_lt_iff_lt_add'.mpr h3,
  have h5 : k < -15 / 1199, from (div_lt_iff (by norm_num : (0 : ℤ) < 1199)).mpr h4,
  have h6 : k ≤ -1, from Int.le_of_lt (by linarith),
  have h7 : 24 * x ≤ 24 * -449, from calc
    24 * x = 1199 * k + 15 : h1
    ... ≤ 1199 * -1 + 15 : add_le_add_right (mul_le_mul_of_nonpos_left h6 (by norm_num)) 15
    ... = 24 * -449 : by norm_num,
  exact (mul_le_mul_left (by norm_num : (0 : ℤ) < 24)).mp h7,
end

end MyNamespace