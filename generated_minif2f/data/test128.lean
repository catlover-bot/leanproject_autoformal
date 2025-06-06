import data.zmod.basic
import tactic

open zmod

lemma inverse_160_mod_1399 : ∀ (n : zmod 1399), n = 160⁻¹ → n = 1058 :=
begin
  intro n,
  intro h,
  have h1 : (160 : zmod 1399) * 1058 = 1,
  { norm_num, },
  rw ←h at h1,
  have h2 : (160 : zmod 1399) * n = 1,
  { rw mul_inv_eq_gcd, exact h, },
  rw h1 at h2,
  exact eq_of_mul_eq_mul_left (by norm_num : (160 : zmod 1399) ≠ 0) h2,
end