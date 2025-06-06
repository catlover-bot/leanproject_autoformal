```lean
import data.zmod.basic
import data.int.gcd

open zmod

lemma inverse_24_mod_121 : ∀ (b : zmod (11^2)), b = 24⁻¹ → b = 116 :=
begin
  intro b,
  intro h,
  have h1 : (24 : zmod 121) * 116 = 1,
  { norm_num },
  have h2 : (24 : zmod 121)⁻¹ = 116,
  { apply eq_inv_of_mul_eq_one_left,
    exact h1 },
  rw h2 at h,
  exact h,
end
```