import Mathlib.Data.ZMod.Basic

open ZMod

theorem inverse_160_eq_1058 : ∀ (n : ZMod 1399), n = 160⁻¹ → n = 1058 :=
begin
  intro n,
  intro h,
  have h1 : (160 * 1058 : ZMod 1399) = 1,
  { norm_num },
  rw ←h1,
  rw ←h,
  apply mul_inv_cancel_left,
end