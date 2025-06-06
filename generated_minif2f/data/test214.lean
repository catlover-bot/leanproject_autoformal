import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD

theorem mathd_numbertheory_222
  (b : ℕ)
  (h₀ : Nat.lcm 120 b = 3720)
  (h₁ : Nat.gcd 120 b = 8) :
  b = 248 :=
begin
  have h₂ : 120 * b = 3720 * 8,
  { rw [Nat.lcm_eq_mul_div_gcd, h₁] at h₀,
    exact (Nat.mul_right_inj (Nat.pos_of_ne_zero (by norm_num))).mp h₀ },
  have h₃ : 120 * b = 29760 := by norm_num [h₂],
  have h₄ : b = 29760 / 120 := Nat.eq_of_mul_eq_mul_left (by norm_num) h₃,
  norm_num at h₄,
  exact h₄,
end