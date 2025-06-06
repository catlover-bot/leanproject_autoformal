import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD

open Nat

theorem mathd_numbertheory_711
(m n : ℕ)
(h₀ : 0 < m ∧ 0 < n)
(h₁ : gcd m n = 8)
(h₂ : lcm m n = 112) :
72 ≤ m + n :=
begin
  -- Express m and n in terms of their gcd
  obtain ⟨a, b, ha, hb, rfl, rfl⟩ := gcd_eq_gcd_ab m n,
  have h₃ : m = 8 * a, from (gcd_eq_left_iff_dvd.mpr (dvd_gcd (dvd_mul_left 8 a) (dvd_mul_left 8 b))).symm,
  have h₄ : n = 8 * b, from (gcd_eq_right_iff_dvd.mpr (dvd_gcd (dvd_mul_left 8 a) (dvd_mul_left 8 b))).symm,
  
  -- Use the lcm condition
  have h₅ : lcm (8 * a) (8 * b) = 8 * a * b / gcd (8 * a) (8 * b), from lcm_eq_mul_div_gcd _ _,
  rw [h₁, gcd_mul_left, gcd_mul_right, gcd_comm] at h₅,
  have h₆ : 8 * a * b = 112, from (eq_div_iff_mul_eq (gcd_pos_of_pos_left _ (mul_pos (by norm_num) ha))).mpr h₂,
  have h₇ : a * b = 14, from (nat.mul_right_inj (by norm_num)).mp h₆,

  -- Find possible pairs (a, b)
  have h₈ : (a, b) = (1, 14) ∨ (a, b) = (14, 1),
  { have : a * b = 14 := h₇,
    have : gcd a b = 1 := by rw [←gcd_mul_left, h₁, gcd_comm, gcd_mul_right, gcd_comm, gcd_self, gcd_comm],
    rcases nat.coprime_mul_eq_one_iff.mp this with ⟨ha, hb⟩,
    rcases nat.eq_one_or_eq_one_of_mul_eq_one ha with rfl | rfl;
    rcases nat.eq_one_or_eq_one_of_mul_eq_one hb with rfl | rfl;
    simp [h₇] },

  -- Calculate m + n
  cases h₈ with h₈ h₈;
  { rw [h₃, h₄, h₈],
    norm_num }
end