import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open Int

theorem odd_square_mod_eight (a : ℤ) (b : ℕ) (ha : odd a) (hb : 4 ∣ b) : (a^2 + b^2) % 8 = 1 := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨c, hc⟩ := hb
  have ha_mod : a % 2 = 1 := by
    rw [hk, add_comm, Int.add_mul_mod_self_left]
    norm_num
  have ha_sq_mod : a^2 % 8 = 1 := by
    rw [hk, add_comm, Int.add_mul_mod_self_left]
    norm_num
  have hb_sq_mod : b^2 % 8 = 0 := by
    rw [hc, Nat.cast_mul, Int.mul_pow, Int.pow_two, Int.mul_assoc, Int.mul_comm 4, Int.mul_assoc]
    norm_num
  calc
    (a^2 + b^2) % 8 = (a^2 % 8 + b^2 % 8) % 8 := Int.add_mod _ _ _
    _ = (1 + 0) % 8 := by rw [ha_sq_mod, hb_sq_mod]
    _ = 1 := by norm_num