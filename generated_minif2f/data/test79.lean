import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Gcd
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Nat

theorem lcm_ge_108 (a b : ℕ) :
  (0 < a ∧ 0 < b) ∧ (a % 10 = 2) ∧ (b % 10 = 4) ∧ (gcd a b = 6) → 108 ≤ lcm a b :=
begin
  rintro ⟨⟨ha, hb⟩, ha_mod, hb_mod, gcd_ab⟩,
  have ha_form : ∃ m, a = 10 * m + 2,
  { use (a / 10), rw [Nat.mod_add_div] },
  have hb_form : ∃ n, b = 10 * n + 4,
  { use (b / 10), rw [Nat.mod_add_div] },
  rcases ha_form with ⟨m, rfl⟩,
  rcases hb_form with ⟨n, rfl⟩,
  have gcd_condition : gcd (10 * m + 2) (10 * n + 4) = 6,
  { rw [gcd_ab] },
  have a_mod_6 : (10 * m + 2) % 6 = 0,
  { rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_add, Nat.mod_eq_zero_of_dvd],
    exact dvd_of_mod_eq_zero (by norm_num) },
  have b_mod_6 : (10 * n + 4) % 6 = 0,
  { rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_add, Nat.mod_eq_zero_of_dvd],
    exact dvd_of_mod_eq_zero (by norm_num) },
  have a_div_6 : ∃ k, 10 * m + 2 = 6 * k,
  { use (10 * m + 2) / 6, rw [Nat.mul_div_cancel' (dvd_of_mod_eq_zero a_mod_6)] },
  have b_div_6 : ∃ l, 10 * n + 4 = 6 * l,
  { use (10 * n + 4) / 6, rw [Nat.mul_div_cancel' (dvd_of_mod_eq_zero b_mod_6)] },
  rcases a_div_6 with ⟨k, rfl⟩,
  rcases b_div_6 with ⟨l, rfl⟩,
  have lcm_formula : lcm (6 * k) (6 * l) = 6 * lcm k l,
  { rw [lcm_mul_left, gcd_mul_left_left, gcd_ab, mul_comm] },
  have lcm_kl_ge_18 : 18 ≤ lcm k l,
  { have : 1 ≤ k ∧ 1 ≤ l,
    { split; apply Nat.div_pos; linarith },
    have : 3 ≤ k + l,
    { linarith },
    have : 18 ≤ k * l,
    { nlinarith },
    exact le_trans (lcm_le_mul k l) this },
  rw [lcm_formula],
  linarith,
end