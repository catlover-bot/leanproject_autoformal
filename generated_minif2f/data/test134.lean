import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

open Nat

theorem prime_dvd_pow_sub_self {p a : ℕ} (ha : 0 < a) (hp : Nat.Prime p) : p ∣ (a^p - a) :=
begin
  by_cases h : a % p = 0,
  { -- Case 1: a ≡ 0 (mod p)
    rw [Nat.mod_eq_zero_of_dvd h] at *,
    have : a^p % p = 0 := Nat.pow_mod _ _ h,
    rw [Nat.sub_self, Nat.zero_mod] at this,
    exact dvd_zero p },
  { -- Case 2: a ≢ 0 (mod p)
    have h1 : a^p % p = a % p,
    { apply Nat.modeq.pow_card_sub_one_eq_self,
      exact hp,
      exact h },
    rw [Nat.sub_eq_iff_eq_add, ←Nat.add_mod, h1, Nat.mod_eq_of_lt (Nat.mod_lt a hp.pos)] at *,
    exact dvd_of_mod_eq_zero (by rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_eq_zero_of_dvd h1]) }
end