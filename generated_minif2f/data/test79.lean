```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Nat

theorem lcm_bound (a b : ℕ) :
  (0 < a ∧ 0 < b) ∧ (a % 10 = 2) ∧ (b % 10 = 4) ∧ (gcd a b = 6) → 108 ≤ lcm a b :=
begin
  rintro ⟨⟨ha, hb⟩, ha2, hb4, hgcd⟩,
  have hdiva : 2 ∣ a := by { rw [←mod_eq_zero_iff_dvd, ←nat.mod_add_div a 10, ha2], norm_num },
  have hdivb : 2 ∣ b := by { rw [←mod_eq_zero_iff_dvd, ←nat.mod_add_div b 10, hb4], norm_num },
  have hdiv6a : 6 ∣ a := by { apply dvd_of_gcd_eq_left hgcd },
  have hdiv6b : 6 ∣ b := by { apply dvd_of_gcd_eq_right hgcd },
  have hdiv3a : 3 ∣ a := by { apply dvd_trans (gcd_dvd_left 6 a) hdiv6a },
  have hdiv3b : 3 ∣ b := by { apply dvd_trans (gcd_dvd_right 6 b) hdiv6b },
  have hcoprime : coprime (a / 6) (b / 6),
  { rw [coprime_div_gcd_div_gcd hgcd hgcd, gcd_self], exact coprime_one_right _ },
  have hlcm : lcm a b = a * b / gcd a b := lcm_eq_mul_div_gcd a b,
  rw [hlcm, hgcd],
  have hdiv36 : 36 ∣ a * b,
  { apply dvd_mul_of_dvd_left hdiv6a b },
  have hdiv36' : 36 ∣ a * b,
  { apply dvd_mul_of_dvd_right hdiv6b a },
  have hdiv36'' : 36 ∣ a * b := dvd_trans hdiv36 hdiv36',
  have hdiv36''' : 36 ∣ a * b / 6,
  { apply dvd_div_of_mul_dvd hdiv36'' },
  have h36 : 36 ≤ a * b / 6,
  { apply nat.le_of_dvd, norm_num, exact hdiv36''' },
  linarith,
end
```