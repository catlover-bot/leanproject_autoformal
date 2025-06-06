import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

theorem mod_equation (n : ℕ) : (2 * n) % 47 = 15 → n % 47 = 31 := by
  intro h
  have h1 : 2 * n ≡ 15 [MOD 47] := Nat.modeq_iff_dvd'.mpr h
  have h2 : 2 * 31 ≡ 15 [MOD 47] := by norm_num
  have h3 : 2 * n ≡ 2 * 31 [MOD 47] := h1.trans h2.symm
  have h4 : 2 * (n - 31) ≡ 0 [MOD 47] := by
    rw [Nat.sub_eq_iff_eq_add.mpr (Nat.modeq_iff_dvd'.mp h3)]
    exact Nat.modeq_zero_iff_dvd.mpr (Nat.dvd_refl _)
  have h5 : n - 31 ≡ 0 [MOD 47] := by
    apply Nat.modeq_of_dvd_of_coprime _ h4
    exact Nat.coprime_of_prime 47 (by norm_num)
  exact Nat.modeq_iff_dvd'.mp h5.symm