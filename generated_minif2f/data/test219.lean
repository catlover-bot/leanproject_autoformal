import Mathlib.Data.Finset
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic.NormNum

open BigOperators

lemma sum_powers_of_two_mod_seven : (∑ k in (finset.range 101), 2^k) % 7 = 3 := by
  have h : (2^3 : ℕ) = 8 := rfl
  have h_mod : (2^3 : ℕ) % 7 = 1 := by norm_num
  have h_geom : (∑ k in finset.range 101, 2^k) = (2^101 - 1) / (2 - 1) := by
    apply Nat.geom_sum_eq
    norm_num
  rw [h_geom]
  have h_mod_exp : (2^101 - 1) % 7 = (2^101 % 7 - 1 % 7) % 7 := Nat.sub_mod _ _ _
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self 6) (Nat.le_of_dvd (Nat.zero_lt_succ 6) (Nat.dvd_of_mod_eq_zero h_mod)))]
  have h_exp : 2^101 % 7 = 2^(101 % 3) % 7 := by
    rw [← Nat.pow_mod, h_mod]
    norm_num
  rw [h_exp]
  norm_num
  rw [h_mod]
  norm_num
  rw [h_mod_exp]
  norm_num
  rw [Nat.mod_eq_of_lt (Nat.lt_succ_self 6)]
  norm_num