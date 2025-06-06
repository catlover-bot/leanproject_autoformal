import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MyNamespace

lemma mod_eq_of_mod_mul_eq {a b c d : ℕ} (h : (a * b) % c = d) (hc : c > 0) : a % c = d :=
  have h1 : (a * b) % c = (a % c * b % c) % c := Nat.mul_mod a b c
  have h2 : (a % c * b % c) % c = d := by rw [h1, h]
  have h3 : a % c * b % c = d := Nat.mod_eq_of_lt (Nat.mod_lt _ hc) ▸ h2
  have h4 : a % c = d := by
    cases b % c with
    | zero => rw [Nat.mul_zero] at h3; exact h3
    | succ b' =>
      have : b' + 1 > 0 := Nat.succ_pos b'
      have : a % c = d := by
        apply Nat.eq_of_mul_eq_mul_right this
        rw [Nat.mul_comm, h3]
      exact this
  h4

theorem mod_11_of_3n_mod_2_eq_11 (n : ℕ) : (3 * n) % 2 = 11 → n % 11 = 8 :=
  fun h =>
    have : 2 > 0 := Nat.succ_pos 1
    have h1 : 3 % 2 = 1 := by norm_num
    have h2 : (3 * n) % 2 = (n % 2 * 1) % 2 := by rw [Nat.mul_mod, h1]
    have h3 : n % 2 = 11 := mod_eq_of_mod_mul_eq h this
    have h4 : n % 11 = 8 := by
      have : n % 2 < 2 := Nat.mod_lt n this
      linarith
    h4

end MyNamespace