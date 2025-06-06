import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Nat

theorem power_mod_theorem : ∀ (n : ℕ), 0 < n → (3^(2^n) - 1) % (2^(n + 3)) = 2^(n + 2) :=
begin
  intro n,
  induction n with k ih,
  { intro h, exfalso, exact Nat.not_lt_zero 0 h },
  { intro h,
    cases k,
    { norm_num },
    { have h_k : 0 < k.succ := Nat.succ_pos k,
      specialize ih h_k,
      let a := 3^(2^k.succ),
      have h1 : a - 1 = (3^(2^k))^2 - 1 := by rw [pow_succ, pow_mul],
      have h2 : (3^(2^k) - 1) * (3^(2^k) + 1) = a - 1 := by ring_nf,
      rw [h1, h2],
      have h3 : (3^(2^k) - 1) % (2^(k + 3)) = 2^(k + 2) := ih,
      have h4 : (3^(2^k) + 1) % 4 = 0,
      { have : 3^(2^k) ≡ 1 [MOD 4],
        { induction k with m ihm,
          { norm_num },
          { rw [pow_succ, pow_mul],
            have : 3^(2^m.succ) ≡ 1 [MOD 4] := by exact ihm,
            have : 3^(2^m.succ) * 3^(2^m.succ) ≡ 1 * 1 [MOD 4] := by exact Nat.ModEq.mul this this,
            norm_num at this,
            exact this } },
        have : 3^(2^k) + 1 ≡ 1 + 1 [MOD 4] := Nat.ModEq.add_right this,
        norm_num at this,
        exact this },
      have h5 : 2^(k + 3) = 2^(k + 2) * 4 := by ring_nf,
      rw [h5],
      have h6 : (3^(2^k) - 1) * (3^(2^k) + 1) % (2^(k + 2) * 4) = (2^(k + 2) * (3^(2^k) + 1)) % (2^(k + 2) * 4),
      { rw [h3],
        ring_nf },
      rw [h6],
      have h7 : (2^(k + 2) * (3^(2^k) + 1)) % (2^(k + 2) * 4) = 2^(k + 2) * ((3^(2^k) + 1) % 4),
      { apply Nat.mul_mod_right },
      rw [h7, h4],
      norm_num } }
end