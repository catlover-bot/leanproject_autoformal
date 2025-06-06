import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

open Nat

theorem fermat_little_theorem (p a : ℕ) (h0 : 0 < a) (hp : Nat.Prime p) : p ∣ (a^p - a) := by
  have h1 : a^p ≡ a [MOD p] := Nat.modeq_pow_self _ hp
  rw [Nat.modeq_iff_dvd] at h1
  exact h1.symm

#eval fermat_little_theorem 3 2 (by decide) (by norm_num)