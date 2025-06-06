import Mathlib.Data.Nat.Basic

theorem impossible_modulo (n : ℕ) : (3 * n) % 2 = 11 → n % 11 = 8 :=
begin
  intro h,
  exfalso,
  have h_impossible : (3 * n) % 2 < 2 := Nat.mod_lt _ (by norm_num),
  rw h at h_impossible,
  exact Nat.not_lt_zero 11 h_impossible,
end