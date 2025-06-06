import Mathlib.Data.Nat.Basic

theorem mod_five_double (n : ℕ) : n % 5 = 3 → (2 * n) % 5 = 1 :=
begin
  intro h,
  -- Express n in terms of division by 5
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h,
  -- Substitute and simplify 2n
  calc
    (2 * (5 * k + 3)) % 5 = (10 * k + 6) % 5 : by rw mul_add
    ... = (0 + 6) % 5 : by rw [Nat.mul_mod_right, zero_add]
    ... = 6 % 5 : rfl
    ... = 1 : by norm_num,
end