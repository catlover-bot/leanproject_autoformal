import Mathlib.Data.Nat.Basic

theorem exists_m_p_for_n (n : ℕ) (h : 0 < n) : ∃ m, (m > n ∧ ∃ p, m * p ≤ m + p) :=
begin
  use n.succ,
  split,
  { exact_mod_cast nat.lt_succ_self n },
  { use 1,
    rw mul_one,
    apply nat.succ_le_succ,
    exact nat.le_refl n }
end