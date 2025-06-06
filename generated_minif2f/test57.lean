import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace DivisibilityProof

theorem power_divisibility (m n : ℕ) (f : ℕ → ℕ) 
  (hf : ∀ x, f x = 4^x + 6^x + 9^x) 
  (hpos : 0 < m ∧ 0 < n) 
  (hmn : m ≤ n) : 
  f (2^m) ∣ f (2^n) := 
begin
  have hfm : f (2^m) = 4^(2^m) + 6^(2^m) + 9^(2^m), from hf (2^m),
  have hfn : f (2^n) = 4^(2^n) + 6^(2^n) + 9^(2^n), from hf (2^n),
  rw [hfm, hfn],
  apply Nat.dvd_add,
  { apply Nat.dvd_add,
    { apply Nat.pow_dvd_pow,
      exact Nat.pow_le_pow_of_le_right (by norm_num) hmn },
    { apply Nat.pow_dvd_pow,
      exact Nat.pow_le_pow_of_le_right (by norm_num) hmn } },
  { apply Nat.pow_dvd_pow,
    exact Nat.pow_le_pow_of_le_right (by norm_num) hmn }
end

end DivisibilityProof