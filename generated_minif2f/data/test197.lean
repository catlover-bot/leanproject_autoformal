import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace MyNamespace

open Nat

theorem even_sub_even_eq_two_and_mul_eq_288_implies_m_eq_18 :
  ∀ (m n : ℕ), even m → even n → m - n = 2 → m * n = 288 → m = 18 :=
begin
  intros m n hm hn hmn hmn_mul,
  obtain ⟨k, hk⟩ := hm,
  obtain ⟨l, hl⟩ := hn,
  rw [hk, hl] at *,
  have h_sub : 2 * k - 2 * l = 2 := hmn,
  rw [mul_sub, mul_one, two_mul, two_mul] at h_sub,
  have h_eq : k - l = 1 := (Nat.sub_eq_of_eq_add (eq_add_of_sub_eq h_sub)).symm,
  have h_mul : (2 * k) * (2 * l) = 288 := hmn_mul,
  rw [mul_assoc, mul_assoc, ←two_mul, ←two_mul] at h_mul,
  have h_kl : k * l = 72 := by linarith,
  have h_k : k = 9 := by linarith,
  rw [h_k, h_eq] at hk,
  norm_num at hk,
end

end MyNamespace