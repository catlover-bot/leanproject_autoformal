import data.real.basic
import data.finset
import analysis.special_functions.trigonometric

open real
open finset

theorem imo_1969_p2
(m n : ℝ)
(k : ℕ)
(a : ℕ → ℝ)
(y : ℝ → ℝ)
(h₀ : 0 < k)
(h₁ : ∀ x, y x = ∑ i in finset.range k, ((cos (a i + x)) / (2^i)))
(h₂ : y m = 0)
(h₃ : y n = 0) :
∃ t : ℤ, m - n = t * π :=
begin
  have h₄ : ∀ x, y (x + 2 * π) = y x,
  { intro x,
    rw h₁,
    rw h₁ (x + 2 * π),
    apply finset.sum_congr rfl,
    intros i hi,
    rw [cos_add, cos_two_pi, sin_two_pi, mul_zero, sub_zero, mul_one, add_zero],
    ring },
  
  have h₅ : y (m + π) = -y m,
  { rw h₁,
    rw h₁ (m + π),
    apply finset.sum_congr rfl,
    intros i hi,
    rw [cos_add, cos_pi, sin_pi, mul_zero, sub_zero, mul_neg_one, add_zero],
    ring },
  
  have h₆ : y (n + π) = -y n,
  { rw h₁,
    rw h₁ (n + π),
    apply finset.sum_congr rfl,
    intros i hi,
    rw [cos_add, cos_pi, sin_pi, mul_zero, sub_zero, mul_neg_one, add_zero],
    ring },
  
  have h₇ : y (m + π) = 0,
  { rw h₂,
    rw h₅,
    simp },
  
  have h₈ : y (n + π) = 0,
  { rw h₃,
    rw h₆,
    simp },
  
  have h₉ : y (m + 2 * π) = 0,
  { rw h₄ m,
    rw h₂ },
  
  have h₁₀ : y (n + 2 * π) = 0,
  { rw h₄ n,
    rw h₃ },
  
  have h₁₁ : ∀ t : ℤ, y (m + t * π) = 0,
  { intro t,
    induction t with t ht t ht,
    { simp [h₂] },
    { rw [int.of_nat_succ, int.cast_add, int.cast_one, add_assoc, add_comm π, add_assoc],
      rw h₅,
      rw ht,
      simp },
    { rw [int.neg_succ_of_nat_coe, int.cast_neg, int.cast_add, int.cast_one, add_assoc, add_comm π, add_assoc],
      rw h₅,
      rw ht,
      simp } },
  
  have h₁₂ : ∀ t : ℤ, y (n + t * π) = 0,
  { intro t,
    induction t with t ht t ht,
    { simp [h₃] },
    { rw [int.of_nat_succ, int.cast_add, int.cast_one, add_assoc, add_comm π, add_assoc],
      rw h₆,
      rw ht,
      simp },
    { rw [int.neg_succ_of_nat_coe, int.cast_neg, int.cast_add, int.cast_one, add_assoc, add_comm π, add_assoc],
      rw h₆,
      rw ht,
      simp } },
  
  use (m - n) / π,
  field_simp [pi_ne_zero],
  rw [← sub_eq_zero, ← sub_mul, sub_eq_zero],
  apply eq_of_sub_eq_zero,
  rw [← h₁₁ ((m - n) / π), ← h₁₂ 0],
  simp,
end