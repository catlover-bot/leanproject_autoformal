import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem imo_1992_p1
  (p q r : ℤ)
  (h₀ : 1 < p ∧ p < q ∧ q < r)
  (h₁ : (p - 1) * (q - 1) * (r - 1) ∣ (p * q * r - 1)) :
  (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) := by
  have h₂ : 0 < (p - 1) * (q - 1) * (r - 1) := by
    linarith
  have h₃ : (p - 1) * (q - 1) * (r - 1) ≤ p * q * r - 1 := by
    apply Int.le_of_dvd
    · linarith
    · exact h₁
  have h₄ : p * q * r - (p - 1) * (q - 1) * (r - 1) ≤ 1 := by
    ring_nf
    linarith
  have h₅ : p * q * r - (p - 1) * (q - 1) * (r - 1) = p + q + r - 2 := by
    ring
  have h₆ : p + q + r - 2 ≤ 1 := by
    rw [← h₅]
    exact h₄
  have h₇ : p + q + r ≤ 3 := by
    linarith
  have h₈ : p ≥ 2 := by
    linarith
  have h₉ : q ≥ 3 := by
    linarith
  have h₁₀ : r ≥ 4 := by
    linarith
  have h₁₁ : p = 2 ∧ q = 4 ∧ r = 8 ∨ p = 3 ∧ q = 5 ∧ r = 15 := by
    interval_cases p <;> interval_cases q <;> interval_cases r <;> norm_num
  cases h₁₁ with
  | inl h₁₂ =>
    left
    exact h₁₂
  | inr h₁₂ =>
    right
    exact h₁₂