import Mathlib.Data.Nat.Factorial
import Mathlib.Data.Int.Basic

theorem amc12_2001_p21
(a b c d : ℕ)
(h₀ : a * b * c * d = 8!)
(h₁ : a * b + a + b = 524)
(h₂ : b * c + b + c = 146)
(h₃ : c * d + c + d = 104) :
↑a - ↑d = (10 : ℤ) := 
by
  have h₁' : (a + 1) * (b + 1) = 525 := by
    rw [Nat.mul_add, Nat.add_mul, add_assoc, add_assoc, add_comm b, ←add_assoc, h₁]
  have h₂' : (b + 1) * (c + 1) = 147 := by
    rw [Nat.mul_add, Nat.add_mul, add_assoc, add_assoc, add_comm c, ←add_assoc, h₂]
  have h₃' : (c + 1) * (d + 1) = 105 := by
    rw [Nat.mul_add, Nat.add_mul, add_assoc, add_assoc, add_comm d, ←add_assoc, h₃]

  have fact_525 : 525 = 3 * 5^2 * 7 := by norm_num
  have fact_147 : 147 = 3 * 7^2 := by norm_num
  have fact_105 : 105 = 3 * 5 * 7 := by norm_num

  have : a + 1 = 21 ∧ b + 1 = 25 := by
    have : (a + 1) * (b + 1) = 525 := h₁'
    rw [fact_525] at this
    have : a + 1 = 21 ∧ b + 1 = 25 := by decide
    exact this

  have : b + 1 = 7 ∧ c + 1 = 21 := by
    have : (b + 1) * (c + 1) = 147 := h₂'
    rw [fact_147] at this
    have : b + 1 = 7 ∧ c + 1 = 21 := by decide
    exact this

  have : c + 1 = 7 ∧ d + 1 = 15 := by
    have : (c + 1) * (d + 1) = 105 := h₃'
    rw [fact_105] at this
    have : c + 1 = 7 ∧ d + 1 = 15 := by decide
    exact this

  have : a = 20 ∧ b = 6 ∧ c = 6 ∧ d = 14 := by
    cases this with ha hb
    cases this with hb' hc
    cases this with hc' hd
    rw [ha, hb, hc, hd]
    exact ⟨rfl, rfl, rfl, rfl⟩

  rw [this.1, this.2.2.2]
  norm_num
  exact rfl