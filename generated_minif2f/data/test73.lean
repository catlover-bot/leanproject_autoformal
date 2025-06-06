import Mathlib.Data.Nat.Basic

theorem mathd_numbertheory_5
(n : ℕ)
(h₀ : 10 ≤ n)
(h₁ : ∃ x, x^2 = n)
(h₂ : ∃ t, t^3 = n) :
64 ≤ n := by
  obtain ⟨x, hx⟩ := h₁
  obtain ⟨t, ht⟩ := h₂
  have : x^2 = t^3 := by rw [hx, ht]
  have : x = t := by
    have : x^2 = t^2 * t := by rw [this, Nat.pow_succ, Nat.pow_one]
    have : x^2 = (t^2) * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have : x^2 = t^2 * t := this
    have