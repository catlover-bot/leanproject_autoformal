import Mathlib.Data.Nat.Basic

lemma exists_multiplicative_property (n : ℕ) (h : 0 < n) : ∃ m, (m > n ∧ ∃ p, m * p ≤ m + p) :=
  ⟨n + 1, by
    constructor
    · linarith
    · use 1
      ring⟩

theorem main_theorem : ∀ n : ℕ, 0 < n → ∃ m, (m > n ∧ ∃ p, m * p ≤ m + p) :=
  λ n h, exists_multiplicative_property n h