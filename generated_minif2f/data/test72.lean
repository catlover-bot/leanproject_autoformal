import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

theorem mathd_algebra_452
  (a : ℕ → ℝ)
  (h₀ : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n)
  (h₁ : a 1 = 2 / 3)
  (h₂ : a 9 = 4 / 5) :
  a 5 = 11 / 15 :=
begin
  have h₃ : ∀ n, a (n + 2) = 2 * a (n + 1) - a n,
  { intro n,
    linarith [h₀ n] },
  have h₄ : ∀ n, a n = a 0 + n * (a 1 - a 0),
  { intro n,
    induction n with n ih,
    { simp },
    { rw [Nat.succ_eq_add_one, h₃, ih],
      ring } },
  have h₅ : a 0 = 1 / 3,
  { have : a 9 = a 0 + 9 * (a 1 - a 0),
    { rw h₄ },
    linarith [h₁, h₂, this] },
  have h₆ : a 5 = a 0 + 5 * (a 1 - a 0),
  { rw h₄ },
  linarith [h₁, h₅, h₆],
end