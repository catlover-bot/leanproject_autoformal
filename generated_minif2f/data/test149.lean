import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

theorem amc12a_2021_p8
(d : ℕ → ℕ)
(h₀ : d 0 = 0)
(h₁ : d 1 = 0)
(h₂ : d 2 = 1)
(h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) :
even (d 2021) ∧ odd (d 2022) ∧ even (d 2023) :=
begin
  -- Define the parity of the sequence
  have parity : ∀ n, d n % 2 = if n % 3 = 0 then 0 else if n % 3 = 1 then 0 else 1,
  { intro n,
    induction n using Nat.strong_induction_on with n ih,
    cases n,
    { rw h₀, simp },
    cases n,
    { rw h₁, simp },
    cases n,
    { rw h₂, simp },
    { have h := h₃ n (by linarith),
      rw h,
      specialize ih (n - 1) (by linarith),
      specialize ih (n - 3) (by linarith),
      cases n % 3,
      { rw [ih, ih (n - 3)], simp },
      { rw [ih, ih (n - 3)], simp },
      { rw [ih, ih (n - 3)], simp } } },
  -- Calculate the parities of d 2021, d 2022, and d 2023
  have h2021 : d 2021 % 2 = 0,
  { rw parity, norm_num },
  have h2022 : d 2022 % 2 = 1,
  { rw parity, norm_num },
  have h2023 : d 2023 % 2 = 0,
  { rw parity, norm_num },
  -- Conclude the proof
  exact ⟨by rw [Nat.even_iff, h2021], by rw [Nat.odd_iff, h2022], by rw [Nat.even_iff, h2023]⟩,
end