import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

theorem amc12a_2021_p8
(d : ℕ → ℕ)
(h₀ : d 0 = 0)
(h₁ : d 1 = 0)
(h₂ : d 2 = 1)
(h₃ : ∀ n≥3, d n = d (n - 1) + d (n - 3)) :
even (d 2021) ∧ odd (d 2022) ∧ even (d 2023) :=
by
  have h₄ : ∀ n, d n = d (n % 3) + (n / 3) * d 3 := by
    intro n
    induction n using Nat.strong_induction_on with n ih
    cases n with
    | zero => rw [h₀, Nat.zero_mod, Nat.zero_div, h₀, zero_add]
    | succ n =>
      cases n with
      | zero => rw [h₁, Nat.one_mod, Nat.one_div, h₁, zero_add]
      | succ n =>
        cases n with
        | zero => rw [h₂, Nat.mod_eq_of_lt (by norm_num), Nat.div_eq_of_lt (by norm_num), h₂, zero_add]
        | succ n =>
          have hn : n + 3 ≥ 3 := by linarith
          rw [h₃ (n + 3) hn, ih (n + 2) (by linarith), ih n (by linarith)]
          rw [Nat.add_mod, Nat.add_div, Nat.mod_eq_of_lt (by norm_num), Nat.div_eq_of_lt (by norm_num)]
          ring
  have h₅ : d 3 = 1 := by
    rw [h₃ 3 (by norm_num), h₂, h₀, add_zero]
  have h₆ : ∀ n, d n = d (n % 3) + (n / 3) := by
    intro n
    rw [h₄ n, h₅, mul_one]
  have h₇ : ∀ n, d n % 2 = d (n % 3) % 2 := by
    intro n
    rw [h₆ n]
    exact Nat.add_mod _ _ 2
  have h₈ : d 0 % 2 = 0 := by rw [h₀]
  have h₉ : d 1 % 2 = 0 := by rw [h₁]
  have h₁₀ : d 2 % 2 = 1 := by rw [h₂]
  have h₁₁ : d 2021 % 2 = 0 := by
    rw [h₇ 2021, Nat.mod_eq_of_lt (by norm_num)]
    exact h₈
  have h₁₂ : d 2022 % 2 = 1 := by
    rw [h₇ 2022, Nat.mod_eq_of_lt (by norm_num)]
    exact h₁₀
  have h₁₃ : d 2023 % 2 = 0 := by
    rw [h₇ 2023, Nat.mod_eq_of_lt (by norm_num)]
    exact h₉
  exact ⟨h₁₁, h₁₂, h₁₃⟩