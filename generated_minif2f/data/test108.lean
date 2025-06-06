import Mathlib.Data.Finset
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.AbsoluteValue

open Int

theorem mathd_algebra_170
(S : Finset ℤ)
(h₀ : ∀ (n : ℤ), n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
S.card = 11 :=
begin
  have h₁ : ∀ n : ℤ, n ∈ S ↔ abs (n - 2) ≤ 56 / 10,
  { intro n, rw h₀, congr, norm_num },
  have h₂ : ∀ n : ℤ, n ∈ S ↔ abs (n - 2) ≤ 28 / 5,
  { intro n, rw h₁, congr, norm_num },
  have h₃ : ∀ n : ℤ, n ∈ S ↔ abs (5 * (n - 2)) ≤ 28,
  { intro n, rw h₂, congr, ring },
  have h₄ : ∀ n : ℤ, n ∈ S ↔ abs (5 * n - 10) ≤ 28,
  { intro n, rw h₃, congr, ring },
  have h₅ : ∀ n : ℤ, n ∈ S ↔ -28 ≤ 5 * n - 10 ∧ 5 * n - 10 ≤ 28,
  { intro n, rw h₄, exact abs_le.mp },
  have h₆ : ∀ n : ℤ, n ∈ S ↔ -18 ≤ 5 * n ∧ 5 * n ≤ 38,
  { intro n, rw h₅, split; intro h; split; linarith },
  have h₇ : ∀ n : ℤ, n ∈ S ↔ 2 ≤ n ∧ n ≤ 7,
  { intro n, rw h₆, split; intro h; split; linarith },
  have h₈ : S = Finset.Icc 2 7,
  { ext n, rw [Finset.mem_Icc, h₇] },
  rw h₈,
  exact Finset.card_Icc 2 7,
end