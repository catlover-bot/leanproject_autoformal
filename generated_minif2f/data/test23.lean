import data.real.nnreal
import data.finset
import algebra.big_operators.basic

open_locale big_operators

theorem imo_2007_p6
  (a : ℕ → nnreal)
  (h₀ : ∑ x in finset.range 100, ((a (x + 1))^2) = 1) :
  ∑ x in finset.range 99, ((a (x + 1))^2 * a (x + 2)) + (a 100)^2 * a 1 < 12 / 25 :=
begin
  have h₁ : ∀ x ∈ finset.range 100, (a (x + 1))^2 ≤ 1,
  { intros x hx,
    have : 0 ≤ (a (x + 1))^2 := nnreal.zero_le _,
    have : (a (x + 1))^2 ≤ 1 := by linarith [h₀],
    exact this },
  have h₂ : ∀ x ∈ finset.range 99, (a (x + 1))^2 * a (x + 2) ≤ (a (x + 1))^2,
  { intros x hx,
    apply mul_le_of_le_one_left,
    exact nnreal.zero_le _,
    apply h₁,
    exact finset.mem_range_succ_iff.mp hx },
  have h₃ : (a 100)^2 * a 1 ≤ (a 100)^2,
  { apply mul_le_of_le_one_left,
    exact nnreal.zero_le _,
    apply h₁,
    exact finset.mem_range_succ_iff.mpr (nat.lt_succ_self 99) },
  have h₄ : ∑ x in finset.range 99, ((a (x + 1))^2 * a (x + 2)) + (a 100)^2 * a 1 ≤ ∑ x in finset.range 100, (a (x + 1))^2,
  { apply finset.sum_le_sum,
    intros x hx,
    apply h₂ x hx,
    apply h₃ },
  rw h₀ at h₄,
  linarith,
end