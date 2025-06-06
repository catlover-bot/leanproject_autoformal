import Mathlib.Data.Finset
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Divisibility

open Finset

lemma card_filter_divisible_by_20 : 
  finset.card (finset.filter (λ x, 20 ∣ x) (finset.Icc 15 85)) = 4 :=
begin
  let s := finset.Icc 15 85,
  have h : (filter (λ x, 20 ∣ x) s) = {20, 40, 60, 80},
  { ext x,
    simp only [mem_filter, mem_Icc, and_iff_right_iff_imp, mem_insert, mem_singleton],
    intro hx,
    obtain ⟨hx1, hx2⟩ := hx.1,
    have h20 : 20 ∣ x := hx.2,
    rcases h20 with ⟨k, rfl⟩,
    have hk : 1 ≤ k ∧ k ≤ 4,
    { split,
      { linarith },
      { linarith } },
    fin_cases hk with h1 h2 h3 h4,
    { left, refl },
    { right, left, refl },
    { right, right, left, refl },
    { right, right, right, refl } },
  rw h,
  simp,
end