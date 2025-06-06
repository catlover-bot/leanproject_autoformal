import data.finset
import data.int.basic
import data.real.basic

open finset
open real

theorem finset_card_example : ∀ (S : finset ℤ), (∀ (x : ℤ), x ∈ S ↔ ↑(abs x) < 3 * real.pi) → S.card = 19 :=
begin
  intros S h,
  have h_bound : ∀ x : ℤ, x ∈ S ↔ abs x < 9, 
  { intro x,
    specialize h x,
    rw [int.cast_lt, int.cast_coe_nat] at h,
    exact h },
  have h_range : ∀ x : ℤ, abs x < 9 ↔ x ∈ Icc (-8 : ℤ) 8,
  { intro x,
    rw [abs_lt, neg_lt, int.lt_iff_add_one_le, int.lt_iff_add_one_le],
    split,
    { intro h,
      split; linarith },
    { rintro ⟨h₁, h₂⟩,
      linarith } },
  have h_S : S = Icc (-8 : ℤ) 8,
  { ext x,
    rw [h_bound, h_range] },
  rw h_S,
  simp,
end