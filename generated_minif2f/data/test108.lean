import data.finset
import data.int.basic

open finset

theorem mathd_algebra_170
(S : finset ℤ)
(h₀ : ∀ (n : ℤ), n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
S.card = 11 :=
begin
  have h₁ : ∀ n : ℤ, n ∈ S ↔ -3.6 ≤ n ∧ n ≤ 7.6,
  { intro n,
    rw h₀,
    split,
    { intro h,
      rw abs_le at h,
      cases h with h_left h_right,
      split,
      { linarith },
      { linarith } },
    { intro h,
      rw abs_le,
      split,
      { linarith },
      { linarith } } },
  have h₂ : S = Icc (-3) 7,
  { ext n,
    rw h₁,
    split,
    { intro h,
      exact ⟨int.ceil_le.mpr h.1, le_of_lt (int.lt_of_le_floor h.2)⟩ },
    { intro h,
      split,
      { linarith [int.le_ceil (-3.6)] },
      { linarith [int.floor_le 7.6] } } },
  rw h₂,
  exact card_Icc.mpr ⟨le_refl (-3), le_refl 7⟩,
end