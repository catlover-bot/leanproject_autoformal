import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace MyNamespace

open Int

theorem no_even_square_sum (a b : ℤ) :
  ¬ ((∃ i j, a = 2 * i ∧ b = 2 * j) ↔ (∃ k, a^2 + b^2 = 8 * k)) :=
begin
  intro h,
  have h1 : ∃ i j, a = 2 * i ∧ b = 2 * j → ∃ k, a^2 + b^2 = 8 * k,
  { intro h2,
    obtain ⟨i, j, ha, hb⟩ := h2,
    rw [ha, hb],
    use i^2 + j^2,
    ring },
  have h2 : (∃ k, a^2 + b^2 = 8 * k) → ∃ i j, a = 2 * i ∧ b = 2 * j,
  { intro h3,
    obtain ⟨k, hk⟩ := h3,
    have : a^2 + b^2 ≡ 0 [MOD 8],
    { rw hk, exact Int.ModEq.refl _ },
    have : a^2 ≡ 0 [MOD 8] ∧ b^2 ≡ 0 [MOD 8],
    { rw [Int.ModEq.add_iff, Int.ModEq.zero_iff] at this,
      exact this },
    cases this with ha hb,
    have : a ≡ 0 [MOD 2] ∧ b ≡ 0 [MOD 2],
    { split; apply Int.ModEq.of_pow_mod_eq_zero; assumption },
    obtain ⟨i, hi⟩ := this.1,
    obtain ⟨j, hj⟩ := this.2,
    use [i, j],
    rw [Int.ModEq, Int.dvd_iff_mod_eq_zero] at hi hj,
    exact ⟨hi, hj⟩ },
  have h3 := h1 ⟨0, 0, rfl, rfl⟩,
  obtain ⟨k, hk⟩ := h3,
  have : 0 = 8 * k := hk,
  norm_num at this,
end

end MyNamespace