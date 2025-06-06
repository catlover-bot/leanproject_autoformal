import data.nat.gcd
import data.fintype.basic
import data.finset

open nat
open finset

theorem mathd_numbertheory_552
  (f g h : ℕ+ → ℕ)
  (h₀ : ∀ x, f x = 12 * x + 7)
  (h₁ : ∀ x, g x = 5 * x + 2)
  (h₂ : ∀ x, h x = nat.gcd (f x) (g x))
  (h₃ : fintype (set.range h)) :
  ∑ k in (set.range h).to_finset, k = 12 :=
begin
  have h₄ : ∀ x, h x = 1 ∨ h x = 12,
  { intro x,
    rw [h₂, h₀, h₁],
    let a := 12 * x + 7,
    let b := 5 * x + 2,
    have : gcd a b = gcd (12 * x + 7) (5 * x + 2) := rfl,
    have : gcd a b = gcd (12 * x + 7 - 5 * (12 * x + 7)) (5 * x + 2) := gcd_sub a b (5 * x + 2),
    rw [this, sub_eq_add_neg, add_comm, add_assoc, add_neg_cancel_left],
    have : gcd (12 * x + 7 - 5 * (12 * x + 7)) (5 * x + 2) = gcd (7 - 35) (5 * x + 2) := rfl,
    rw [this, sub_eq_add_neg, add_comm, add_assoc, add_neg_cancel_left],
    have : gcd (-28) (5 * x + 2) = gcd 28 (5 * x + 2) := gcd_neg_left 28 (5 * x + 2),
    rw this,
    have : gcd 28 (5 * x + 2) = gcd 28 (5 * x + 2 - 5 * 28) := gcd_sub 28 (5 * x + 2) (5 * 28),
    rw [this, sub_eq_add_neg, add_comm, add_assoc, add_neg_cancel_left],
    have : gcd 28 (-138) = gcd 28 138 := gcd_neg_right 28 138,
    rw this,
    have : gcd 28 138 = gcd 28 (138 % 28) := gcd_rec 28 138,
    rw this,
    norm_num,
    exact or.inl rfl },
  have h₅ : set.range h = {1, 12},
  { ext k,
    split,
    { intro hk,
      rcases hk with ⟨x, rfl⟩,
      exact h₄ x },
    { intro hk,
      cases hk,
      { use 1,
        rw h₂,
        norm_num },
      { use 1,
        rw h₂,
        norm_num } } },
  rw h₅,
  simp,
end