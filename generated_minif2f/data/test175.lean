import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

open Nat

theorem prime_product_neq_194 (p q : ℕ) (hp : prime p) (hq : prime q) 
  (hp_bounds : 4 ≤ p ∧ p ≤ 18) (hq_bounds : 4 ≤ q ∧ q ≤ 18) : 
  (↑p * ↑q - (↑p + ↑q) ≠ (194:ℤ)) := by
  have primes_in_range : ∀ r, prime r ∧ 4 ≤ r ∧ r ≤ 18 → r ∈ [5, 7, 11, 13, 17] := by
    intro r ⟨hr_prime, hr_bounds⟩
    have : r = 5 ∨ r = 7 ∨ r = 11 ∨ r = 13 ∨ r = 17 := by
      interval_cases r <;> try norm_num
      all_goals
        try (exfalso; apply not_prime_one; assumption)
        try (exfalso; apply not_prime_even; assumption)
    assumption
  have hp_in_range := primes_in_range p ⟨hp, hp_bounds⟩
  have hq_in_range := primes_in_range q ⟨hq, hq_bounds⟩
  fin_cases hp_in_range <;> fin_cases hq_in_range <;> norm_num