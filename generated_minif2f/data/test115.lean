```lean
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Nat

theorem polynomial_gcd_condition (n : ℕ) (p : ℕ → ℕ) 
  (h : ∀ x, p x = x^2 - x + 41) 
  (gcd_cond : 1 < gcd (p n) (p (n+1))) : 41 ≤ n :=
begin
  -- Assume for contradiction that n < 41
  by_contradiction h₁,
  push_neg at h₁,
  have h₂ : n ≤ 40 := Nat.le_of_lt_succ h₁,
  
  -- Check the primality of p(n) for n ≤ 40
  have prime_p : ∀ m ≤ 40, Prime (p m),
  { intros m hm,
    rw h,
    interval_cases m; norm_num },

  -- Since p(n) and p(n+1) are both prime, their gcd should be 1
  have gcd_one : gcd (p n) (p (n+1)) = 1,
  { apply Prime.gcd_eq_one_of_coprime,
    { apply prime_p, exact h₂ },
    { apply prime_p, linarith } },

  -- This contradicts the assumption that gcd is greater than 1
  linarith,
end
```