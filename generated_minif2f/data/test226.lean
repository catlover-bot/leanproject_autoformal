```lean
import Mathlib.Data.Nat.Prime

theorem product_sum_2005 (m n : ℕ) (hm : 1 < m) (hn : 1 < n) (h : m * n = 2005) : m + n = 406 := by
  have h2005 : 2005 = 5 * 401 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h401 : Nat.Prime 401 := by norm_num
  have hmn : m = 5 ∧ n = 401 ∨ m = 401 ∧ n = 5 := by
    apply Nat.Prime.eq_mul_of_mul_eq_prime_mul h5 h401 h
    rw [h2005]
  cases hmn with
  | inl hmn1 =>
    cases hmn1 with
    | intro hm5 hn401 =>
      rw [hm5, hn401]
      norm_num
  | inr hmn2 =>
    cases hmn2 with
    | intro hm401 hn5 =>
      rw [hm401, hn5]
      norm_num
```