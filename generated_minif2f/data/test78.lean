import Mathlib.Data.Nat.Digits

theorem amc12a_2003_p5
(A M C : ℕ)
(h₀ : A ≤ 9 ∧ M ≤ 9 ∧ C ≤ 9)
(h₁ : nat.of_digits 10 [0,1,C,M,A] + nat.of_digits 10 [2,1,C,M,A] = 123422) :
A + M + C = 14 :=
begin
  -- Express the numbers in terms of A, M, C
  have h2 : nat.of_digits 10 [0,1,C,M,A] = 1000 * C + 100 * M + 10 * A,
  { simp [nat.of_digits, show 10^4 = 10000, by norm_num, show 10^3 = 1000, by norm_num,
          show 10^2 = 100, by norm_num, show 10^1 = 10, by norm_num, show 10^0 = 1, by norm_num] },
  have h3 : nat.of_digits 10 [2,1,C,M,A] = 200000 + 1000 * C + 100 * M + 10 * A,
  { simp [nat.of_digits, show 10^5 = 100000, by norm_num, show 10^4 = 10000, by norm_num,
          show 10^3 = 1000, by norm_num, show 10^2 = 100, by norm_num, show 10^1 = 10, by norm_num,
          show 10^0 = 1, by norm_num] },
  
  -- Substitute into the given equation
  rw [h2, h3] at h₁,
  -- Simplify the equation
  linarith,
end