import data.nat.parity
import data.finset
import algebra.big_operators.basic

open finset

lemma sum_first_odd_numbers : ∑ k in range 8, (2 * k + 1) = 64 :=
begin
  -- Calculate the sum of the first 8 odd numbers: 1, 3, 5, ..., 15
  rw sum_range_succ,
  rw sum_range_succ,
  rw sum_range_succ,
  rw sum_range_succ,
  rw sum_range_succ,
  rw sum_range_succ,
  rw sum_range_succ,
  rw sum_range_succ,
  norm_num,
end

lemma sum_sequence (a : ℕ) : ∑ k in range 5, (a + 2 * k) = 5 * a + 20 :=
begin
  -- Calculate the sum of the sequence a, a+2, a+4, a+6, a+8
  rw sum_range_succ,
  rw sum_range_succ,
  rw sum_range_succ,
  rw sum_range_succ,
  rw sum_range_succ,
  norm_num,
  ring,
end

theorem even_a_implies_a_eq_8 (a : ℕ) (h_even : even a)
  (h_eq : (↑∑ k in range 8, (2 * k + 1) - ↑∑ k in range 5, (a + 2 * k) = (4:ℤ))) : a = 8 :=
begin
  -- Use the precomputed sums
  have h1 : ∑ k in range 8, (2 * k + 1) = 64 := sum_first_odd_numbers,
  have h2 : ∑ k in range 5, (a + 2 * k) = 5 * a + 20 := sum_sequence a,
  
  -- Substitute these into the hypothesis
  rw [h1, h2] at h_eq,
  
  -- Simplify the equation
  norm_cast at h_eq,
  linarith,
end