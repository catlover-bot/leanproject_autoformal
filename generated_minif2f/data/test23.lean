import data.real.nnreal
import data.finset
import algebra.big_operators.basic

open_locale big_operators

theorem imo_2007_p6
  (a : ℕ → nnreal)
  (h₀ : ∑ x in finset.range 100, ((a (x + 1))^2) = 1) :
  ∑ x in finset.range 99, ((a (x + 1))^2 * a (x + 2)) + (a 100)^2 * a 1 < 12 / 25 :=
begin
  -- We will use the AM-GM inequality to bound each term (a(x+1))^2 * a(x+2)
  have h₁ : ∀ x ∈ finset.range 99, (a (x + 1))^2 * a (x + 2) ≤ (2/3) * (a (x + 1))^3 + (1/3) * (a (x + 2))^3,
  { intros x hx,
    apply nnreal.mul_le_mul,
    { apply nnreal.pow_le_pow_of_le_left,
      { exact a (x + 1).2 },
      { exact le_of_lt (nnreal.lt_add_one (a (x + 1))) } },
    { exact le_of_lt (nnreal.lt_add_one (a (x + 2))) } },
  
  -- Similarly, bound the term (a 100)^2 * a 1
  have h₂ : (a 100)^2 * a 1 ≤ (2/3) * (a 100)^3 + (1/3) * (a 1)^3,
  { apply nnreal.mul_le_mul,
    { apply nnreal.pow_le_pow_of_le_left,
      { exact a 100.2 },
      { exact le_of_lt (nnreal.lt_add_one (a 100)) } },
    { exact le_of_lt (nnreal.lt_add_one (a 1)) } },

  -- Sum up the inequalities
  have h₃ : ∑ x in finset.range 99, ((a (x + 1))^2 * a (x + 2)) + (a 100)^2 * a 1
            ≤ ∑ x in finset.range 99, ((2/3) * (a (x + 1))^3 + (1/3) * (a (x + 2))^3) + ((2/3) * (a 100)^3 + (1/3) * (a 1)^3),
  { apply finset.sum_le_sum,
    intros x hx,
    apply h₁ x hx,
    apply h₂ },

  -- Simplify the right-hand side
  have h₄ : ∑ x in finset.range 99, ((2/3) * (a (x + 1))^3 + (1/3) * (a (x + 2))^3) + ((2/3) * (a 100)^3 + (1/3) * (a 1)^3)
            = (2/3) * ∑ x in finset.range 100, (a (x + 1))^3,
  { rw [finset.sum_add_distrib, finset.sum_range_succ, finset.sum_range_succ],
    simp only [add_assoc, add_comm, add_left_comm, mul_add, mul_assoc, mul_comm (2/3)],
    congr' 1,
    { apply finset.sum_congr rfl,
      intros x hx,
      rw [add_comm, add_assoc] },
    { rw [add_comm, add_assoc] } },

  -- Use the fact that the sum of cubes is bounded by the sum of squares
  have h₅ : ∑ x in finset.range 100, (a (x + 1))^3 ≤ (∑ x in finset.range 100, (a (x + 1))^2)^(3/2),
  { apply nnreal.sum_pow_le_pow_sum,
    { intros x hx,
      exact a (x + 1).2 },
    { exact h₀ } },

  -- Combine the inequalities
  have h₆ : (2/3) * ∑ x in finset.range 100, (a (x + 1))^3 ≤ (2/3) * (1^(3/2)),
  { apply nnreal.mul_le_mul,
    { exact h₅ },
    { exact le_of_lt (nnreal.lt_add_one 1) } },

  -- Simplify the right-hand side
  have h₇ : (2/3) * (1^(3/2)) = 2/3,
  { simp },

  -- Conclude the proof
  linarith,
end