import data.nat.factorial
import data.finset
import algebra.big_operators.basic

open finset
open_locale big_operators

theorem odd_prod_eq_factorial_div :
  (finset.prod (finset.filter (λ x, ¬ even x) (finset.range 10000)) (id : ℕ → ℕ)) = (10000! / ((2^5000) * 5000!)) :=
begin
  have h1 : (finset.range 10000).filter (λ x, ¬ even x) ∪ (finset.range 10000).filter even = finset.range 10000,
  { rw finset.filter_union_filter_neg_eq },
  
  have h2 : disjoint ((finset.range 10000).filter (λ x, ¬ even x)) ((finset.range 10000).filter even),
  { exact finset.disjoint_filter_filter_neg _ _ },
  
  have h3 : (finset.prod (finset.range 10000) (id : ℕ → ℕ)) = 10000!,
  { exact finset.prod_range_id 10000 },
  
  have h4 : (finset.prod ((finset.range 10000).filter even) (id : ℕ → ℕ)) = 2^5000 * 5000!,
  { rw finset.prod_filter,
    have : (finset.range 5000).image (λ x, 2 * x) = (finset.range 10000).filter even,
    { ext x,
      simp only [mem_filter, mem_range, mem_image],
      split,
      { rintro ⟨hx, ⟨y, hy, rfl⟩⟩,
        exact ⟨nat.lt_of_mul_lt_mul_left (by simpa using hx) (by norm_num), nat.even_mul_self _⟩ },
      { rintro ⟨hx, he⟩,
        obtain ⟨y, rfl⟩ := nat.even_iff_two_dvd.mp he,
        refine ⟨_, ⟨y, ⟨_, rfl⟩⟩⟩,
        { rw [mul_comm, nat.mul_lt_mul_left (by norm_num)],
          exact hx } } },
    rw ← this,
    simp only [prod_image, nat.mul_left_inj (by norm_num), prod_range_id],
    exact λ x hx y hy hxy, nat.mul_left_cancel₀ (by norm_num) hxy },
  
  rw [← h1, finset.prod_union h2, h3, h4],
  exact nat.mul_right_inj (by norm_num) (by rw [mul_comm, nat.div_mul_cancel (nat.factorial_mul_factorial_dvd_factorial (by norm_num))]),
end