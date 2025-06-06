import data.rat.basic
import data.real.basic
import data.nat.prime

open nat

theorem rational_function_property
  (f : ℚ → ℝ)
  (h_mul : ∀ x > 0, ∀ y > 0, f (x * y) = f x + f y)
  (h_prime : ∀ p, prime p → f p = p) :
  f (25 /. 11) < 0 :=
begin
  -- Establish f(25) using the functional equation and prime condition
  have f_5 : f 5 = 5,
  { apply h_prime, exact prime_iff.2 ⟨2, dec_trivial⟩ },
  
  have f_25 : f 25 = f (5 * 5),
  { rw h_mul 5 (by norm_num) 5 (by norm_num), },
  rw [f_25, f_5, f_5],
  have f_25_value : f 25 = 10,
  { norm_num, },

  -- Establish f(11) using the prime condition
  have f_11 : f 11 = 11,
  { apply h_prime, exact prime_iff.2 ⟨2, dec_trivial⟩ },

  -- Calculate f(25 / 11) using the functional equation
  have f_25_div_11 : f (25 /. 11) = f 25 - f 11,
  { rw [h_mul 25 (by norm_num) (11⁻¹) (by norm_num)],
    rw [h_mul 11 (by norm_num) (11⁻¹) (by norm_num)],
    rw [f_11, mul_inv_cancel (by norm_num : (11 : ℚ) ≠ 0), f_11],
    norm_num, },

  -- Conclude f(25 / 11) < 0
  rw [f_25_div_11, f_25_value, f_11],
  norm_num,
end