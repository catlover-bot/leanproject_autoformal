import data.nat.basic
import data.finset
import algebra.big_operators

open finset

theorem mathd_numbertheory_353
(s : ℕ)
(h₀ : s = ∑ k in finset.Icc 2010 4018, k) :
s % 2009 = 0 :=
begin
  have h₁ : 4018 - 2010 + 1 = 2009 := rfl,
  have h₂ : s = 2009 * (2010 + 4018) / 2,
  { rw h₀,
    rw sum_Icc_eq_sum_range,
    rw range_eq_Ico,
    rw sum_range_add,
    rw sum_range_id,
    rw h₁,
    norm_num,
    ring },
  rw h₂,
  have h₃ : 2009 * (2010 + 4018) / 2 % 2009 = 0,
  { rw nat.mul_div_cancel_left,
    exact nat.divisible_of_dvd (dvd_refl 2009) },
  exact h₃,
end