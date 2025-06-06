import Mathlib.Data.Real.Basic
import Mathlib.Algebra.GroupPower.Basic

open Real

theorem real_exponent_equation (x : ℝ) :
  ((11:ℝ)^(1 / 4))^(3 * x - 3) = 1 / 5 → ((11:ℝ)^(1 / 4))^(6 * x + 2) = 121 / 25 :=
begin
  intro h,
  have h1 : (11^(1/4))^(3 * x - 3) = (11^(1/4))^(-3) * (11^(1/4))^(3 * x),
  { rw [←rpow_add, sub_eq_add_neg, add_comm] },
  rw h1 at h,
  have h2 : (11^(1/4))^(-3) = 1 / (11^(1/4)^3),
  { rw [rpow_neg, one_div] },
  rw h2 at h,
  have h3 : (11^(1/4)^3) = 11^(3/4),
  { rw [←rpow_mul, mul_comm, ←rpow_nat_cast, rpow_nat_cast, rpow_nat_cast] },
  rw h3 at h,
  have h4 : (11^(3/4)) = 5,
  { rw [←rpow_eq_iff_eq_rpow, rpow_one, rpow_nat_cast, rpow_nat_cast],
    exact_mod_cast h },
  have h5 : (11^(1/4))^(3 * x) = 5 * (11^(1/4))^3,
  { rw [←rpow_add, ←h4, ←rpow_mul, mul_comm, ←rpow_nat_cast, rpow_nat_cast] },
  rw h5 at h,
  have h6 : (11^(1/4))^(6 * x + 2) = (11^(1/4))^(6 * x) * (11^(1/4))^2,
  { rw [←rpow_add, add_comm] },
  rw h6,
  have h7 : (11^(1/4))^(6 * x) = (5 * (11^(1/4))^3)^2,
  { rw [←rpow_mul, mul_comm, ←rpow_nat_cast, rpow_nat_cast, ←h5] },
  rw h7,
  have h8 : (11^(1/4))^2 = 11^(1/2),
  { rw [←rpow_mul, mul_comm, ←rpow_nat_cast, rpow_nat_cast] },
  rw h8,
  have h9 : (5 * (11^(1/4))^3)^2 * 11^(1/2) = 121 / 25,
  { rw [mul_pow, h4, pow_two, mul_assoc, mul_comm, mul_div_assoc, mul_comm, div_self, mul_one],
    norm_num },
  exact h9,
end