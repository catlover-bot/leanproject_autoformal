import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem div_by_11 (n : ℕ) : 11 ∣ (10^n - (-1 : ℤ)^n) :=
begin
  induction n with k ih,
  { -- Base case: n = 0
    simp, -- 10^0 - (-1)^0 = 1 - 1 = 0
    exact dvd_zero 11, -- 11 divides 0
  },
  { -- Inductive step: assume the hypothesis holds for k, prove for k + 1
    rw [pow_succ, pow_succ, mul_comm 10 (10^k)], -- 10^(k+1) = 10 * 10^k
    have h : 10 * 10^k - (-1) * (-1)^k = 10 * (10^k - (-1)^k) + (10 * (-1)^k + (-1)^(k+1)),
    { ring, },
    rw h,
    apply dvd_add,
    { exact dvd_mul_of_dvd_right ih 10, },
    { cases k % 2 with h_even h_odd,
      { -- k is even, (-1)^k = 1, (-1)^(k+1) = -1
        rw [pow_succ, pow_mul, neg_one_sq, one_mul, neg_one_pow_of_even h_even],
        norm_num, -- 10 * 1 + (-1) = 9
        exact dvd_refl 11, -- 11 divides 0
      },
      { -- k is odd, (-1)^k = -1, (-1)^(k+1) = 1
        rw [pow_succ, pow_mul, neg_one_sq, one_mul, neg_one_pow_of_odd h_odd],
        norm_num, -- 10 * (-1) + 1 = -9
        exact dvd_refl 11, -- 11 divides 0
      }
    }
  }
end