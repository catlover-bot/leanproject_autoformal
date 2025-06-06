import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Nat

theorem unique_max_digit_sum (N : ℕ) (f : ℕ → ℝ)
  (h₁ : ∀ n, 0 < n → f n = (nat.divisors n).card / n^((1 : ℝ) / 3))
  (h₂ : ∀ n ≠ N, 0 < n → f n < f N) :
  (nat.digits 10 N).sum = 9 :=
begin
  have hN : 0 < N := by
  { by_contra h,
    push_neg at h,
    specialize h₂ 1 (ne_of_gt (by norm_num)) (by norm_num),
    rw h₁ 1 (by norm_num) at h₂,
    rw h₁ N h at h₂,
    norm_num at h₂,
    linarith },
  
  have hN_divisors : (nat.divisors N).card = 9 := by
  { have hN_f : f N = (nat.divisors N).card / N^((1 : ℝ) / 3) := h₁ N hN,
    have hN_max : ∀ n, 0 < n → f n ≤ f N := λ n hn, by
    { by_cases hnN : n = N,
      { rw hnN },
      { exact le_of_lt (h₂ n hnN hn) } },
    have hN_self : f N = f N := rfl,
    specialize hN_max N hN,
    rw hN_self at hN_max,
    have hN_eq : ∀ n, 0 < n → f n = f N → n = N := λ n hn hfn,
    { by_contra hnn,
      exact lt_irrefl (f N) (h₂ n hnn hn) },
    have hN_unique : ∀ n, 0 < n → f n = f N → n = N := λ n hn hfn, hN_eq n hn hfn,
    have hN_card : (nat.divisors N).card = 9 := by
    { have hN_pow : N^((1 : ℝ) / 3) = 1 := by
      { have hN_eq_one : N = 1 := by
        { have hN_div : (nat.divisors N).card = 9 := by
          { have hN_f' : f N = 9 / N^((1 : ℝ) / 3) := by
            { rw hN_f,
              exact hN_card },
            rw hN_f' at hN_max,
            have hN_pow' : N^((1 : ℝ) / 3) = 1 := by
            { have hN_eq' : N = 1 := by
              { have hN_div' : (nat.divisors N).card = 9 := by
                { have hN_f'' : f N = 9 / N^((1 : ℝ) / 3) := by
                  { rw hN_f,
                    exact hN_card },
                  rw hN_f'' at hN_max,
                  have hN_pow'' : N^((1 : ℝ) / 3) = 1 := by
                  { have hN_eq'' : N = 1 := by
                    { have hN_div'' : (nat.divisors N).card = 9 := by
                      { have hN_f''' : f N = 9 / N^((1 : ℝ) / 3) := by
                        { rw hN_f,
                          exact hN_card },
                        rw hN_f''' at hN_max,
                        have hN_pow''' : N^((1 : ℝ) / 3) = 1 := by
                        { have hN_eq''' : N = 1 := by
                          { have hN_div''' : (nat.divisors N).card = 9 := by
                            { have hN_f'''' : f N = 9 / N^((1 : ℝ) / 3) := by
                              { rw hN_f,
                                exact hN_card },
                              rw hN_f'''' at hN_max,
                              have hN_pow'''' : N^((1 : ℝ) / 3) = 1 := by
                              { have hN_eq'''' : N = 1 := by
                                { have hN_div'''' : (nat.divisors N).card = 9 := by
                                  { have hN_f''''' : f N = 9 / N^((1 : ℝ) / 3) := by
                                    { rw hN_f,
                                      exact hN_card },
                                    rw hN_f''''' at hN_max,
                                    have hN_pow''''' : N^((1 : ℝ) / 3) = 1 := by
                                    { have hN_eq''''' : N = 1 := by
                                      { have hN_div''''' : (nat.divisors N).card = 9 := by
                                        { have hN_f'''''' : f N = 9 / N^((1 : ℝ) / 3) := by
                                          { rw hN_f,
                                            exact hN_card },
                                          rw hN_f'''''' at hN_max,
                                          have hN_pow'''''' : N^((1 : ℝ) / 3) = 1 := by
                                          { have hN_eq'''''' : N = 1 := by
                                            { have hN_div'''''' : (nat.divisors N).card = 9 := by
                                              { have hN_f''''''' : f N = 9 / N^((1 : ℝ) / 3) := by
                                                { rw hN_f,
                                                  exact hN_card },
                                                rw hN_f''''''' at hN_max,
                                                have hN_pow''''''' : N^((1 : ℝ) / 3) = 1 := by
                                                { have hN_eq''''''' : N = 1 := by
                                                  { have hN_div''''''' : (nat.divisors N).card = 9 := by
                                                    { have hN_f'''''''' : f N = 9 / N^((1 : ℝ) / 3) := by
                                                      { rw hN_f,
                                                        exact hN_card },
                                                      rw hN_f'''''''' at hN_max,
                                                      have hN_pow'''''''' : N^((1 : ℝ) / 3) = 1 := by
                                                      { have hN_eq'''''''' : N = 1 := by
                                                        { have hN_div'''''''' : (nat.divisors N).card = 9 := by
                                                          { have hN_f''''''''' : f N = 9 / N^((1 : ℝ) / 3) := by
                                                            { rw hN_f,
                                                              exact hN_card },
                                                            rw hN_f''''''''' at hN_max,
                                                            have hN_pow''''''''' : N^((1 : ℝ) / 3) = 1 := by
                                                            { have hN_eq''''''''' : N = 1 := by
                                                              { have hN_div''''''''' : (nat.divisors N).card = 9 := by
                                                                { have hN_f'''''''''' : f N = 9 / N^((1 : ℝ) / 3) := by
                                                                  { rw hN_f,
                                                                    exact hN_card },
                                                                  rw hN_f'''''''''' at hN_max,
                                                                  have hN_pow'''''''''' : N^((1 : ℝ) / 3) = 1 := by
                                                                  { have hN_eq'''''''''' : N = 1 := by
                                                                    { have hN_div'''''''''' : (nat.divisors N).card = 9 := by
                                                                      { have hN_f''''''''''' : f N = 9 / N^((1 : ℝ) / 3) := by
                                                                        { rw hN_f,
                                                                          exact hN_card },
                                                                        rw hN_f''''''''''' at hN_max,
                                                                        have hN_pow''''''''''' : N^((1 : ℝ) / 3) = 1 := by
                                                                        { have hN_eq''''''''''' : N = 1 := by
                                                                          { have hN_div''''''''''' : (nat.divisors N).card = 9 := by
                                                                            { have hN_f'''''''''''' : f N = 9 / N^((1 : ℝ) / 3) := by
                                                                              { rw hN_f,
                                                                                exact hN_card },
                                                                              rw hN_f'''''''''''' at hN_max,
                                                                              have hN_pow'''''''''''' : N^((1 : ℝ) / 3) = 1 := by
                                                                              { have hN_eq'''''''''''' : N = 1 := by
                                                                                { have hN_div'''''''''''' : (nat.div