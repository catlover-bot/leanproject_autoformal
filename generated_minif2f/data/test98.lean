import data.nat.digits
import data.finset
import data.nat.parity
import algebra.big_operators.basic

open finset
open_locale big_operators

theorem digits_theorem :
  ∀ (n A B C : ℕ),
    n = 3^17 + 3^10 →
    11 ∣ (n + 1) →
    [A, B, C].pairwise (≠) →
    {A, B, C} ⊂ Icc 0 9 →
    odd A ∧ odd C →
    ¬ 3 ∣ B →
    nat.digits 10 n = [B, A, B, C, C, A, C, B, A] →
    100 * A + 10 * B + C = 129 :=
begin
  intros n A B C hn hdiv hpw hsub hodd hnotdiv hdigs,
  have hA : A ∈ Icc 0 9 := (mem_of_subset hsub (mem_insert_self A {B, C})),
  have hB : B ∈ Icc 0 9 := (mem_of_subset hsub (mem_insert_of_mem (mem_insert_self B {C}))),
  have hC : C ∈ Icc 0 9 := (mem_of_subset hsub (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self C)))),
  
  have hA_odd : A % 2 = 1 := hodd.1,
  have hC_odd : C % 2 = 1 := hodd.2,
  
  have hB_notdiv3 : B % 3 ≠ 0 := hnotdiv,
  
  have hn_val : n = 3^17 + 3^10 := hn,
  have hdiv11 : 11 ∣ (n + 1) := hdiv,
  
  have hdigit : nat.digits 10 n = [B, A, B, C, C, A, C, B, A] := hdigs,
  
  -- Calculate n explicitly
  have hn_calc : n = 3^17 + 3^10 := hn,
  have hn_val : n = 129140163 + 59049 := by norm_num,
  rw hn_val at hn_calc,
  
  -- Check divisibility by 11
  have hdiv11_check : 11 ∣ (129140163 + 59049 + 1) := by norm_num,
  rw hn_calc at hdiv11,
  
  -- Analyze the digit representation
  have hdigit_check : nat.digits 10 (129140163 + 59049) = [1, 2, 1, 9, 9, 2, 9, 1, 2] := by norm_num,
  rw hdigit_check at hdigit,
  
  -- Assign values to A, B, C
  have hA_val : A = 2 := by { rw hdigit at hdigit_check, exact hdigit_check.2.2.2.2.2.2.2.2.1 },
  have hB_val : B = 1 := by { rw hdigit at hdigit_check, exact hdigit_check.2.2.2.2.2.2.2.1 },
  have hC_val : C = 9 := by { rw hdigit at hdigit_check, exact hdigit_check.2.2.2.2.2.2.1 },
  
  -- Calculate 100 * A + 10 * B + C
  have hcalc : 100 * A + 10 * B + C = 100 * 2 + 10 * 1 + 9 := by rw [hA_val, hB_val, hC_val],
  norm_num at hcalc,
  exact hcalc,
end