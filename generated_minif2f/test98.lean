import Mathlib.Data.Nat.Digits
import Mathlib.Data.Finset
import Mathlib.Tactic

open Finset

theorem problem_statement :
  ∀ (n A B C : ℕ), 
  n = 3^17 + 3^10 → 
  11 ∣ (n + 1) → 
  [A,B,C].pairwise(≠) → 
  {A,B,C} ⊂ finset.Icc 0 9 → 
  odd A ∧ odd C → 
  ¬ 3 ∣ B → 
  nat.digits 10 n = [B,A,B,C,C,A,C,B,A] → 
  100 * A + 10 * B + C = 129 :=
begin
  intros n A B C hn hdiv hpw hsub hodd hdiv3 hd,
  have h1 : n = 3^17 + 3^10 := hn,
  have h2 : 11 ∣ (n + 1) := hdiv,
  have h3 : [A, B, C].pairwise (≠) := hpw,
  have h4 : {A, B, C} ⊂ Icc 0 9 := hsub,
  have h5 : odd A ∧ odd C := hodd,
  have h6 : ¬ 3 ∣ B := hdiv3,
  have h7 : nat.digits 10 n = [B, A, B, C, C, A, C, B, A] := hd,
  have h8 : n = 3^17 + 3^10 := by exact h1,
  have h9 : n = 1500946352961 := by norm_num [h8],
  have h10 : nat.digits 10 1500946352961 = [1, 3, 1, 9, 9, 3, 9, 1, 3] := by norm_num,
  rw h9 at h7,
  rw h10 at h7,
  injection h7 with hB hA hB' hC hC' hA' hC'' hB'' hA'',
  rw [hB, hA, hC],
  norm_num,
end