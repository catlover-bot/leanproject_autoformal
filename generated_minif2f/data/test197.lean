```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open Nat

theorem even_m_n_sub_eq_prod_eq (m n : ℕ) (hm : even m) (hn : even n) (h1 : m - n = 2) (h2 : m * n = 288) : m = 18 := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  rw [ha, hb] at h1 h2
  have h1' : 2 * a - 2 * b = 2 := h1
  have h2' : (2 * a) * (2 * b) = 288 := h2
  rw [mul_sub, mul_comm 2 b, mul_comm 2 a, ← two_mul, ← two_mul] at h1'
  rw [mul_assoc, mul_assoc, mul_comm 2, ← mul_assoc, ← mul_assoc, mul_comm 2] at h2'
  have : a - b = 1 := by
    linarith
  have : 4 * a * b = 288 := h2'
  have : a * b = 72 := by
    linarith
  have : a = b + 1 := by
    linarith
  rw [this] at this
  have : (b + 1) * b = 72 := this
  have : b^2 + b - 72 = 0 := by
    ring_nf at this
    exact this
  have : b = 8 := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 1 < 2)
    norm_num at this
    exact this
  have : a = 9 := by
    rw [this] at this
    linarith
  have : m = 2 * a := ha
  rw [this, this]
  norm_num
```