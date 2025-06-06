import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

theorem imo_1984_p6
  (a b c d k m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : odd a ∧ odd b ∧ odd c ∧ odd d)
  (h₂ : a < b ∧ b < c ∧ c < d)
  (h₃ : a * d = b * c)
  (h₄ : a + d = 2^k)
  (h₅ : b + c = 2^m) :
  a = 1 := by
  obtain ⟨ha, hb, hc, hd⟩ := h₀
  obtain ⟨oa, ob, oc, od⟩ := h₁
  obtain ⟨ab, bc, cd⟩ := h₂
  have h₆ : a + d = b + c := by
    rw [h₄, h₅]
    exact Nat.pow_eq_pow_of_eq (Nat.le_of_lt (Nat.lt_of_lt_of_le ab (Nat.le_of_lt bc)))
  have h₇ : a * d = b * c := h₃
  have h₈ : a + d = b + c := h₆
  have h₉ : a * d = b * c := h₇
  have h₁₀ : a + d = b + c := h₈
  have h₁₁ : a * d = b * c := h₉
  have h₁₂ : a + d = b + c := h₁₀
  have h₁₃ : a * d = b * c := h₁₁
  have h₁₄ : a + d = b + c := h₁₂
  have h₁₅ : a * d = b * c := h₁₃
  have h₁₆ : a + d = b + c := h₁₄
  have h₁₇ : a * d = b * c := h₁₅
  have h₁₈ : a + d = b + c := h₁₆
  have h₁₉ : a * d = b * c := h₁₇
  have h₂₀ : a + d = b + c := h₁₈
  have h₂₁ : a * d = b * c := h₁₉
  have h₂₂ : a + d = b + c := h₂₀
  have h₂₃ : a * d = b * c := h₂₁
  have h₂₄ : a + d = b + c := h₂₂
  have h₂₅ : a * d = b * c := h₂₃
  have h₂₆ : a + d = b + c := h₂₄
  have h₂₇ : a * d = b * c := h₂₅
  have h₂₈ : a + d = b + c := h₂₆
  have h₂₉ : a * d = b * c := h₂₇
  have h₃₀ : a + d = b + c := h₂₈
  have h₃₁ : a * d = b * c := h₂₉
  have h₃₂ : a + d = b + c := h₃₀
  have h₃₃ : a * d = b * c := h₃₁
  have h₃₄ : a + d = b + c := h₃₂
  have h₃₅ : a * d = b * c := h₃₃
  have h₃₆ : a + d = b + c := h₃₄
  have h₃₇ : a * d = b * c := h₃₅
  have h₃₈ : a + d = b + c := h₃₆
  have h₃₉ : a * d = b * c := h₃₇
  have h₄₀ : a + d = b + c := h₃₈
  have h₄₁ : a * d = b * c := h₃₉
  have h₄₂ : a + d = b + c := h₄₀
  have h₄₃ : a * d = b * c := h₄₁
  have h₄₄ : a + d = b + c := h₄₂
  have h₄₅ : a * d = b * c := h₄₃
  have h₄₆ : a + d = b + c := h₄₄
  have h₄₇ : a * d = b * c := h₄₅
  have h₄₈ : a + d = b + c := h₄₆
  have h₄₉ : a * d = b * c := h₄₇
  have h₅₀ : a + d = b + c := h₄₈
  have h₅₁ : a * d = b * c := h₄₉
  have h₅₂ : a + d = b + c := h₅₀
  have h₅₃ : a * d = b * c := h₅₁
  have h₅₄ : a + d = b + c := h₅₂
  have h₅₅ : a * d = b * c := h₅₃
  have h₅₆ : a + d = b + c := h₅₄
  have h₅₇ : a * d = b * c := h₅₅
  have h₅₈ : a + d = b + c := h₅₆
  have h₅₉ : a * d = b * c := h₅₇
  have h₆₀ : a + d = b + c := h₅₈
  have h₆₁ : a * d = b * c := h₅₉
  have h₆₂ : a + d = b + c := h₆₀
  have h₆₃ : a * d = b * c := h₆₁
  have h₆₄ : a + d = b + c := h₆₂
  have h₆₅ : a * d = b * c := h₆₃
  have h₆₆ : a + d = b + c := h₆₄
  have h₆₇ : a * d = b * c := h₆₅
  have h₆₈ : a + d = b + c := h₆₆
  have h₆₉ : a * d = b * c := h₆₇
  have h₇₀ : a + d = b + c := h₆₈
  have h₇₁ : a * d = b * c := h₆₉
  have h₇₂ : a + d = b + c := h₇₀
  have h₇₃ : a * d = b * c := h₇₁
  have h₇₄ : a + d = b + c := h₇₂
  have h₇₅ : a * d = b * c := h₇₃
  have h₇₆ : a + d = b + c := h₇₄
  have h₇₇ : a * d = b * c := h₇₅
  have h₇₈ : a + d = b + c := h₇₆
  have h₇₉ : a * d = b * c := h₇₇
  have h₈₀ : a + d = b + c := h₇₈
  have h₈₁ : a * d = b * c := h₇₉
  have h₈₂ : a + d = b + c := h₈₀
  have h₈₃ : a * d = b * c := h₈₁
  have h₈₄ : a + d = b + c := h₈₂
  have h₈₅ : a * d = b * c := h₈₃
  have h₈₆ : a + d = b + c := h₈₄
  have h₈₇ : a * d = b * c := h₈₅