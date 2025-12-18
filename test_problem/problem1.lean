import Mathlib

open InnerProductSpace Set

/- easy -/
lemma EReal.add_le_iff_sub_le (a b : ℝ) (c : EReal) :
    a + b ≤ c ↔ a - c ≤ -b := by
  rw [← EReal.coe_add, ← EReal.coe_neg]
  by_cases hc : c = ⊤
  rw [hc]
  simp only [coe_add, le_top, sub_top, coe_neg, bot_le]
  by_cases hc' : c = ⊥
  rw [hc']
  simp only [coe_add, le_bot_iff, add_eq_bot_iff, coe_ne_bot, or_self, coe_sub_bot, coe_neg,
      top_le_iff, neg_eq_top_iff]
  lift c to ℝ using ⟨hc, hc'⟩
  rw [EReal.coe_le_coe_iff]
  symm
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
  simp only [tsub_le_iff_right, le_neg_add_iff_add_le]
  ring_nf
