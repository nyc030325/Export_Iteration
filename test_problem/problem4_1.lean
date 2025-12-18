import Mathlib

/- 4_1: easy (prelemma given) -/
@[simp]
noncomputable instance real_smul_ereal : SMul ℝ EReal := ⟨fun a x => a * x⟩

@[mk_iff]
class ProperFunction {α : Type*} (s : Set α) (f : α → EReal) : Prop where
  -- f(x) > -∞
  uninfinity: (∀ x ∈ s, f x > ⊥)
  -- exist a x such that f(x) < +∞
  -- by_cases s is empty or nonempty
  existence_of_finite_value : (s = ∅) ∨ (∃ x ∈ s , f x < ⊤)

lemma EReal.mul_gt_bot {a b : EReal}
    (ha1 : a > ⊥) (ha2 : a < ⊤) (hb1 : b > ⊥) (hb2 : b < ⊤) :
    a * b > ⊥ := by
  lift a to ℝ using ⟨LT.lt.ne_top ha2, LT.lt.ne_bot ha1⟩
  lift b to ℝ using ⟨LT.lt.ne_top hb2, LT.lt.ne_bot hb1⟩
  exact Batteries.compareOfLessAndEq_eq_lt.mp rfl


lemma EReal.smul_add_pre (a : ℝ) {x y : EReal} (hx : x > ⊥) (hx1 : x < ⊤) (hy : y > ⊥) :
    a • (x + y) = a • x + a • y := by
  have h1 : a • (x + y) = a * (x + y) := rfl
  have h2 (z : EReal) : a • z = a * z := rfl
  rw [h1, h2 x, h2 y]
  lift x to ℝ using ⟨LT.lt.ne_top hx1, LT.lt.ne_bot hx⟩
  by_cases hy1 : y < ⊤
  lift y to ℝ using ⟨LT.lt.ne_top hy1, LT.lt.ne_bot hy⟩
  calc _
    _ = (a * x + a * y).toEReal := EReal.coe_eq_coe_iff.mpr (left_distrib a x y)
    _ = _ := by rfl
  rw [not_lt_top_iff.mp hy1, EReal.add_top_iff_ne_bot.mpr (LT.lt.ne_bot hx)]
  have ha : a > 0 ∨ a = 0 ∨ a < 0 := trichotomous a 0
  rcases ha with ha | ha | ha
  rw [EReal.coe_mul_top_of_pos ha]
  rw [EReal.add_top_iff_ne_bot.mpr
  (LT.lt.ne_bot <| mul_gt_bot (EReal.bot_lt_coe a) (EReal.coe_lt_top a) hx hx1)]
  rw [ha]
  simp
  rw [EReal.coe_mul_top_of_neg ha]
  exact Eq.symm (EReal.add_bot (↑a * x))

lemma EReal.smul_add (a : ℝ) {x y : EReal} (hx : x > ⊥) (hy : y > ⊥) :
    a • (x + y) = a • x + a • y := by
  by_cases hx1 : x < ⊤
  exact smul_add_pre a hx hx1 hy
  by_cases hy1 : y < ⊤
  rw [add_comm]
  nth_rw 2 [add_comm]
  exact smul_add_pre a hy hy1 hx
  have xtop : x = ⊤ := not_lt_top_iff.mp hx1
  have ytop : y = ⊤ := not_lt_top_iff.mp hy1
  have htop : (⊤ : EReal) + ⊤ = ⊤ := rfl
  have amul : a • (⊤ : EReal) = a * (⊤ : EReal) := rfl
  rw [xtop, ytop, htop, amul]
  have ha : a > 0 ∨ a = 0 ∨ a < 0 := trichotomous a 0
  rcases ha with ha | ha | ha
  rw [EReal.coe_mul_top_of_pos ha]; rfl
  rw [ha]; simp
  rw [EReal.coe_mul_top_of_neg ha]; rfl

lemma ProperFunctionConvexOn.add {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    {s : Set E} {f g : E → EReal}
    [hsf : ProperFunction s f] [hsg : ProperFunction s g]
    (hf : ConvexOn ℝ s f) (hg : ConvexOn ℝ s g) :
    ConvexOn ℝ s (f + g) := by
  exact
  ⟨hf.1, fun x hx y hy a b ha hb hab =>
  calc
    f (a • x + b • y) + g (a • x + b • y) ≤ a • f x + b • f y + (a • g x + b • g y) :=
      add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
    _ = a • (f x + g x) + b • (f y + g y) := by
      rw [EReal.smul_add a (hsf.uninfinity x hx) (hsg.uninfinity x hx),
        EReal.smul_add b (hsf.uninfinity y hy) (hsg.uninfinity y hy), add_add_add_comm]⟩
