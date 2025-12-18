import Mathlib

/- hard -/
@[simp]
noncomputable instance real_smul_ereal : SMul ℝ EReal := ⟨fun a x => a * x⟩

@[mk_iff]
class ProperFunction {α : Type*} (s : Set α) (f : α → EReal) : Prop where
  -- f(x) > -∞
  uninfinity: (∀ x ∈ s, f x > ⊥)
  -- exist a x such that f(x) < +∞
  -- by_cases s is empty or nonempty
  existence_of_finite_value : (s = ∅) ∨ (∃ x ∈ s , f x < ⊤)

lemma ProperFunctionConvexOn.add {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    {s : Set E} {f g : E → EReal}
    [hsf : ProperFunction s f] [hsg : ProperFunction s g]
    (hf : ConvexOn ℝ s f) (hg : ConvexOn ℝ s g) :
    ConvexOn ℝ s (f + g) :=
  sorry
