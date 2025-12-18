import Mathlib

open Set

/- hard -/
theorem Strong_convex_Lipschitz_smooth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {m : ℝ} {f' : E → E} {xm x₀ : E} {x : ℕ → E}
    {a : ℝ} {x y : E} {l : NNReal}
    (hsc : StrongConvexOn univ m f) (mp : m > 0)
    (hf : ∀ x, HasGradientAt f (f' x) x) (h₂ : LipschitzWith l f') (hl : l > (0 : ℝ)) :
    inner (f' x - f' y) (x - y) ≥ m * l / (m + l) * ‖x - y‖ ^ 2
    + 1 / (m + l) * ‖f' x - f' y‖ ^ 2 := by
  sorry
