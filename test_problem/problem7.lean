import Mathlib

/- medium -/
theorem Convex_first_order_condition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {f : E → ℝ} {f' : E → (E →L[ℝ] ℝ)} {x : E}
    (h : HasFDerivAt f (f' x) x) (hf : ConvexOn ℝ s f) (xs : x ∈ s) :
    ∀ y ∈ s, f x + f' x (y - x) ≤ f y := by
  intro y ys
  -- consider the real function obtained by restricting `f` to the line through `x` and `y`
  let inner : ℝ → E := fun t => x + t • (y - x)
  let g : ℝ → ℝ := fun t => f (inner t)
  have hinner_eq_line : inner = fun t => AffineMap.lineMap x y t := by
    funext t
    calc
      inner t = t • (y - x) + x := by simp [inner, add_comm, add_left_comm, add_assoc]
      _ = AffineMap.lineMap x y t := by
        simp [AffineMap.lineMap_apply_module', add_comm, add_left_comm, add_assoc]
  have hsubset : Set.Icc (0 : ℝ) 1 ⊆ inner ⁻¹' s := by
    intro t ht
    have : AffineMap.lineMap x y t ∈ s := by
      have hmem : AffineMap.lineMap x y t ∈ segment ℝ x y := by
        have : AffineMap.lineMap x y t ∈ (AffineMap.lineMap x y) '' (Set.Icc (0 : ℝ) 1) :=
          ⟨t, ht, rfl⟩
        simpa [segment_eq_image_lineMap] using this
      exact (hf.1.segment_subset xs ys) hmem
    simpa [inner, AffineMap.lineMap_apply_module', add_comm, add_left_comm, add_assoc] using this
  -- convexity of `g` on the preimage of `s`
  have hconv : ConvexOn ℝ (inner ⁻¹' s) g := by
    have hconv' : ConvexOn ℝ ((AffineMap.lineMap x y) ⁻¹' s)
        (fun t => f (AffineMap.lineMap x y t)) :=
      hf.comp_affineMap (AffineMap.lineMap x y)
    simpa [g, hinner_eq_line] using hconv'
  -- derivative of the parametrisation of the line
  have hinner_deriv : HasDerivAt inner (y - x) 0 := by
    have h'' : HasDerivAt (fun t : ℝ => t • (y - x)) (y - x) 0 := by
      simpa using (hasDerivAt_id (x := (0 : ℝ))).smul_const (y - x)
    simpa [inner] using h''.const_add x
  -- derivative of `g` at `0`
  have hderiv :
      HasDerivAt g (f' x (y - x)) 0 := by
    -- chain rule
    have hOuter : HasFDerivAt f (f' x) (inner 0) := by
      simpa [inner] using h
    have hgF :
        HasFDerivAt g
          ((f' x).comp
            (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (y - x))) 0 :=
      hOuter.comp 0 hinner_deriv.hasFDerivAt
    -- translate back to `HasDerivAt`
    simpa using (hgF.hasDerivAt)
  have hdiff : DifferentiableAt ℝ g 0 := hderiv.differentiableAt
  -- apply the one-dimensional slope bound
  have hx : (0 : ℝ) ∈ inner ⁻¹' s := hsubset (by constructor <;> norm_num)
  have hy : (1 : ℝ) ∈ inner ⁻¹' s := hsubset (by constructor <;> norm_num)
  have hineq :
      deriv g 0 ≤ slope g 0 1 :=
    hconv.deriv_le_slope hx hy (by norm_num) hdiff
  have hderiv' : deriv g 0 = f' x (y - x) := by
    simpa using hderiv.deriv
  have hslope : slope g 0 1 = f y - f x := by
    simp [g, inner, slope]
  -- rearrange
  have : f' x (y - x) ≤ f y - f x := by
    simpa [hderiv', hslope] using hineq
  linarith
