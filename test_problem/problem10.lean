import Mathlib

set_option maxHeartbeats 1000000

open Set

/- hard -/
theorem openSegment_sub_intrinsicInterior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hsc : Convex ℝ s) {x y : E}
    (hx : x ∈ intrinsicInterior ℝ s) (hy : y ∈ intrinsicClosure ℝ s) :
    openSegment ℝ x y ⊆ intrinsicInterior ℝ s := by
  classical
  -- Work inside the affine span of `s`.
  obtain ⟨xA, hxA, rfl⟩ := mem_intrinsicInterior.mp hx
  obtain ⟨yA, hyA, rfl⟩ := mem_intrinsicClosure.mp hy
  let A : AffineSubspace ℝ E := affineSpan ℝ s
  haveI : Nonempty A := ⟨xA⟩
  let sA : Set A := ((↑) ⁻¹' s : Set A)
  let φ : A ≃ᵃⁱ[ℝ] A.direction := AffineIsometryEquiv.constVSub ℝ xA
  let t : Set A.direction := φ.symm ⁻¹' sA
  let g : A.direction →ᵃ[ℝ] E := A.subtype.comp φ.symm.toAffineMap
  -- `t` is the preimage of `s` under `g`, hence convex.
  have hconv : Convex ℝ t := by
    have ht : t = g ⁻¹' s := by
      ext v
      simp [t, g, sA, Function.comp]
    simpa [ht] using hsc.affine_preimage g
  -- φ transports interior/closure between `sA` and `t`.
  have hpre_img : φ '' sA = t := by
    simpa [t] using (φ.image_eq_preimage sA)
  have hinterior_t : interior t = φ '' interior sA := by
    have h := φ.toHomeomorph.image_interior sA
    calc
      interior t = interior (φ '' sA) := by simp [hpre_img]
      _ = φ '' interior sA := h.symm
  have hclosure_t : closure t = φ '' closure sA := by
    have h := φ.toHomeomorph.image_closure sA
    calc
      closure t = closure (φ '' sA) := by simp [hpre_img]
      _ = φ '' closure sA := h.symm
  -- Coordinates of the endpoints in the direction space.
  have hφx : φ xA = 0 := by simp [φ, AffineIsometryEquiv.coe_constVSub]
  have hsymm0 : φ.symm (0 : A.direction) = xA := by
    simpa [hφx] using (φ.left_inv xA)
  -- Simplify the interior/closure hypotheses.
  have hxA' : xA ∈ interior sA := by simpa [sA] using hxA
  have hyA' : yA ∈ closure sA := by simpa [sA] using hyA
  have hx0 : (0 : A.direction) ∈ interior t := by
    have hx_im : φ xA ∈ φ '' interior sA := ⟨xA, hxA', rfl⟩
    simpa [hinterior_t, hφx] using hx_im
  have hy0 : φ yA ∈ closure t := by
    have hy_im : φ yA ∈ φ '' closure sA := ⟨yA, hyA', rfl⟩
    simpa [hclosure_t] using hy_im
  -- Segment inside the direction space lies in the interior.
  have hseg_dir :
      openSegment ℝ (0 : A.direction) (φ yA) ⊆ interior t :=
    hconv.openSegment_interior_closure_subset_interior hx0 hy0
  -- Image of the segment under `g` is the original segment.
  have hg0 : g 0 = (xA : E) := by simp [g, hsymm0]
  have hgφ : g (φ yA) = (yA : E) := by simp [g, φ]
  have hopenseg_g :
      g '' openSegment ℝ (0 : A.direction) (φ yA) =
        openSegment ℝ (xA : E) (yA : E) := by
    simp [hg0, hgφ]
  -- Now take a point on the segment, pull it back, and use interior membership.
  intro z hz
  have hz_dir : z ∈ g '' openSegment ℝ (0 : A.direction) (φ yA) := by
    simpa [hopenseg_g] using hz
  rcases hz_dir with ⟨v, hv, rfl⟩
  have hv_int : v ∈ interior t := hseg_dir hv
  have hv_im : v ∈ φ '' interior sA := by simpa [hinterior_t] using hv_int
  rcases hv_im with ⟨w, hw, rfl⟩
  -- `g` sends `w` to the corresponding point in `E`.
  have : (A.subtype) w ∈ intrinsicInterior ℝ s := by
    -- intrinsicInterior is the image of `interior sA` under the subtype map.
    refine ⟨w, ?_, rfl⟩
    simpa [sA] using hw
  simpa [g] using this
