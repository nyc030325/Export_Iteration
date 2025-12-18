import Mathlib

open Set Topology Filter

/- easy -/
theorem lowerSemicontinuousOn_iff {E : Type} [NormedAddCommGroup E] {s : Set E} {f : E → EReal} :
    LowerSemicontinuousOn f s ↔
    ∀ x ∈ s, ∀ y, f x ∈ Ioi y → ∃ u, IsOpen u ∧ x ∈ u ∧ u ∩ s ⊆ f ⁻¹' Ioi y := by
  simp [LowerSemicontinuousOn, LowerSemicontinuousWithinAt]
  exact forall₃_congr fun a _ c ↦
    imp_congr_right fun _ ↦ ⟨fun hx ↦ mem_nhdsWithin.mp hx,
    fun ⟨u, hu⟩ ↦ eventually_iff_exists_mem.mpr
    ⟨u ∩ s, mem_nhdsWithin.mpr ⟨u, hu.1, hu.2.1 , by simp⟩, fun _ hy => hu.2.2 hy⟩⟩
