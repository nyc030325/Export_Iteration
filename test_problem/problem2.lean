import Mathlib

open InnerProductSpace Set

/- easy -/
theorem Convergence_Continuous {E : Type*} [NormedAddCommGroup E] {f : E → ℝ}
    {x : E} (h : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E),
    ‖x - x'‖ ≤ δ → ‖f x' - f x‖ ≤ ε) : ContinuousAt f x := by
  rw [continuousAt_def]
  intro A amem
  rw [Metric.mem_nhds_iff] at amem
  rcases amem with ⟨ε, epos, bmem⟩
  specialize h (ε / 2) (half_pos epos)
  rcases h with ⟨δ , dpos, h⟩
  rw [Metric.mem_nhds_iff]
  use δ; constructor
  exact dpos
  rw [Set.subset_def]
  intro x' x1mem
  have : ‖x - x'‖ ≤ δ := by
    rw [Metric.ball, Set.mem_setOf, dist_comm, dist_eq_norm_sub] at x1mem
    exact LT.lt.le x1mem
  specialize h x' this
  have H1: f x' ∈  Metric.ball (f x) ε := by
    rw [Metric.ball, Set.mem_setOf, dist_eq_norm_sub]
    apply lt_of_le_of_lt h (half_lt_self epos)
  exact bmem H1
