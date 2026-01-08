import Mathlib
import Mathlib.Tactic











theorem theorem_279215_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  (x : ℕ → X)
  (R : X →L[𝕜] Y)
  (h : CauchySeq x) :
  CauchySeq (fun n ↦ R (x n)) := by
  sorry













theorem theorem_280068_problem (n : ℕ)
  (x : Matrix (Fin n) (Fin 1) ℝ)
  (A : Matrix (Fin n) (Fin n) ℝ) :
  Matrix.transpose x * (A * x) = Matrix.transpose (A * x) * x := by
  sorry

















theorem theorem_280047_problem (n : ℕ) (hn : n ≥ 3)
  (Y : Set (Fin n → ℝ))
  (hY : ∃ (a : Fin n → ℝ) (b : ℝ), a ≠ 0 ∧ Y = {y | ∑ i, a i * y i = b})
  (Δ : Set (Fin n → ℝ))
  (hΔ : Δ = {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1})
  (h_inter : (Y ∩ intrinsicInterior ℝ Δ).Nonempty) :
  ∃ f : (Fin n → ℝ) → ℝ,
    (∀ x, 0 ≤ f x) ∧
    (∀ x, f x = 0 ↔ x = 0) ∧
    (∀ c x, f (c • x) = |c| * f x) ∧
    (∀ x y, f (x + y) ≤ f x + f y) ∧
    ContDiffOn ℝ 1 f {0}ᶜ ∧
    StrictConvex ℝ {x | f x ≤ 1} ∧
    ∃ x_min ∈ Y ∩ Δ, IsMinOn f (Y ∩ Δ) x_min ∧ x_min ∈ intrinsicFrontier ℝ (Y ∩ Δ) := by
  sorry

theorem theorem_280298_problem (n : ℕ) (c : Fin n → ℂ) :
  convexHull ℝ (Set.range c) =
  {z : ℂ | ∃ (a : Fin n → ℝ), (∀ i, 0 ≤ a i) ∧ (∑ i, a i = 1) ∧ z = ∑ i, a i • c i} := by
  sorry

theorem theorem_279820_problem
  (U : Set (Fin 2 → ℝ))
  (hU : IsOpen U)
  (f : (Fin 2 → ℝ) → (Fin 3 → ℝ))
  (hf : ContDiffOn ℝ 2 f U)
  (u : Fin 2 → ℝ)
  (hu : u ∈ U)
  -- Definitions of partial derivatives corresponding to f_{u_i}
  (f_u : Fin 2 → (Fin 3 → ℝ))
  (h_fu : ∀ i, f_u i = fderiv ℝ f u (Pi.single i 1))
  -- Definitions of second partial derivatives corresponding to f_{u_i u_j}
  (f_uu : Fin 2 → Fin 2 → (Fin 3 → ℝ))
  (h_fuu : ∀ i j, f_uu i j = fderiv ℝ (fun p => fderiv ℝ f p (Pi.single i 1)) u (Pi.single j 1))
  -- Definition of the Euclidean dot product in R^3
  (dot : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ)
  (h_dot : ∀ v w, dot v w = ∑ k, v k * w k)
  -- The first fundamental form matrix I
  (I_mat : Matrix (Fin 2) (Fin 2) ℝ)
  (h_I : ∀ i j, I_mat i j = dot (f_u i) (f_u j))
  -- Condition: I is positive definite
  (h_pos : I_mat.PosDef) :
  -- Conclusion: The Christoffel symbols are uniquely determined by the system
  ∀ i j : Fin 2, ∃! Γ : Fin 2 → ℝ,
    ∀ k : Fin 2, dot (f_uu i j) (f_u k) =
      Γ 0 * dot (f_u 0) (f_u k) + Γ 1 * dot (f_u 1) (f_u k) := by
  sorry





theorem theorem_280545_problem
  {K V U : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : ℕ}
  (g : Fin n → Module.Dual K V)
  (f : Fin n → U → K)
  (hg : LinearIndependent K g)
  (h_sum : ∀ u : U, ∑ i : Fin n, f i u • g i = 0) :
  ∀ i : Fin n, f i = 0 := by
  sorry















theorem theorem_280499_problem (g : ℝ → ℝ)
  (h_rat : ∀ (q : ℚ), g q = 1 / (q.den : ℝ))
  (h_irr : ∀ (x : ℝ), Irrational x → g x = 0)
  (x₀ : ℝ) (hx₀ : Irrational x₀) :
  ContinuousAt g x₀ := by
  sorry



theorem theorem_280370_problem (v w : Fin 3 → ℝ)
  (v_times : Matrix (Fin 3) (Fin 3) ℝ)
  (h_def : v_times = !![0, -v 2, v 1;
                        v 2, 0, -v 0;
                        -v 1, v 0, 0]) :
  Matrix.mulVec v_times w = crossProduct v w := by
  sorry

theorem theorem_280756_problem {n : ℕ} {F : Type*} [Field F]
  (A B : Matrix (Fin n) (Fin n) F) :
  Matrix.det (A * B) = Matrix.det A * Matrix.det B := by
  sorry

theorem theorem_280428_problem
  (a b : ℝ)
  (h_ab : a < b)
  (f : ℝ → ℝ)
  (hf : ContinuousOn f (Set.Icc a b))
  (g : ℝ → ℝ)
  (hg : ∀ x ∈ Set.Icc a b, g x = sSup (f '' Set.Icc a x)) :
  ContinuousOn g (Set.Icc a b) := by
  sorry



















theorem theorem_281458_problem
  {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Type*}
  (f : X₁ → Y₁) (g : X₂ → Y₂)
  (f' : Y₁ → Z₁) (g' : Y₂ → Z₂) :
  (Prod.map f' g') ∘ (Prod.map f g) = Prod.map (f' ∘ f) (g' ∘ g) := by
  sorry



theorem theorem_281188_problem
  (X Y : Type*)
  [NormedAddCommGroup X] [NormedSpace ℝ X] [Nontrivial X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (hY : ¬ CompleteSpace Y) :
  ∃ T : ℕ → (X →L[ℝ] Y), CauchySeq T ∧ ¬ ∃ L : X →L[ℝ] Y, Filter.Tendsto T Filter.atTop (nhds L) := by
  sorry

theorem theorem_281742_problem
  (d : ℕ)
  (K : Set (Fin d → ℝ))
  (A : (Fin d → ℝ) →ₗ[ℝ] ℝ)
  (h_closed : IsClosed K)
  (h_convex : Convex ℝ K)
  (h_cone : ∀ x ∈ K, ∀ r : ℝ, 0 ≤ r → r • x ∈ K) :
  IsClosed (A '' K) := by
  sorry









theorem theorem_281680_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA : IsUnit A) (hB : IsUnit B)
  (h : A * A.transpose = B * B.transpose) :
  ∃ Q : Matrix (Fin n) (Fin n) ℝ, Q * Q.transpose = 1 ∧ B = Q * A := by
  sorry







theorem theorem_282050_problem
  {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (T : H →L[𝕜] H) :
  ‖ContinuousLinearMap.adjoint T ∘L T‖ = ‖T‖ ^ 2 := by
  sorry









theorem theorem_282281_problem
  (M : ℕ)
  (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (Y : Set E)
  (X : Type*)
  (f : X → Y)
  (S : Set E)
  (s : E) (hs : s ∈ S)
  (epsilon : Y → ℝ)
  (pi : E → Y) :
  ∀ x : X, ↑(pi (↑(f x) + epsilon (f x) • s)) ∈ Y := by
  sorry



theorem theorem_282703_problem
  {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  (T : X →ₗ[ℝ] Y)
  (h : ∀ (x_n : ℕ → X) (x : X) (y : Y),
    Filter.Tendsto x_n Filter.atTop (nhds x) →
    Filter.Tendsto (fun n ↦ T (x_n n)) Filter.atTop (nhds y) →
    y = T x) :
  Continuous T := by
  sorry

theorem theorem_282009_problem
  (n p : ℕ)
  (Ω : Type*)
  (X_bar : Ω → (Fin p → ℝ))
  (μ : Fin p → ℝ)
  (S : Ω → Matrix (Fin p) (Fin p) ℝ)
  (c : ℝ)
  (hn : 0 < n)
  (hc : 0 < c)
  (f : Ω → (Fin p → ℝ) → ℝ)
  (hf : ∀ ω a, f ω a = |(Real.sqrt n * Matrix.dotProduct a (X_bar ω - μ)) / Real.sqrt (Matrix.dotProduct a (Matrix.mulVec (S ω) a))|)
  (A : Set Ω)
  (hA : A = ⋃ a : Fin p → ℝ, {ω | f ω a > c})
  (B : Set Ω)
  (hB : B = {ω | (⨆ a : Fin p → ℝ, f ω a) > c}) :
  A = B := by
  sorry









theorem theorem_283104_problem (n : ℕ) (hn : 0 < n) (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
  ∃ W : Submodule ℝ (Fin n → ℝ), Submodule.map A W ≤ W ∧
  (FiniteDimensional.finrank ℝ W = 1 ∨ FiniteDimensional.finrank ℝ W = 2) := by
  sorry



theorem theorem_282882_problem
  (x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ x₄ y₄ z₄ : ℝ) :
  let P₁ : Fin 3 → ℝ := ![x₁, y₁, z₁]
  let P₂ : Fin 3 → ℝ := ![x₂, y₂, z₂]
  let P₃ : Fin 3 → ℝ := ![x₃, y₃, z₃]
  let P₄ : Fin 3 → ℝ := ![x₄, y₄, z₄]
  let A : Matrix (Fin 4) (Fin 4) ℝ := !![x₁, x₂, x₃, x₄;
                                         y₁, y₂, y₃, y₄;
                                         z₁, z₂, z₃, z₄;
                                         1,  1,  1,  1]
  Coplanar ℝ ({P₁, P₂, P₃, P₄} : Set (Fin 3 → ℝ)) ↔ A.det = 0 := by
  sorry











theorem theorem_282909_problem
  (u1 v1 w1 u2 v2 w2 : EuclideanSpace ℝ (Fin 3))
  (S : Set (EuclideanSpace ℝ (Fin 3)))
  (hS : S = {u1, v1, w1, u2, v2, w2})
  (T1 : Set (EuclideanSpace ℝ (Fin 3)))
  (hT1 : T1 = convexHull ℝ {u1, v1, w1})
  (T2 : Set (EuclideanSpace ℝ (Fin 3)))
  (hT2 : T2 = convexHull ℝ {u2, v2, w2})
  (h_nondeg1 : AffineIndependent ℝ ![u1, v1, w1])
  (h_nondeg2 : AffineIndependent ℝ ![u2, v2, w2])
  (P1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
  (hP1 : P1 = affineSpan ℝ {u1, v1, w1})
  (P2 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
  (hP2 : P2 = affineSpan ℝ {u2, v2, w2})
  (h_par : P1.direction = P2.direction)
  (h_dist : P1 ≠ P2)
  (x1 x2 : EuclideanSpace ℝ (Fin 3))
  (hx1 : x1 ∈ intrinsicInterior ℝ T1)
  (hx2 : x2 ∈ intrinsicInterior ℝ T2)
  (C : Set (EuclideanSpace ℝ (Fin 3)))
  (hC_conv : Convex ℝ C)
  (hC_sub : C ⊆ convexHull ℝ S)
  (h_x1 : x1 ∈ C)
  (h_x2 : x2 ∈ C) :
  S ⊆ C := by
  sorry







theorem theorem_283812_problem (F : Type*) (V : Type*) [Field F] [AddCommGroup V] [Module F V] :
  ∃ B : Set V, LinearIndependent F (Subtype.val : B → V) ∧ Submodule.span F B = ⊤ := by
  sorry

theorem theorem_282988_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (Ω₁ Ω₂ : Set E)
  (hΩ₁ : Bornology.IsBounded Ω₁)
  (hΩ₂_bd : Bornology.IsBounded Ω₂)
  (hΩ₂_cp : IsCompact Ω₂)
  (h_int : 0 ∈ interior Ω₂)
  (δ : ℝ) (hδ : 0 < δ) :
  ∃ ε > 0, ∀ z : E, ∀ x₀ ∈ frontier Ω₂,
    x₀ ∈ Metric.sphere z δ →
    inner (z - x₀) x₀ > ε * δ * ‖x₀‖ := by
  sorry





theorem theorem_284057_problem (A : Matrix (Fin 2) (Fin 2) ℤ) 
  (h : IsUnit A) : 
  A.det = 1 ∨ A.det = -1 := by
  sorry

theorem theorem_284103_problem
  (m n : ℕ)
  (F : Matrix (Fin m) (Fin n) ℝ)
  (h_skinny : m < n)
  (h_full_rank : F.transpose.rank = m) :
  LinearMap.ker (Matrix.toLin' (F * F.transpose)) = ⊥ := by
  sorry

theorem theorem_283865_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : E → F) (x : E) (M : ℝ)
  (h_diff : DifferentiableAt ℝ f x)
  (h_bound : ∃ δ₀ > 0, ∀ h : E, ‖h‖ < δ₀ → ‖f (x + h) - f x‖ ≤ M * ‖h‖) :
  ∀ ε > 0, ∃ δ > 0, ∀ h : E, ‖h‖ < δ → ‖fderiv ℝ f x h‖ ≤ (M + ε) * ‖h‖ := by
  sorry



theorem theorem_284077_problem
  (n : ℕ)
  (P : Matrix (Fin n) (Fin n) ℝ)
  (q : Fin n → ℝ)
  (r : ℝ)
  (hP_symm : P.IsSymm)
  (hP_off_diag : ∀ i j, i ≠ j → P i j ≤ 0) :
  ConvexOn ℝ {y : Fin n → ℝ | ∀ i, 0 ≤ y i}
    (fun y =>
      (1 / 2 : ℝ) * (∑ i, P i i * y i) +
      (∑ i, ∑ j, if i ≠ j then P i j * Real.sqrt (y i * y j) else 0) +
      (∑ i, q i * Real.sqrt (y i)) +
      r) := by
  sorry



theorem theorem_283834_problem
  {K : Type*} [NormedField K]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace K V]
  {n : ℕ}
  (u : Fin n → V)
  (h_ind : LinearIndependent K u) :
  ∃ c : ℝ, c > 0 ∧ ∀ (α : Fin n → K),
    ‖∑ i, α i • u i‖ ≥ c * ∑ i, ‖α i‖ := by
  sorry







theorem theorem_284504_problem (a b : ℝ) (ha : 0 < a) :
  let H : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
    {M | ∃ u : ℝ, 0 < u ∧ M = !![u, 0; 0, 1]}
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; 0, 1]
  let Target : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
    {M | ∃ x y : ℝ, 0 < x ∧ M = !![x, y; 0, 1] ∧ x⁻¹ * y = a⁻¹ * b}
  (H.image (fun h => h * A)) = Target := by
  sorry

