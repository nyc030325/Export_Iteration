import Mathlib
import Mathlib.Tactic

















theorem theorem_48292_problem
  (n : ℕ)
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA_symm : A.IsSymm)
  (hA_pos : A.PosDef)
  (hB_symm : B.IsSymm)
  (S : Matrix (Fin n) (Fin n) ℝ)
  (hS_def : S.PosDef ∧ S ^ 2 = A)
  (H : Matrix (Fin n) (Fin n) ℝ)
  (hH_def : H = S * B * S) :
  H.charpoly = B.charpoly := by
  sorry

theorem theorem_49038_problem (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
  gradient (fun (x : EuclideanSpace ℝ (Fin n)) ↦ ∑ i : Fin n, (x i)^2) u = (2 : ℝ) • u := by
  sorry

theorem theorem_48004_problem (xn : ℕ → ℝ) (x : ℝ)
  (h : Filter.Tendsto xn Filter.atTop (nhds x)) :
  Filter.Tendsto (fun n ↦ |xn n|) Filter.atTop (nhds |x|) := by
  sorry

theorem theorem_48570_problem
  (n m : ℕ)
  (h_nm : n < m)
  (X : Matrix (Fin n) (Fin m) ℝ)
  (h_rank : X.rank = n)
  (X_R : Matrix (Fin m) (Fin n) ℝ)
  (h_def : X_R = X.transpose * (X * X.transpose)⁻¹)
  (y : Fin n → ℝ) :
  X.mulVec (X_R.mulVec y) = y := by
  sorry

theorem theorem_48916_problem
  (n : ℕ)
  (L : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ))
  (y : Fin n → ℝ → ℝ)
  (h_sol : ∀ i, L (y i) = 0)
  (c : Fin n → ℝ) :
  L (∑ i, c i • y i) = 0 := by
  sorry



theorem theorem_48095_problem
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix m n ℝ)
  (U : Matrix m m ℝ)
  (V : Matrix n n ℝ)
  (hU : U.transpose * U = 1)
  (hV : V.transpose * V = 1) :
  Real.sqrt (Matrix.trace ((U * A * V.transpose).transpose * (U * A * V.transpose))) =
  Real.sqrt (Matrix.trace (A.transpose * A)) := by
  sorry







theorem theorem_48143_problem {n : ℕ} {R : Type*} [CommRing R]
  (A : Matrix (Fin n) (Fin n) R)
  (i j : Fin n) (hneq : i ≠ j) (β : R)
  (A' : Matrix (Fin n) (Fin n) R)
  (hA' : A' = fun r c => if c = i then A r c + β * A r j else A r c) :
  A.det = A'.det := by
  sorry

theorem theorem_48174_problem
  (y1 y2 : ℝ → ℝ)
  (h1 : Differentiable ℝ y1)
  (h2 : Differentiable ℝ y2)
  (y : ℝ → ℝ × ℝ) (hy : y = fun t ↦ (y1 t, y2 t))
  (y_1 : ℝ → ℝ × ℝ) (hy1 : y_1 = y)
  (y_2 : ℝ → ℝ × ℝ) (hy2 : y_2 = deriv y_1)
  (y_bold : ℝ → ℝ × ℝ × ℝ × ℝ)
  (hy_bold : y_bold = fun t ↦ ((y_1 t).1, (y_1 t).2, (y_2 t).1, (y_2 t).2)) :
  y_bold 0 = (y1 0, y2 0, deriv y1 0, deriv y2 0) := by
  sorry













theorem theorem_48772_problem (f g : ℝ → ℂ)
  (hf : MeasureTheory.Integrable f) (hg : MeasureTheory.Integrable g) :
  let convolution := fun (f g : ℝ → ℂ) (t : ℝ) ↦ ∫ τ, f τ * g (t - τ)
  let fourier := fun (h : ℝ → ℂ) (ω : ℝ) ↦ ∫ t, h t * Complex.exp (-Complex.I * ω * t)
  fourier (convolution f g) = (fun ω ↦ fourier f ω * fourier g ω) := by
  sorry

theorem theorem_48121_problem (n : ℕ) (hn : n > 0) :
  ∃ L : ℝ, ∀ (f : ℂ → ℂ) (a : ℕ → ℂ),
    DifferentiableOn ℂ f (Metric.ball 0 1) →
    (∀ z ∈ Metric.ball 0 1, f z ≠ 0) →
    (∀ z ∈ Metric.ball 0 1, ‖f z‖ < 1) →
    (∀ z ∈ Metric.ball 0 1, HasSum (fun k => a k * z ^ k) (f z)) →
    ‖∑ k in Finset.range (n + 1), a k‖ ≤ L := by
  sorry

theorem theorem_33080_problem (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (x : Fin n → ℝ)
  (phi : Fin n → ℝ)
  (delta : Fin n → Fin n → ℝ)
  (h_delta : ∀ i j, delta i j = if i = j then 1 else 0)
  (h_phi : ∀ i, phi i = ∑ j, A i j * x j)
  (h_fixed : ∀ i, phi i = x i) :
  ∀ i, ∑ j, (delta i j - A i j) * x j = 0 := by
  sorry

theorem theorem_49139_problem (n : ℕ) :
  FiniteDimensional.finrank ℝ ↥(selfAdjoint (Matrix (Fin n) (Fin n) ℝ)) = n * (n + 1) / 2 ∧
  FiniteDimensional.finrank ℝ ↥(selfAdjoint (Matrix (Fin n) (Fin n) ℂ)) = n ^ 2 := by
  sorry



theorem theorem_48402_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
  (T₁ : H₁ →L[𝕜] H₁) (T₂ : H₂ →L[𝕜] H₂) :
  sInf { c : ℝ | 0 ≤ c ∧ ∀ (x : H₁) (y : H₂),
    Real.sqrt (‖T₁ x‖^2 + ‖T₂ y‖^2) ≤ c * Real.sqrt (‖x‖^2 + ‖y‖^2) } =
  max ‖T₁‖ ‖T₂‖ := by
  sorry

theorem theorem_48699_problem
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
  (f : E → ℝ) (hf_diff : Differentiable ℝ f)
  (x : E) (hx : x ∈ C)
  (h_local_min : IsLocalMinOn f C x) :
  let T_C := tangentConeAt ℝ C x
  let T_C_polar := {L : E →L[ℝ] ℝ | ∀ d ∈ T_C, 0 ≤ L d}
  fderiv ℝ f x ∈ T_C_polar := by
  sorry





theorem theorem_49397_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (W : Submodule ℝ V)
  (P : V →ₗ[ℝ] V)
  (h1 : ∀ w ∈ W, P w = w)
  (h2 : ∀ v ∈ Wᗮ, P v = 0)
  (h3 : P ≠ (Submodule.subtype W).comp (orthogonalProjection W).toLinearMap) :
  ∃ v : V, ‖v‖ < ‖P v‖ := by
  sorry



theorem theorem_48248_problem
  (A_bar : (Fin 3 → ℝ) → (Fin 3 → ℝ))
  (gamma : ℝ → (Fin 3 → ℝ))
  (p : ℝ)
  (h_smooth_A : ContDiff ℝ ⊤ A_bar)
  (h_smooth_gamma : ContDiff ℝ ⊤ gamma) :
  deriv (A_bar ∘ gamma) p = (fderiv ℝ A_bar (gamma p)) (deriv gamma p) := by
  sorry

theorem theorem_49669_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ) (p v : E) (t₀ : ℝ)
  (h : DifferentiableAt ℝ f p) :
  deriv (fun t => f (p + (t - t₀) • v)) t₀ = inner (gradient f p) v := by
  sorry







theorem theorem_49617_problem
  {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  (v w : I → V) (i j : I)
  (h1 : ∀ l, w l = v l - v j)
  (h2 : ∀ l, v l = w l - w i) :
  Submodule.span K (Set.range v) = Submodule.span K (Set.range w) := by
  sorry











theorem theorem_49647_problem
  (n : ℕ)
  (K : Type*) [Field K]
  (A B C D : Matrix (Fin n) (Fin n) K)
  (h_singular_B : ¬ IsUnit B)
  (h_C : C = A * B * D) :
  ¬ IsUnit C := by
  sorry

























theorem theorem_50676_problem {E : Type*} [NormedAddCommGroup E] (T T_n : E) :
  |‖T‖ - ‖T_n‖| ≤ ‖T - T_n‖ := by
  sorry



theorem theorem_50246_problem
  (X : Type*) [AddCommGroup X] [Module ℂ X]
  (Y Z : Submodule ℂ X) (h : Y ≤ Z) :
  Nonempty ((X ⧸ Y) ≃ₗ[ℂ] (X ⧸ Z) × (Z ⧸ (Y.comap Z.subtype))) := by
  sorry





theorem theorem_50845_problem
  {n : ℕ} {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  (a : ι → Fin n → ℂ)
  (h_bound : ∃ s : Set (Fin n → ℂ), Bornology.IsBounded s ∧ Filter.Eventually (fun i => a i ∈ s) Filter.atTop) :
  ∃ x : Fin n → ℂ, MapClusterPt x Filter.atTop a := by
  sorry

theorem theorem_50863_problem (x y : ℕ → ℝ)
  (hx : Summable (fun i => (x i) ^ 2))
  (hy : Summable (fun i => (y i) ^ 2)) :
  Real.sqrt (∑' i, (x i + y i) ^ 2) ≤ Real.sqrt (∑' i, (x i) ^ 2) + Real.sqrt (∑' i, (y i) ^ 2) := by
  sorry



theorem theorem_51632_problem
  {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]
  (x : ℕ → X)
  (h : Summable (fun n => ‖x n‖)) :
  Summable x := by
  sorry



theorem theorem_51793_problem
  (n : ℕ)
  (V D : Matrix (Fin n) (Fin n) ℝ)
  (beta : ℝ)
  (hV : V * V.transpose = 1)
  (hD_diag : D.IsDiag)
  (hD_nonneg : ∀ i, 0 ≤ D i i)
  (hbeta : 0 < beta)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : A = V * D * V.transpose + beta • (1 : Matrix (Fin n) (Fin n) ℝ)) :
  A⁻¹ = V * (D + beta • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ * V.transpose := by
  sorry



theorem theorem_50522_problem
  (n : ℕ)
  (a b : EuclideanSpace ℝ (Fin n))
  (μ : ℝ)
  (hμ : 0 ≤ μ ∧ μ ≤ 1)
  (c : EuclideanSpace ℝ (Fin n))
  (hc : c = (1 - μ) • a + μ • b) :
  ‖c‖^2 = (1 - μ)^2 * ‖a‖^2 + μ^2 * ‖b‖^2 + 2 * μ * (1 - μ) * inner a b := by
  sorry

theorem theorem_51106_problem (n p m : ℕ)
  (A : Matrix (Fin n) (Fin p) ℝ)
  (B : Matrix (Fin p) (Fin m) ℝ)
  (hA : Matrix.rank A = min n p)
  (hB : Matrix.rank B = min p m) :
  Matrix.rank (A * B) ≤ min n (min p m) := by
  sorry





theorem theorem_52022_problem (S : Matrix (Fin 3) (Fin 3) ℝ)
  (Q : Matrix (Fin 3) (Fin 3) ℝ)
  (hQ : Q = S - (Matrix.trace S) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) :
  Matrix.trace Q = -2 * Matrix.trace S := by
  sorry







theorem theorem_51444_problem
  {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  (T : E →ₗ[𝕜] F)
  (h_cont : @Continuous E F (TopologicalSpace.induced (fun x (f : E →L[𝕜] 𝕜) ↦ f x) inferInstance) _ T) :
  FiniteDimensional 𝕜 (LinearMap.range T) := by
  sorry













theorem theorem_50876_problem (a b c d : ℝ)
  (A B : Matrix (Fin 4) (Fin 4) ℝ)
  (hA : A = !![1, a, b, c + d;
               1, b, c, d + a;
               1, c, d, a + b;
               1, d, a, b + c])
  (hB : B = !![0, a, b, 1;
               0, b, c, 1;
               0, c, d, 1;
               0, d, a, 1]) :
  A.det = (a + b + c + d) * B.det := by
  sorry



theorem theorem_50994_problem (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
  (x : V) (hx : x ≠ 0) :
  ∃ f : V →ₗ[K] K, f x = 1 := by
  sorry





theorem theorem_51693_problem {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
  (h : ((A - A.conjTranspose).conjTranspose * (A - A.conjTranspose)).trace = 0) :
  A = A.conjTranspose := by
  sorry



theorem theorem_52446_problem (n : ℕ) :
  let V := Fin n → ℝ
  let e := Pi.basisFun ℝ (Fin n)
  let ι := ExteriorAlgebra.ι ℝ
  let pairs := {p : Fin n × Fin n // p.1 < p.2}
  let basis_elems := fun (p : pairs) ↦ ι (e p.1.1) * ι (e p.1.2)
  let TwoForms := Submodule.span ℝ (Set.range (fun (uv : V × V) ↦ ι uv.1 * ι uv.2))
  LinearIndependent ℝ basis_elems ∧
  Submodule.span ℝ (Set.range basis_elems) = TwoForms := by
  sorry

theorem theorem_51134_problem
  (K : Type*) [Field K]
  (V W : Type*) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [FiniteDimensional K V] [FiniteDimensional K W]
  (T : V →ₗ[K] W) :
  ∃! Tt : (Module.Dual K W) →ₗ[K] (Module.Dual K V),
    ∀ (g : Module.Dual K W) (v : V), Tt g v = g (T v) := by
  sorry

theorem theorem_50967_problem (a b c : ℝ) (z : ℂ) (α : ℂ) (β : ℝ)
  (hα : α = ((a : ℂ) - (b : ℂ) * Complex.I) / 2)
  (hβ : β = -c) :
  a * z.re + b * z.im = c ↔ α * z + star α * star z + (β : ℂ) = 0 := by
  sorry

theorem theorem_51378_problem (T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
  (h1 : T ![1, 0] = ![0, 1])
  (h2 : T ![0, 1] = ![0, 0]) :
  ¬ ∃ (b : Basis (Fin 2) ℝ (Fin 2 → ℝ)), (LinearMap.toMatrix b b T).IsSymm := by
  sorry



