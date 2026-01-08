import Mathlib
import Mathlib.Tactic

theorem theorem_289631_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (S U D : Matrix n n ℝ)
  (hS_pd : S.PosDef)
  (hU_ortho : U ∈ Matrix.orthogonalGroup n ℝ)
  (hD_diag : ∀ i j, i ≠ j → D i j = 0)
  (h_decomp : S = U.transpose * D * U)
  [Invertible S] [Invertible D] :
  S⁻¹ = U.transpose * D⁻¹ * U := by
  sorry

theorem theorem_289578_problem (n p : ℕ)
  (X U : Matrix (Fin n) (Fin p) ℝ)
  (h_rank : X.rank = p)
  (h_orthonormal : U.transpose * U = 1)
  (h_ortho : U.transpose * X = 0) :
  2 * p ≤ n := by
  sorry



theorem theorem_289664_problem
  (pts : Fin 11 → ℝ × ℝ)
  (h_distinct : Function.Injective pts)
  (h_consistent : ∃ f : Polynomial ℝ, f.degree ≤ 42 ∧ ∀ i, f.eval (pts i).1 = (pts i).2) :
  {f : Polynomial ℝ | f.degree ≤ 42 ∧ ∀ i, f.eval (pts i).1 = (pts i).2}.Infinite := by
  sorry







theorem theorem_289863_problem (F : Type*) [Field F] (n : ℕ) (A : Matrix (Fin n) (Fin n) F) :
  Polynomial.aeval A (Matrix.charpoly A) = 0 := by
  sorry









theorem theorem_289967_problem
  {n : ℕ} {α : Type*}
  (X : Fin n → α → ℝ)
  (h_dep : ∃ c : Fin n → ℝ, c ≠ 0 ∧ ∀ (a : α), ∑ i : Fin n, c i * X i a = 0) :
  ∃ (β β' : Fin n → ℝ), β ≠ β' ∧
    ∀ (β₀ : ℝ) (a : α), β₀ + ∑ i : Fin n, β i * X i a = β₀ + ∑ i : Fin n, β' i * X i a := by
  sorry





theorem theorem_290573_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (T : X →ₗ[ℝ] ℝ)
  (x : ℕ → X)
  (hx : ∃ K, ∀ n, ‖x n‖ ≤ K)
  (hTx : ¬ ∃ M, ∀ n, ‖T (x n)‖ ≤ M) :
  ¬ IsBoundedLinearMap ℝ T := by
  sorry









theorem theorem_290306_problem
  {Z : Type*} [AddCommGroup Z] [Module ℝ Z] [FiniteDimensional ℝ Z]
  (n_U n_V : ℕ)
  (u : Fin n_U → Z) (v : Fin n_V → Z)
  -- Bases imply linear independence and span
  (hu : LinearIndependent ℝ u)
  (hv : LinearIndependent ℝ v)
  (U V : Submodule ℝ Z)
  (hU : U = Submodule.span ℝ (Set.range u))
  (hV : V = Submodule.span ℝ (Set.range v))
  -- Linear maps A and B
  (A : (Fin n_U → ℝ) →ₗ[ℝ] Z)
  (hA : ∀ x, A x = ∑ i, x i • u i)
  (B : (Fin n_V → ℝ) →ₗ[ℝ] Z)
  (hB : ∀ y, B y = ∑ i, y i • v i)
  -- Linear map Gamma
  (Gamma : ((Fin n_U → ℝ) × (Fin n_V → ℝ)) →ₗ[ℝ] Z)
  (hGamma : ∀ x y, Gamma (x, y) = A x - B y)
  -- Kernel N
  (N : Submodule ℝ ((Fin n_U → ℝ) × (Fin n_V → ℝ)))
  (hN : N = LinearMap.ker Gamma)
  -- Projection Pi_x
  (Pi_x : ((Fin n_U → ℝ) × (Fin n_V → ℝ)) →ₗ[ℝ] (Fin n_U → ℝ))
  (hPi_x : ∀ x y, Pi_x (x, y) = x)
  -- Basis for N
  (n_N : ℕ)
  (nu : Basis (Fin n_N) ℝ N) :
  U ⊓ V = Submodule.span ℝ (Set.range (fun i ↦ A (Pi_x (nu i)))) := by
  sorry





theorem theorem_290305_problem
  (n : ℕ)
  (x₀ y : EuclideanSpace ℝ (Fin n))
  (hx₀ : x₀ ≠ 0)
  (h : ‖y‖ ≥ ‖x₀‖ + ‖x₀ - y‖) :
  ∃ k : ℝ, k ≥ 1 ∧ y = k • x₀ := by
  sorry













theorem theorem_291534_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
  (inferInstance : TopologicalSpace (WeakDual 𝕜 X)) = (inferInstance : TopologicalSpace (NormedSpace.Dual 𝕜 X)) ↔
  FiniteDimensional 𝕜 X := by
  sorry

theorem theorem_291301_problem (α β k : ℝ) (v w : ℝ × ℝ × ℝ)
  (hα : Real.cos α ≠ 1)
  (hβ : Real.cos β ≠ 1)
  (hk : k = -1)
  (hv : v = (k, k * Real.sin α / (Real.cos α - 1), k * Real.sin β / (Real.cos β - 1)))
  (hw : w = (-Real.sin (α / 2) * Real.sin (β / 2),
             Real.cos (α / 2) * Real.sin (β / 2),
             Real.cos (β / 2) * Real.sin (α / 2))) :
  ∃ c : ℝ, c ≠ 0 ∧ w = c • v := by
  sorry



theorem theorem_291475_problem
  (f : ℂ → ℂ)
  (g : ℂ → ℂ)
  (hf : DifferentiableOn ℂ f {z | 0 < Complex.abs z ∧ Complex.abs z < 1})
  (hg : ∀ z, 1 < Complex.abs z → g z = f (1 / z)) :
  DifferentiableOn ℂ g {z | 1 < Complex.abs z} := by
  sorry





theorem theorem_292034_problem
  {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
  (C : Set E) (c₀ : E)
  (hC_open : IsOpen C)
  (hC_convex : Convex ℝ C)
  (hc₀ : c₀ ∈ C)
  (x₀ : E) (hx₀ : x₀ ∉ C) :
  ∃ f : E →L[ℝ] ℝ, ∀ x ∈ C, f x < f x₀ := by
  sorry



theorem theorem_291774_problem
  (n : ℕ)
  (u : EuclideanSpace ℝ (Fin n) → ℝ)
  (hu : ContDiff ℝ ⊤ u) :
  ∀ᵐ x, ‖gradient (fun y ↦ ‖gradient u y‖) x‖^2 ≤
    ∑ i : Fin n, ‖gradient (fun y ↦ (gradient u y) i) x‖^2 := by
  sorry

theorem theorem_291839_problem (f : ℂ → ℂ) (z₀ : ℂ)
  (h : DifferentiableAt ℂ f z₀) :
  LinearMap.det ((fderiv ℝ f z₀).toLinearMap) = Complex.abs (deriv f z₀) ^ 2 := by
  sorry















theorem theorem_291748_problem
  (n m : ℕ)
  (x : Matrix (Fin n) (Fin 1) ℝ)
  (C1 C2 : Matrix (Fin m) (Fin n) ℝ)
  (v1 v2 : Matrix (Fin m) (Fin 1) ℝ)
  (R1 R2 : Matrix (Fin m) (Fin m) ℝ)
  (hR1_pos : R1.PosDef)
  (hR2_pos : R2.PosDef)
  -- Covariance assumptions interpreted algebraically
  (h_cov1 : v1 * v1.transpose = R1)
  (h_cov2 : v2 * v2.transpose = R2)
  (h_indep1 : v1 * v2.transpose = 0)
  (h_indep2 : v2 * v1.transpose = 0)
  -- Measurement equations
  (y1 : Matrix (Fin m) (Fin 1) ℝ)
  (h_y1 : y1 = C1 * x + v1)
  (y2 : Matrix (Fin m) (Fin 1) ℝ)
  (h_y2 : y2 = C2 * x + v2)
  -- Concatenated definitions using Sum types for block structures
  (y : Matrix (Fin m ⊕ Fin m) (Fin 1) ℝ)
  (h_y : y = Sum.elim y1 y2)
  (C : Matrix (Fin m ⊕ Fin m) (Fin n) ℝ)
  (h_C : C = Sum.elim C1 C2)
  (v : Matrix (Fin m ⊕ Fin m) (Fin 1) ℝ)
  (h_v : v = Sum.elim v1 v2)
  (R : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
  (h_R : R = Matrix.fromBlocks R1 0 0 R2) :
  y = C * x + v ∧ v * v.transpose = R := by
  sorry









theorem theorem_292352_problem
  (m : ℕ)
  (x y z_vals : Fin m → ℝ)
  (A : Matrix (Fin m) (Fin 6) ℝ)
  (z : Matrix (Fin m) (Fin 1) ℝ)
  (hA : ∀ i, A i 0 = 1 ∧ A i 1 = x i ∧ A i 2 = y i ∧
             A i 3 = (x i)^2 ∧ A i 4 = x i * y i ∧ A i 5 = (y i)^2)
  (hz : ∀ i, z i 0 = z_vals i)
  (h_rank : A.rank = 6) :
  let a_LS := (A.transpose * A)⁻¹ * (A.transpose * z)
  (∀ a : Matrix (Fin 6) (Fin 1) ℝ,
    ∑ i, ((A * a_LS - z) i 0) ^ 2 ≤ ∑ i, ((A * a - z) i 0) ^ 2) ∧
  (∀ a : Matrix (Fin 6) (Fin 1) ℝ,
    ∑ i, ((A * a - z) i 0) ^ 2 = ∑ i, ((A * a_LS - z) i 0) ^ 2 → a = a_LS) := by
  sorry

theorem theorem_292444_problem {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) :
  |inner a b / (norm a * norm b)| ≤ 1 := by
  sorry





theorem theorem_292542_problem (a : ℝ) (θ : ℝ → ℝ)
  (h_diff : Differentiable ℝ (deriv θ))
  (h_ode : ∀ t, deriv (deriv θ) t = Real.sign (- deriv θ t - a * θ t)) :
  let x : ℝ → (Fin 2 → ℝ) := fun t => ![θ t, deriv θ t]
  ∀ t, deriv x t = ![x t 1, Real.sign (- (x t 1) - a * (x t 0))] := by
  sorry

theorem theorem_292736_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {n m : ℕ}
  (T : V →ₗ[K] W)
  (α : Basis (Fin n) K V)
  (f : Basis (Fin n) K (Module.Dual K V))
  (g : Basis (Fin m) K (Module.Dual K W))
  (h_dual : f = α.dualBasis)
  (j : Fin m) :
  LinearMap.dualMap T (g j) = ∑ i, (LinearMap.dualMap T (g j) (α i)) • (f i) := by
  sorry

theorem theorem_291875_problem
  (P₁ P₂ : Matrix (Fin 2) (Fin 1) ℝ)
  (A B C F G H : ℝ) :
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![A, B; B, C]
  let N : Matrix (Fin 1) (Fin 2) ℝ := !![2 * F, 2 * G]
  ∃ s₁₁ s₂₂ s₁₂ : ℝ, ∀ t : ℝ,
    let u := 1 - t
    let Q := t • P₁ + u • P₂
    let conic_val := (Q.transpose * M * Q) 0 0 + (N * Q) 0 0 + H
    conic_val = t^2 * s₁₁ + u^2 * s₂₂ + 2 * t * u * s₁₂ := by
  sorry

theorem theorem_292779_problem (B : Set ℝ)
  (h_indep : LinearIndependent ℚ (Subtype.val : B → ℝ))
  (h_span : Submodule.span ℚ B = ⊤) :
  ¬ Set.Countable B := by
  sorry







theorem theorem_293505_problem
  {K : Type*} [Field K]
  {V W : Type*}
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {n m : ℕ}
  (B_V : Basis (Fin n) K V)
  (B_W : Basis (Fin m) K W)
  (f : V →ₗ[K] W) :
  ∃! A : Matrix (Fin m) (Fin n) K,
    ∀ v : V, (B_W.repr (f v) : Fin m → K) = Matrix.mulVec A (B_V.repr v : Fin n → K) := by
  sorry

theorem theorem_292636_problem 
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (a b v1 v2 : V)
  (h1 : b = a + v2)
  (h2 : b + (v2 - v1) = a + v1 + (v2 - v1)) :
  v2 - v1 = 0 := by
  sorry





theorem theorem_293010_problem
  {n : ℕ}
  {E : Type*} [AddCommGroup E] [Module ℝ E]
  (U : Set (Fin n → ℝ))
  (V : Set (Fin n → ℝ))
  (hV : V ⊆ U)
  (X : U → E)
  (g : U → ℝ)
  (hg : ∀ x : U, ↑x ∉ V → g x = 0)
  (hX : ∀ x : U, ↑x ∈ V → X x = 0) :
  ∀ x : U, X x = (1 - g x) • X x := by
  sorry







theorem theorem_293112_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
  ∃ θ : ℝ, Real.cos θ = inner x y / (‖x‖ * ‖y‖) := by
  sorry

theorem theorem_292913_problem (a b : EuclideanSpace ℝ (Fin 3)) :
  ‖crossProduct a b‖ ^ 2 + (inner a b) ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  sorry



theorem theorem_292873_problem
  {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace V]
  (T : E → V)
  (F : Set V)
  (h1 : ∀ n : ℕ, T '' (Metric.ball 0 n) ⊆ F)
  (h2 : F = closure (⋃ n : ℕ, T '' (Metric.ball 0 n))) :
  F = ⋃ n : ℕ, closure (T '' (Metric.ball 0 n)) := by
  sorry





theorem theorem_293586_problem
  {F : Type*} [Field F]
  {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  (g₁ : V₁ →ₗ[F] V₁ →ₗ[F] F)
  (g₂ : V₂ →ₗ[F] V₂ →ₗ[F] F)
  (T : V₁ →ₗ[F] V₂)
  (h₁ : Function.Bijective g₁)
  (h₂ : Function.Bijective g₂) :
  let g₁_flat := g₁
  let g₂_flat := g₂
  let g₁_sharp := (LinearEquiv.ofBijective g₁ h₁).symm
  let T_prime := T.dualMap
  let T_star := g₁_sharp.toLinearMap ∘ₗ T_prime ∘ₗ g₂_flat
  ∀ (v₁ : V₁) (v₂ : V₂), g₁ (T_star v₂) v₁ = g₂ v₂ (T v₁) := by
  sorry













theorem theorem_293804_problem (x : ℝ) :
  ∃ (ι : Type) (b : Basis ι ℚ ℝ), ∃! (q : ι →₀ ℚ), Finsupp.total ι ℝ ℚ b q = x := by
  sorry

theorem theorem_293788_problem
  {𝕜 E ι : Type*}
  [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [Finite ι]
  (F : ι → E →L[𝕜] 𝕜)
  (K : Submodule 𝕜 E)
  (hK : K = ⨅ i, LinearMap.ker (F i))
  (U : Set E)
  (weak_top : TopologicalSpace E := TopologicalSpace.induced (fun x i ↦ F i x) Pi.topologicalSpace)
  (hU : @IsOpen E weak_top U)
  (x : E) (hx : x ∈ U) :
  ∀ k ∈ K, x + k ∈ U := by
  sorry



theorem theorem_294437_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
  (h : ∃ X : Matrix (Fin n) (Fin m) ℝ, X * A = 1) :
  Matrix.rank A = n := by
  sorry



theorem theorem_294542_problem
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  (F G : ℝ → A)
  (hF : Differentiable ℝ F)
  (hG : Differentiable ℝ G)
  (hFG : ∀ t, F t * G t = 1)
  (hGF : ∀ t, G t * F t = 1) :
  deriv F = fun t ↦ - F t * deriv G t * F t := by
  sorry

theorem theorem_294735_problem
  (K V G : Type*)
  [Field K] [IsAlgClosed K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Group G]
  (ρ : Representation K G V)
  (h_irred : ∀ (W : Submodule K V), (∀ g : G, W.map (ρ g) ≤ W) → W = ⊥ ∨ W = ⊤)
  (g₁ : G)
  (c : K)
  (h_eig : Module.End.HasEigenvalue (ρ g₁) c) :
  Module.End.eigenspace (ρ g₁) c = ⊤ := by
  sorry



theorem theorem_294274_problem
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (C : Set E) (hC : IsCompact C)
  (ε : ℝ) (hε : 0 < ε)
  (N : Set E) (hN_fin : N.Finite)
  (hN_net : ∀ c ∈ C, ∃ n ∈ N, ‖c - n‖ < ε) :
  ∃ S : Set E, S.Finite ∧ S ⊆ convexHull ℝ N ∧
    ∀ a ∈ convexHull ℝ C, ∃ s ∈ S, ‖a - s‖ < 2 * ε := by
  sorry

theorem theorem_293971_problem (z₁ z₂ z₃ z₄ : ℂ)
  (h₁ : Complex.I * (z₂ - z₁) = z₃ - z₂)
  (h₂ : Complex.I * (z₃ - z₂) = z₄ - z₃) :
  z₁ - z₄ = Complex.I * (z₄ - z₃) ∧ z₂ - z₁ = Complex.I * (z₁ - z₄) := by
  sorry



theorem theorem_294760_problem
  (E : Type*)
  (f : ℕ → E → ℝ)
  (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → ∀ x, |f n x - f m x| < ε) :
  ∃ g : E → ℝ, ∀ ε > 0, ∃ N, ∀ n, N ≤ n → ∀ x, |f n x - g x| < ε := by
  sorry





theorem theorem_294611_problem (a b c d x y : ℤ)
  (h : a * d - b * c = 1 ∨ a * d - b * c = -1) :
  Int.gcd (a * x + b * y) (c * x + d * y) = Int.gcd x y := by
  sorry

theorem theorem_294625_problem (N n : ℕ)
  (u : Fin N → ℝ)
  (x : Fin N → (Fin n → ℝ))
  (v : Fin n → ℝ)
  (beta : ℝ)
  (h_beta : beta = 1 / ∑ k, u k)
  (a : Fin N → (Fin n → ℝ))
  (h_a : ∀ k, a k = Real.sqrt (u k) • (x k - v))
  (P : Matrix (Fin n) (Fin n) ℝ)
  (h_P : P = beta • ∑ k, Matrix.vecMulVec (a k) (a k)) :
  P = P.transpose := by
  sorry

