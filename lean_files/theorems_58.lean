import Mathlib
import Mathlib.Tactic

theorem theorem_310605_problem (n : ℕ) (u : (Fin n → ℝ) → (Fin n → ℝ))
  (h_diff : ContDiff ℝ 2 u)
  (h_supp : HasCompactSupport u) :
  ∫ x, (LinearMap.trace ℝ (Fin n → ℝ) (fderiv ℝ u x).toLinearMap) ^ 2 ≤
  ∫ x, ∑ i : Fin n, ∑ j : Fin n, ((fderiv ℝ u x) (Pi.single j 1) i) ^ 2 := by
  sorry

theorem theorem_310560_problem 
  {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [CommRing R]
  (As Aa : Matrix n n R) :
  let I : Matrix n n R := 1
  let contract (X Y : Matrix n n R) : R := ∑ i, ∑ j, X i j * Y i j
  (contract As As) • ((contract I As) • Aa) = 
  ((∑ i, ∑ j, As i j * As i j) * (∑ i, ∑ j, I i j * As i j)) • Aa := by
  sorry







theorem theorem_310379_problem
  (K V G : Type*)
  [Field K]
  [AddCommGroup V]
  [Module K V]
  [Group G]
  [Fintype G]
  [DistribMulAction G V]
  [SMulCommClass G K V]
  (h_char : (Fintype.card G : K) ≠ 0)
  (q : V → V)
  (hq : ∀ v : V, q v = (Fintype.card G : K)⁻¹ • ∑ g : G, g • v) :
  ∀ v : V, q (q v) = q v := by
  sorry













theorem theorem_311018_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (U : Set E) (hU : IsOpen U)
  (f : E → ℝ) (x₀ : E) (hx₀ : x₀ ∈ U)
  (h_diff_U : DifferentiableOn ℝ f U)
  (h_diff_twice_x₀ : DifferentiableAt ℝ (fderiv ℝ f) x₀) :
  ∀ (u v : E), fderiv ℝ (fderiv ℝ f) x₀ u v = fderiv ℝ (fderiv ℝ f) x₀ v u := by
  sorry

theorem theorem_311060_problem
  {K : Type*} [Field K]
  {m1 n1 m2 n2 : ℕ}
  (B : Matrix (Fin m1) (Fin n1) K)
  (C : Matrix (Fin m2) (Fin n2) K)
  (A : Matrix (Fin m1 × Fin m2) (Fin n1 × Fin n2) K)
  (hA : ∀ (i1 : Fin m1) (i2 : Fin m2) (j1 : Fin n1) (j2 : Fin n2),
    A (i1, i2) (j1, j2) = B i1 j1 * C i2 j2)
  (i2 : Fin m2) (j2 : Fin n2)
  (hC : C i2 j2 ≠ 0) :
  ∀ (i1 : Fin m1) (j1 : Fin n1),
    B i1 j1 = A (i1, i2) (j1, j2) / C i2 j2 := by
  sorry







theorem theorem_311835_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
  ∃ U : Matrix (Fin n) (Fin n) ℂ,
    U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
    let T := U * A * U.conjTranspose
    (∀ i j : Fin n, i > j → T i j = 0) ∧
    (∀ i j : Fin n, j.val = i.val + 1 → (T i j).im = 0 ∧ 0 ≤ (T i j).re) := by
  sorry

theorem theorem_311528_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (x : V) (hx : x ≠ 0) (w : V) :
  ExteriorAlgebra.ι F x * ExteriorAlgebra.ι F w = 0 ↔ ∃ c : F, w = c • x := by
  sorry

theorem theorem_311636_problem (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ)
  (hC : C.PosSemidef) :
  (Matrix.fromBlocks C C C C).PosSemidef := by
  sorry



theorem theorem_311699_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (A : V →ₗ[F] V)
  (f : V → V)
  (h : ∀ x, f x = A x)
  {α : Type*}
  (Alg : (V → V) → α) :
  Alg f = Alg A := by
  sorry

theorem theorem_312419_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (A : H →L[𝕜] H)
  (U : H ≃ₗᵢ[𝕜] H) :
  ‖star (U : H →L[𝕜] H) * A * (U : H →L[𝕜] H)‖ = ‖A‖ := by
  sorry

theorem theorem_311591_problem (T : C(Set.Icc (0 : ℝ) 1, ℝ) →L[ℝ] ℝ)
  (h : ∀ g, ‖T g‖ ≤ ‖g ⟨0, by norm_num⟩‖ + 7 * ‖g ⟨(1/2 : ℝ), by norm_num⟩‖) :
  ‖T‖ = 8 := by
  sorry

theorem theorem_312091_problem
  (m n : ℕ)
  (R : Type*) [CommRing R]
  (A : Matrix (Fin m) (Fin n) R)
  (B : Matrix (Fin n) (Fin m) R) :
  Matrix.det (1 + A * B) = Matrix.det (1 + B * A) := by
  sorry

theorem theorem_311667_problem :
  ∃ (n : ℕ) (F : Type) (_ : Field F) (A₁ A₂ A₃ : Matrix (Fin n) (Fin n) F),
    LinearIndependent F ![A₁, A₂, A₃] ∧
    IsUnit A₁ ∧ IsUnit A₂ ∧ IsUnit A₃ ∧
    ¬ LinearIndependent F ![A₁⁻¹, A₂⁻¹, A₃⁻¹] := by
  sorry





theorem theorem_312630_problem
  (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (T : X →ₗ[ℝ] Y)
  (h : T '' {x : X | ‖x‖ = 1} = {y : Y | ‖y‖ = 1}) :
  Continuous T := by
  sorry



theorem theorem_313103_problem
  (K F W : Type*)
  [Field K] [Field F] [Algebra F K]
  [AddCommGroup W]
  [Module K W]
  [Module F W] [IsScalarTower F K W] :
  Module.rank K W ≤ Module.rank F W := by
  sorry

theorem theorem_313084_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (ϕ : V →ₗ[F] V) (h_nil : IsNilpotent ϕ) :
  ∃ (n : ℕ) (b : Basis (Fin n) F V),
    ∀ i j : Fin n, j ≤ i → LinearMap.toMatrix b b ϕ i j = 0 := by
  sorry

theorem theorem_312745_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (x₁ x₂ y₁ y₂ : V)
  (hx₁ : ‖x₁‖ = 1) (hx₂ : ‖x₂‖ = 1)
  (hy₁ : ‖y₁‖ = 1) (hy₂ : ‖y₂‖ = 1)
  (h : ‖x₁ - x₂‖ = ‖y₁ - y₂‖) :
  ∃ T : V ≃ₗᵢ[ℝ] V, T x₁ = y₁ ∧ T x₂ = y₂ := by
  sorry

theorem theorem_312073_problem (n : ℕ) (A B S : Matrix (Fin n) (Fin n) ℂ)
  (hS : Invertible S) (h : B = S⁻¹ * A * S) (p : Polynomial ℂ) :
  Polynomial.aeval A p = S * Polynomial.aeval B p * S⁻¹ := by
  sorry



theorem theorem_313162_problem (V : Type*) [AddCommGroup V] [Module ℝ V]
  (one : V) (h_one_ne_zero : one ≠ 0) :
  IsLeast {W : Submodule ℝ V | ∃ (Λ : W →ₗ[ℝ] ℝ) (h : one ∈ W), Λ ⟨one, h⟩ = 1}
    (Submodule.span ℝ {one}) := by
  sorry

theorem theorem_313173_problem {n : ℕ} {F : Type*} [Field F] [CharZero F]
  (A B : Matrix (Fin n) (Fin n) F) :
  Matrix.trace (A * B) = Matrix.trace (B * A) := by
  sorry















theorem theorem_313568_problem (n : ℕ) (F : Type*) [Field F] [NeZero n]
  [Module (Matrix (Fin n) (Fin n) F) (Fin n → F)]
  (h_action : ∀ (B : Matrix (Fin n) (Fin n) F) (v : Fin n → F), B • v = Matrix.mulVec B v) :
  Nonempty ((Module.End (Matrix (Fin n) (Fin n) F) (Fin n → F)) ≃+* F) := by
  sorry

theorem theorem_313422_problem (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (x : Matrix (Fin n) (Fin 1) ℝ)
  (hA : A.transpose * A = 1)
  (hx : x ≠ 0) :
  x.transpose * x = (A * x).transpose * (A * x) := by
  sorry

theorem theorem_313802_problem (n : ℕ) (x v : Matrix (Fin n) (Fin 1) ℝ) :
  x * x.transpose * v = v * (x.transpose * x) ↔ ¬ LinearIndependent ℝ ![x, v] := by
  sorry

theorem theorem_313475_problem (x y u v : ℝ) 
  (h1 : u = x + y) 
  (h2 : v = x - y) : 
  x^2 + y^2 - x * y = (1/4) * u^2 + (3/4) * v^2 := by
  sorry







theorem theorem_313520_problem (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] :
  Nonempty (TensorPower F 1 V ≃ₗ[F] V) := by
  sorry

theorem theorem_313650_problem (n : ℕ) (x : Fin n → ℝ) (hn : n ≠ 0) :
  Filter.Tendsto (fun p : ℝ => (∑ i, |x i| ^ p) ^ (1 / p)) Filter.atTop (nhds (⨆ i, |x i|)) := by
  sorry



theorem theorem_313474_problem
  (x y z : Fin 6 → ℝ)
  (h_distinct : Function.Injective (fun i ↦ (x i, y i)))
  (h_det : (Matrix.of (fun i ↦ ![(x i)^2, (x i) * (y i), (y i)^2, x i, y i, 1])).det ≠ 0) :
  ∃! (coeffs : Fin 6 → ℝ), ∀ i,
    (coeffs 0) * (x i)^2 + (coeffs 1) * (x i) * (y i) + (coeffs 2) * (y i)^2 +
    (coeffs 3) * (x i) + (coeffs 4) * (y i) + (coeffs 5) = z i := by
  sorry





theorem theorem_313879_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  (k : ℕ)
  (α : V)
  (C : (Fin k → K) → (Fin k → V))
  (hC : ∀ x : Fin k → K, C x = fun i => x i • α)
  (f : (Fin k → V) → W) :
  ∃ g : (Fin k → K) → W, g = f ∘ C := by
  sorry

theorem theorem_314312_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι]
  (x : ι → E)
  (w : ι → ι → ℝ)
  (i : ι) :
  ‖∑ j, w i j • (x i - x j)‖^2 =
  ∑ j, ∑ k, w i j * w i k * inner (x i - x j) (x i - x k) := by
  sorry

theorem theorem_314008_problem
  (T : (ℕ → ℝ) → (ℕ → ℝ))
  (hT : ∀ x : ℕ → ℝ, T x = fun n ↦ if n = 0 then 0 else x (n - 1)) :
  ¬ ∃ μ : ℝ, ∃ x : ℕ → ℝ, x ≠ 0 ∧ T x = μ • x := by
  sorry



theorem theorem_314236_problem
  (m K : ℕ)
  (T : Fin K → ℕ)
  (x : Fin m → ℝ)
  (q : (k : Fin K) → (Fin m → ℝ) → Fin (T k))
  (w : (k : Fin K) → Fin (T k) → ℝ)
  (f : (k : Fin K) → (Fin m → ℝ) → ℝ)
  (h1 : ∀ k, ∀ v, f k v = w k (q k v))
  (F : (Fin m → ℝ) → ℝ)
  (h2 : ∀ v, F v = ∑ k : Fin K, w k (q k v)) :
  F x = ∑ k : Fin K, f k x := by
  sorry



theorem theorem_314469_problem (a b : ℝ) (h_le : a ≤ b) (F : ℝ → ℝ)
  (h_mono : MonotoneOn F (Set.Icc a b))
  (h_dense : Set.Icc (F a) (F b) ⊆ closure (F '' (Set.Icc a b))) :
  ContinuousOn F (Set.Icc a b) := by
  sorry

theorem theorem_314427_problem
  {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [DistribMulAction G V]
  [AddCommGroup W] [Module k W] [DistribMulAction G W]
  (ρ : V →ₗ[k] W) :
  (∀ (g : G) (x : V), ρ (g • x) = g • ρ x) ↔
  (∀ (g : G), (fun x ↦ g • ρ (g⁻¹ • x)) = ρ) := by
  sorry

theorem theorem_314587_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (n : ℕ) (h_dim : FiniteDimensional.finrank F V = n)
  (V_seq : ℕ → Subspace F V)
  (h_nested : ∀ i, V_seq (i + 1) ≤ V_seq i) :
  ∃ k ≤ n, ∀ i > k, FiniteDimensional.finrank F (V_seq i) = FiniteDimensional.finrank F (V_seq (k + 1)) := by
  sorry

theorem theorem_314048_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (X : V →ₗ[ℝ] V)
  (ε : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (hε : ∀ u v : V, ε u v = - inner v u) :
  ∀ u v : V, ε (X u) (X v) = - ε u (LinearMap.adjoint X (X v)) := by
  sorry





theorem theorem_314681_problem (n m : ℕ) (P : Fin n → Matrix (Fin m) (Fin m) ℝ)
  (h_symm : ∀ i, (P i).IsSymm)
  (h_idem : ∀ i, P i * P i = P i)
  (h_rel : ∀ i j, i ≠ j → P i * P j + P j * P i = 2 • (P i * P j)) :
  (∑ i, P i) ^ 2 = (∑ i, P i) + 2 • ∑ i, ∑ j in Finset.filter (fun x => i < x) Finset.univ, P i * P j := by
  sorry

















theorem theorem_315067_problem
  (n : ℕ)
  (Y : (Fin n → ℝ) → (Fin n → ℝ))
  (c : ℝ → (Fin n → ℝ))
  (p : Fin n → ℝ)
  (X : Fin n → ℝ)
  (hY : ContDiff ℝ ⊤ Y)
  (hc : ContDiff ℝ ⊤ c)
  (h_c0 : c 0 = p)
  (h_cd0 : deriv c 0 = X) :
  deriv (Y ∘ c) 0 = fun j => ∑ i : Fin n, (fderiv ℝ Y p (Pi.single i 1) j) * (X i) := by
  sorry





theorem theorem_315626_problem (A : Matrix (Fin 2) (Fin 2) ℂ)
  (hA : A = !![0, 1; 0, 0]) :
  ¬ ∃ B : Matrix (Fin 2) (Fin 2) ℂ, B ^ 2 = A := by
  sorry

theorem theorem_315317_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (r : ℕ) (hr : r ≥ 1)
  (μ : V →ₗ[K] K)
  (l : Fin r → (V →ₗ[K] K))
  (h : (⨅ i, LinearMap.ker (l i)) ≤ LinearMap.ker μ) :
  ∃ c : Fin r → K, μ = ∑ i, c i • l i := by
  sorry









theorem theorem_315976_problem
  (n : ℕ)
  (A B P : Matrix (Fin n) (Fin n) ℂ)
  (hP : Invertible P)
  (hB : ∀ i j, i ≠ j → B i j = 0)
  (hA : A = P * B * P⁻¹)
  (k : ℕ)
  (hk : k > 0) :
  A ^ k = P * (B ^ k) * P⁻¹ := by
  sorry



theorem theorem_316114_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : ℝ → H →L[ℂ] H) (t : ℝ)
  (h_smooth : Differentiable ℝ U)
  (h_unitary : ∀ t, U t * Star.star (U t) = 1) :
  (deriv U t) * Star.star (U t) + Star.star ((deriv U t) * Star.star (U t)) = 0 := by
  sorry



theorem theorem_315336_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (r p1 : ℕ)
  (Hr1 Hr2 : Submodule K V)
  (h_sub : Hr2 ≤ Hr1)
  (B : V →ₗ[K] V)
  (f : Fin p1 → V)
  (h_indep : ∀ (α : Fin p1 → K), (∑ i, α i • f i) ∈ Hr1 → ∀ i, α i = 0)
  (α : Fin p1 → K)
  (x : V)
  (hx : x = ∑ i, α i • f i)
  (h_nontriv : ∃ i, α i ≠ 0)
  (hB : (B ^ (r - 1)) x = 0) :
  x ∉ Hr1 := by
  sorry

theorem theorem_316158_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [CommRing R]
  (A B : Matrix n n R)
  (h1 : IsUnit (1 + A * B))
  (h2 : IsUnit (1 + B * A)) :
  (1 + A * B)⁻¹ = 1 - A * (1 + B * A)⁻¹ * B := by
  sorry





theorem theorem_316263_problem (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
  (h_symm : K.IsSymm) (h_pos : K.PosDef) :
  ∃! L : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j : Fin n, i < j → L i j = 0) ∧
    (∀ i : Fin n, 0 < L i i) ∧
    K = L * L.transpose := by
  sorry

theorem theorem_316765_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  (T : X →L[𝕜] Y)
  (h_inj : Function.Injective T)
  (h_closed : IsClosed (LinearMap.range T : Set Y)) :
  Continuous (LinearEquiv.ofInjective T.toLinearMap h_inj).symm := by
  sorry



theorem theorem_316399_problem
  {X Y : Type*}
  (f : X → Y → ℝ)
  (xn : ℕ → X) (ym : ℕ → Y)
  (x : X) (y : Y)
  (h1 : ∀ ε > 0, ∃ N, ∀ n > N, ∀ m, |f (xn n) (ym m) - f x (ym m)| < ε)
  (h2 : Filter.Tendsto (fun m ↦ f x (ym m)) Filter.atTop (nhds (f x y))) :
  Filter.Tendsto (fun p : ℕ × ℕ ↦ f (xn p.1) (ym p.2)) Filter.atTop (nhds (f x y)) := by
  sorry

theorem theorem_316543_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (U : Set E) (f : E → ℝ)
  (hU_cmp : IsCompact U)
  (hU_cvx : Convex ℝ U)
  (hU_ne : U.Nonempty)
  (hf_cvx : ConvexOn ℝ U f)
  (hf_cont : ContinuousOn f U) :
  ∃ b ∈ frontier U, ∀ x ∈ U, f x ≤ f b := by
  sorry

