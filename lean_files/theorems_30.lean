import Mathlib
import Mathlib.Tactic



theorem theorem_158103_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (A B C D : V)
  (PE : Set V) (hPE : PE = {A, B, C, D})
  (Z : Set V) (hZ : Z = convexHull ℝ PE)
  (h_distinct : A ≠ B) :
  ∃ v ∈ Z, v ∉ PE := by
  sorry









theorem theorem_158427_problem 
  {m : Type*} [Fintype m] [DecidableEq m]
  (M : Matrix m m ℚ)
  (d : ℤ)
  (h_d : d ≠ 0)
  (A : Matrix m m ℚ)
  (h_A : A = (d : ℚ) • M)
  (n : ℕ)
  (h_n : n > 0) :
  M ^ n = (1 / ((d : ℚ) ^ n)) • (A ^ n) := by
  sorry



theorem theorem_158271_problem
  {X : Type*}
  (V : Submodule ℂ (X → ℂ))
  (y1 y2 : X → ℂ)
  (hy1 : y1 ∈ V)
  (hy2 : y2 ∈ V)
  -- y1, y2 is a fundamental system of complex solutions
  (h_basis : Basis (Fin 2) ℂ V)
  (h_basis_0 : h_basis 0 = ⟨y1, hy1⟩)
  (h_basis_1 : h_basis 1 = ⟨y2, hy2⟩)
  -- y1/2 and y2/(2i) are real-valued
  (h_real1 : ∀ x, (y1 x / 2).im = 0)
  (h_real2 : ∀ x, (y2 x / (2 * I)).im = 0)
  -- V_real is the space of real-valued solutions
  (V_real : Submodule ℝ (X → ℝ))
  (h_V_real : ∀ f, f ∈ V_real ↔ (fun x ↦ (f x : ℂ)) ∈ V) :
  -- The real parts (which equal the functions themselves) form a fundamental system of real solutions
  ∃ (h1 : (fun x ↦ (y1 x / 2).re) ∈ V_real)
    (h2 : (fun x ↦ (y2 x / (2 * I)).re) ∈ V_real)
    (b : Basis (Fin 2) ℝ V_real),
    b 0 = ⟨fun x ↦ (y1 x / 2).re, h1⟩ ∧
    b 1 = ⟨fun x ↦ (y2 x / (2 * I)).re, h2⟩ := by
  sorry











theorem theorem_158759_problem (x y z a b s t : ℝ)
  (h_range : x ∈ ({0, 1} : Set ℝ) ∧ y ∈ ({0, 1} : Set ℝ) ∧ z ∈ ({0, 1} : Set ℝ) ∧
             a ∈ ({0, 1} : Set ℝ) ∧ b ∈ ({0, 1} : Set ℝ) ∧
             s ∈ ({0, 1} : Set ℝ) ∧ t ∈ ({0, 1} : Set ℝ)) :
  ((x = 1 ∧ y = 1 ∧ z = 1) ∧ ¬(a = 1 ∧ b = 1) ∧ ¬(s = 1 ∧ t = 1) ∨
   ¬(x = 1 ∧ y = 1 ∧ z = 1) ∧ (a = 1 ∧ b = 1) ∧ ¬(s = 1 ∧ t = 1) ∨
   ¬(x = 1 ∧ y = 1 ∧ z = 1) ∧ ¬(a = 1 ∧ b = 1) ∧ (s = 1 ∧ t = 1)) ↔
  ∃ u v w : ℝ,
    (1 - a + 1 - b + 1 - s + 1 - t ≥ 1) ∧
    (1 - a + 1 - b + 1 - x + 1 - y + 1 - z ≥ 1) ∧
    (a + s + x ≥ 1) ∧
    (a + s + y ≥ 1) ∧
    (a + s + z ≥ 1) ∧
    (a + t + x ≥ 1) ∧
    (a + t + y ≥ 1) ∧
    (a + t + z ≥ 1) ∧
    (b + s + x ≥ 1) ∧
    (b + s + y ≥ 1) ∧
    (b + s + z ≥ 1) ∧
    (b + t + x ≥ 1) ∧
    (b + t + y ≥ 1) ∧
    (b + t + z ≥ 1) ∧
    (1 - s + 1 - t + 1 - x + 1 - y + 1 - z ≥ 1) ∧
    (u + v + w = 1) ∧
    (u ≤ x) ∧ (u ≤ y) ∧ (u ≤ z) ∧
    (u ≥ x + y + z - 2) ∧
    (v ≤ a) ∧ (v ≤ b) ∧
    (v ≥ a + b - 1) ∧
    (w ≤ s) ∧ (w ≤ t) ∧
    (w ≥ s + t - 1) ∧
    (u ≥ 0) ∧ (v ≥ 0) ∧ (w ≥ 0) := by
  sorry





theorem theorem_158795_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (n : ℕ)
  (x : Fin n → V)
  (y : Fin n → ℝ)
  (h_y_vals : ∀ i, y i = 1 ∨ y i = -1)
  (w_star : V)
  (γ : ℝ)
  (h_gamma_pos : 0 < γ)
  (h_sep : ∀ i, γ ≤ y i * inner w_star (x i))
  (h_norm_w_star : ‖w_star‖ = 1)
  (R : ℝ)
  (h_R : ∀ i, ‖x i‖ ≤ R)
  (num_updates : ℕ)
  (update_indices : Fin num_updates → Fin n)
  (w : ℕ → V)
  (h_w0 : w 0 = 0)
  (h_update_step : ∀ k : Fin num_updates, w (k + 1) = w k + (y (update_indices k)) • (x (update_indices k)))
  (h_misclassified : ∀ k : Fin num_updates, y (update_indices k) * inner (w k) (x (update_indices k)) ≤ 0) :
  (num_updates : ℝ) ≤ R^2 / γ^2 := by
  sorry











theorem theorem_159276_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (K₁ K₂ : Set V)
  (hK₁_cp : IsCompact K₁) (hK₁_cv : Convex ℝ K₁) (hK₁_ne : K₁.Nonempty)
  (hK₂_cp : IsCompact K₂) (hK₂_cv : Convex ℝ K₂) (hK₂_ne : K₂.Nonempty)
  (h_disj : K₁ ∩ K₂ = ∅) :
  ∃ ξ : V →L[ℝ] ℝ, ξ ≠ 0 ∧ sSup (ξ '' K₁) < sInf (ξ '' K₂) := by
  sorry

theorem theorem_159477_problem
  (K : Set ℝ)
  (f : ℕ → ℝ → ℝ)
  (g : ℝ → ℝ)
  (hK_comp : IsCompact K)
  (hK_reg : K = closure (interior K))
  (hf_cont : ∀ n, ContinuousOn (f n) K)
  (hg_cont : ContinuousOn g K)
  (h_conv_int : TendstoUniformlyOn f g atTop (interior K)) :
  TendstoUniformlyOn f g atTop K := by
  sorry

theorem theorem_159772_problem (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
  CompactSpace (E →L[ℝ] E) ↔ Subsingleton E := by
  sorry



theorem theorem_159866_problem (n : ℕ) (X1 : Fin n → ℝ)
  -- Condition: X1 is standardized such that 1/n * sum = 0
  (h_mean : (1 / (n : ℝ)) * ∑ i, X1 i = 0)
  -- Definition: The Design Matrix X implied by the model Y ~ N(β₀ + β₁X₁, τ²)
  (X : Matrix (Fin n) (Fin 2) ℝ)
  (hX_col0 : ∀ i, X i 0 = 1)       -- Intercept column
  (hX_col1 : ∀ i, X i 1 = X1 i)   -- Predictor column
  -- The information matrix XᵀX
  (M : Matrix (Fin 2) (Fin 2) ℝ)
  (hM : M = X.transpose * X)
  -- Assumption that the covariance matrix exists (model is valid)
  [Invertible M] :
  -- Conclusion: β₀ and β₁ are uncorrelated implies the off-diagonal of the inverse is 0
  (⅟M) 0 1 = 0 := by
  sorry

theorem theorem_159965_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (f : X →L[ℝ] ℝ)
  (x : ℕ → X)
  (L : ℝ)
  (h_norm : ∀ n, ‖x n‖ = 1)
  (h_lim : Filter.Tendsto (fun n ↦ f (x n)) Filter.atTop (nhds L)) :
  ‖f‖ ≥ L := by
  sorry



theorem theorem_159475_problem
  {n : ℕ} {R : Type*} [CommRing R]
  (d : Fin n → R)
  (D : Matrix (Fin n) (Fin n) R)
  (hD : D = Matrix.diagonal d)
  (k : ℕ) (hk : k > 0) :
  D ^ k = Matrix.diagonal (fun i => (d i) ^ k) := by
  sorry

theorem theorem_159928_problem (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ)
  (a b : Matrix (Fin n) (Fin 1) ℝ)
  (hQ : Q.transpose = Q) :
  (a.transpose * Q * b).transpose = a.transpose * Q * b := by
  sorry







theorem theorem_159706_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  (M : V →L[𝕜] V)
  (hM : ∃ L : V →L[𝕜] V, L.comp M = ContinuousLinearMap.id 𝕜 V)
  (u : ℕ → V)
  (hu_norm : ∀ n, ‖u n‖ = 1)
  (h_lim : Filter.Tendsto (fun n ↦ M (u n)) Filter.atTop (nhds 0)) :
  ¬ Filter.Tendsto u Filter.atTop (nhds 0) := by
  sorry

theorem theorem_160548_problem
  (K L : Type*)
  [NormedField K] [CompleteSpace K]
  [Field L] [Algebra K L] [FiniteDimensional K L]
  (v₁ v₂ : AbsoluteValue L ℝ)
  (h₁ : ∀ x : K, v₁ (algebraMap K L x) = ‖x‖)
  (h₂ : ∀ x : K, v₂ (algebraMap K L x) = ‖x‖) :
  v₁ = v₂ := by
  sorry

theorem theorem_159923_problem (a : ℕ → ℕ → ℝ) (a_n : ℕ → ℝ)
  (h_def : ∀ n m : ℕ, a n m = if n < m then 1 else 0)
  (h_seq : ∀ n : ℕ, Filter.Tendsto (a n) Filter.atTop (nhds (a_n n))) :
  Filter.Tendsto a_n Filter.atTop (nhds 1) := by
  sorry



theorem theorem_160253_problem (n : ℕ) :
  let K : Set ((Fin n → ℝ) × ℝ) := { x | ∑ i, |x.1 i| ≤ x.2 }
  let dual_cone_K : Set ((Fin n → ℝ) × ℝ) :=
    { y | ∀ x ∈ K, (∑ i, x.1 i * y.1 i) + x.2 * y.2 ≥ 0 }
  dual_cone_K = { y | 0 ≤ y.2 ∧ ∀ i, |y.1 i| ≤ y.2 } := by
  sorry







theorem theorem_160396_problem
  (n : ℕ)
  (U : Set (Fin n → ℂ))
  (hU : IsOpen U)
  (f : (Fin n → ℂ) → ℂ)
  (h_separate : ∀ (z : Fin n → ℂ), z ∈ U → ∀ (i : Fin n),
    DifferentiableAt ℂ (fun w => f (Function.update z i w)) (z i)) :
  DifferentiableOn ℂ f U := by
  sorry







theorem theorem_160306_problem (β₀ β₁ β₂ β₃ : ℝ)
  (x_A y_A x_B y_B : ℝ)
  (h_xA : x_A = Real.exp (β₀ + β₁ * 1 + β₂ * 1 + β₃ * (1 * 1)))
  (h_yA : y_A = Real.exp (β₀ + β₁ * 0 + β₂ * 1 + β₃ * (0 * 1)))
  (h_xB : x_B = Real.exp (β₀ + β₁ * 1 + β₂ * 0 + β₃ * (1 * 0)))
  (h_yB : y_B = Real.exp (β₀ + β₁ * 0 + β₂ * 0 + β₃ * (0 * 0))) :
  x_A / y_A = x_B / y_B ↔ β₃ = 0 := by
  sorry

theorem theorem_160734_problem (f : ℂ → ℂ)
  (h_entire : Differentiable ℂ f)
  (h_alg : ∃ P : MvPolynomial (Fin 2) ℂ, P ≠ 0 ∧ ∀ z : ℂ, MvPolynomial.eval ![z, f z] P = 0) :
  ∃ Q : Polynomial ℂ, ∀ z : ℂ, f z = Q.eval z := by
  sorry

theorem theorem_160513_problem
  (n : ℕ)
  (A F : Matrix (Fin n) (Fin n) ℝ)
  (hA_symm : A.IsSymm)
  (hA_pos : A.PosDef)
  (hF_lower : ∀ i j : Fin n, i < j → F i j = 0)
  (hF_diag : ∀ i : Fin n, 0 < F i i)
  (h_decomp : A = F * F.transpose) :
  Real.log A.det = 2 * ∑ i : Fin n, Real.log (F i i) := by
  sorry

theorem theorem_160453_problem (n : ℕ) (K₀ : Set (Matrix (Fin n) (Fin n) ℂ))
  (hK₀ : IsCompact K₀) :
  IsCompact (⋃ (i : Fin n) (j : Fin n), (fun A ↦ A i j) '' K₀) := by
  sorry



theorem theorem_160679_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (Y : Submodule ℝ X) (f : Y →L[ℝ] ℝ) :
  ∃ F : X →L[ℝ] ℝ, (∀ x : Y, F x = f x) ∧ ‖F‖ = ‖f‖ := by
  sorry













theorem theorem_160943_problem
  {n : ℕ}
  {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (ξ : Basis (Fin n) ℝ V)
  (g : Matrix (Fin n) (Fin n) ℝ)
  (hg : ∀ i j, g i j = inner (ξ i) (ξ j))
  (g_inv : Matrix (Fin n) (Fin n) ℝ)
  (hg_inv : g * g_inv = 1)
  (Z : V)
  (a : Fin n → ℝ)
  (ha : Z = ∑ i, a i • ξ i)
  (b : Fin n → ℝ)
  (hb : ∀ j, b j = inner Z (ξ j)) :
  ∀ k, a k = ∑ j, b j * g_inv j k := by
  sorry





theorem theorem_161307_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (P : H → ℝ) (f_hat : H) (h : H)
  (h_min : ∀ f : H, P f_hat ≤ P f)
  (D : ℝ)
  (h_lim : Filter.Tendsto (fun ε : ℝ ↦ (P (f_hat + ε • h) - P f_hat) / ε) (nhdsWithin 0 {0}ᶜ) (nhds D)) :
  D = 0 := by
  sorry







theorem theorem_161409_problem
  (m n : ℕ)
  (a : Fin m) (b : Fin n)
  (K X : Matrix (Fin m) (Fin n) ℝ)
  (hK_at : K a b = 1)
  (hK_else : ∀ i j, (i ≠ a ∨ j ≠ b) → K i j = 0)
  (g : Matrix (Fin m) (Fin n) ℝ → ℝ)
  (hg : ∀ M, g M = Matrix.trace (K.transpose * M)) :
  g X = 0 ↔ X a b = 0 := by
  sorry







theorem theorem_161432_problem (f : ℝ → ℝ) (x₀ x₁ x₂ : ℝ)
  (h_ord : x₀ < x₁ ∧ x₁ < x₂)
  (h_space : x₁ - x₀ = x₂ - x₁) :
  let L₀ : ℝ → ℝ := fun x ↦ (x - x₁) * (x - x₂) / ((x₀ - x₁) * (x₀ - x₂));
  let L₁ : ℝ → ℝ := fun x ↦ (x - x₀) * (x - x₂) / ((x₁ - x₀) * (x₁ - x₂));
  let L₂ : ℝ → ℝ := fun x ↦ (x - x₀) * (x - x₁) / ((x₂ - x₀) * (x₂ - x₁));
  let p₂ : ℝ → ℝ := fun x ↦ L₀ x * f x₀ + L₁ x * f x₁ + L₂ x * f x₂;
  ∫ x in x₀..x₂, p₂ x = (x₂ - x₀) / 6 * (f x₀ + 4 * f x₁ + f x₂) := by
  sorry





theorem theorem_161647_problem
  (a : ℝ)
  (k : EuclideanSpace ℝ (Fin 3))
  (ϕ : EuclideanSpace ℝ (Fin 3) → ℝ)
  (hϕ : ∀ r, ϕ r = Real.exp (a * inner k r)) :
  ∀ r, gradient ϕ r = (a * ϕ r) • k := by
  sorry



theorem theorem_161755_problem
  (n : ℕ)
  (r : ℝ → EuclideanSpace ℝ (Fin n))
  (t : ℝ)
  (h_diff : DifferentiableAt ℝ r t) :
  inner (r t) (deriv r t) = (1 / 2 : ℝ) * deriv (fun x => ‖r x‖ ^ 2) t := by
  sorry



theorem theorem_161549_problem
  {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  (M : Submodule ℝ X)
  (f : M →L[ℝ] ℝ)
  (p : Seminorm ℝ X)
  (hp : Continuous p)
  (h_bound : ∀ (m : M), |f m| ≤ p m) :
  ∃ F : X →L[ℝ] ℝ, (∀ (m : M), F m = f m) ∧ (∀ (x : X), |F x| ≤ p x) := by
  sorry

theorem theorem_161964_problem {K m n p : Type*} [Field K]
  [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
  (A : Matrix m n K) (B : Matrix n p K) :
  (A * B).rank ≤ min A.rank B.rank := by
  sorry

theorem theorem_160858_problem
  {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [InnerProductSpace ℂ T] [CompleteSpace T]
  (n : ℕ)
  (pure_tensor : (Fin n → H) → T)
  -- Condition: The tensor product space T is the closure of the span of pure tensors
  (h_pure_dense : (Submodule.span ℂ (Set.range pure_tensor)).topologicalClosure = ⊤)
  (antisym : T →L[ℂ] T)
  -- Condition: The range of the antisymmetrizer (space of antisymmetric wave functions) is closed
  (h_antisym_range_closed : IsClosed (LinearMap.range antisym : Set T)) :
  -- Question: Prove that the closure of the span of Slater determinants (antisymmetrized pure tensors)
  -- is exactly the space of antisymmetric wave functions (range of the antisymmetrizer).
  (Submodule.span ℂ (Set.range (fun f => antisym (pure_tensor f)))).topologicalClosure =
    LinearMap.range antisym := by
  sorry















theorem theorem_162573_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (K : Set V)
  (h_boundedly_compact : ∀ r : ℝ, IsCompact (K ∩ Metric.closedBall 0 r))
  (h_chebyshev : ∀ x : V, ∃! k ∈ K, ∀ y ∈ K, dist x k ≤ dist x y) :
  Convex ℝ K := by
  sorry



theorem theorem_162195_problem
  (n p : ℕ)
  (X : Matrix (Fin n) (Fin p) ℝ)
  (A : Matrix (Fin p) (Fin n) ℝ)
  (σ : ℝ)
  (h_rank : Invertible (X.transpose * X))
  (h_unbiased : A * X = 1) :
  let B := (X.transpose * X)⁻¹ * X.transpose
  let Cov_OLS := σ^2 • (B * B.transpose)
  let Cov_A := σ^2 • (A * A.transpose)
  Matrix.PosSemidef (Cov_A - Cov_OLS) := by
  sorry

theorem theorem_162443_problem 
  (m n : ℕ)
  (M : Matrix (Fin m) (Fin n) ℝ)
  (v w : Fin n → ℝ)
  (h_null : Matrix.mulVec M v = 0)
  (h_col : ∃ u : Fin m → ℝ, Matrix.mulVec M.transpose u = w) :
  Matrix.dotProduct v w = 0 := by
  sorry



theorem theorem_162284_problem
  (n : ℕ) (p : ℤ) (i : ℤ)
  (E : Type*) [AddCommGroup E] [Module ℝ E]
  (d : ℤ → E)
  (N : ℤ → ℝ → ℝ)
  (u : ℤ → ℝ)
  (s : ℝ → E)
  (hs : ∀ t, s t = ∑ j in Finset.Icc (-n : ℤ) (p - 1), N j t • d j)
  (h_range : -n ≤ i - 1 ∧ i - 1 ≤ p - 1)
  (h_local : ∀ j ∈ Finset.Icc (-n : ℤ) (p - 1), j ≠ i - 1 → N j (u i) = 0)
  (h_sum_one : ∑ j in Finset.Icc (-n : ℤ) (p - 1), N j (u i) = 1) :
  s (u i) = d (i - 1) ↔ N (i - 1) (u i) = 1 := by
  sorry



theorem theorem_162643_problem (n : ℕ) (hn : n > 0) (c : Fin n → ℂ) :
  let θ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  let F : Matrix (Fin n) (Fin n) ℂ := λ i j ↦ (1 / (Real.sqrt n : ℂ)) * θ ^ ((i : ℕ) * (j : ℕ))
  let C : Matrix (Fin n) (Fin n) ℂ := λ i j ↦ c (i - j)
  (F.conjTranspose * F = 1) ∧ (F.conjTranspose * C * F).IsDiag := by
  sorry

theorem theorem_162817_problem 
  {K : Type*} [Field K] 
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix m n K) 
  (B : Matrix m m K) 
  (y : m → K) 
  (x : n → K) 
  (hB : IsUnit B) 
  (h : B.mulVec (A.mulVec x - y) = 0) : 
  A.mulVec x = y := by
  sorry





theorem theorem_162803_problem
  (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  (A : Matrix (Fin 2) (Fin 2) R)
  (hA : Matrix.trace A = 0) :
  ∃ B C : Matrix (Fin 2) (Fin 2) R, A = B * C - C * B := by
  sorry



