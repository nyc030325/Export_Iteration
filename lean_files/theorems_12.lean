import Mathlib
import Mathlib.Tactic

















theorem theorem_58935_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (vals : Fin n → ℝ) (hA : A.IsSymm) :
  ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then 2 * (A i j)^2 else 0) ≤
  ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then (Real.exp (vals i - vals j) + Real.exp (vals j - vals i)) * (A i j)^2 else 0) := by
  sorry





theorem theorem_59281_problem :
  ¬ ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      (r q : V) (Tr Tq : V →ₗ[ℝ] V),
    r ≠ 0 → q ≠ 0 →
    (∀ η, η ≠ 0 → inner (Tr η) r = (0 : ℝ)) →
    (∀ η, η ≠ 0 → inner (Tq η) q = (0 : ℝ)) →
    (∀ η, η ≠ 0 → inner (Tr η) (Tq η) = (0 : ℝ)) := by
  sorry

theorem theorem_59270_problem
  {X : Type*} [NormedRing X]
  -- Hypothesis: The norm is multiplicative (factorization property mentioned in solution)
  (h_mult_norm : ∀ x y : X, ‖x * y‖ = ‖x‖ * ‖y‖)
  -- Hypothesis: The space contains elements of arbitrary positive norm
  (h_exists_norm : ∀ k : ℝ, k > 0 → ∃ x : X, ‖x‖ = k)
  -- Given definitions
  (f p : X) (c : ℝ)
  (h_diff : ‖f - p‖ = c)
  (hc : c > 0) :
  -- Conclusion: The quantity becomes arbitrarily large as k -> ∞
  ∀ M : ℝ, ∃ K : ℝ, ∀ k : ℝ, k > K →
    ∃ g q : X, ‖g‖ = k ∧ ‖g - q‖ = 0 ∧ ‖f * g - p * q‖^2 > M := by
  sorry









theorem theorem_59962_problem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : ℕ}
  (T : V →ₗ[K] V)
  (β : Basis (Fin n) K V)
  (γ : Basis (Fin n) K V)
  (u : V) :
  T u = ∑ i : Fin n, (Matrix.mulVec (LinearMap.toMatrix β γ T) (β.equivFun u) i) • (γ i) := by
  sorry

theorem theorem_59519_problem :
  ∃ (m n p q : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ) (C : Matrix (Fin p) (Fin q) ℝ),
    Matrix.rank A = min m n ∧
    Matrix.rank B = min n p ∧
    Matrix.rank C = min p q ∧
    A * B * C = 0 := by
  sorry



theorem theorem_60068_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (N : V → ℝ)
  (hN_def : ∀ v, N v = 0 ↔ v = 0)
  (hN_hom : ∀ (c : ℝ) v, N (c • v) = |c| * N v)
  (hN_tri : ∀ u v, N (u + v) ≤ N u + N v)
  (h_inv : ∀ (R : V ≃ₗᵢ[ℝ] V) (v : V), N (R v) = N v) :
  ∃ c : ℝ, ∀ v, N v = c * ‖v‖ := by
  sorry







theorem theorem_59402_problem
  {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (T : V →ₗ[K] W) (f : W)
  (h_sol : ∃ y, T y = f)
  (x : V) (hx : T x = f) :
  ∃ x_h x_p : V, T x_h = 0 ∧ T x_p = f ∧ x = x_h + x_p := by
  sorry

theorem theorem_60138_problem (n : ℕ) (hn : n > 0) (K : Type*) [Field K] [DecidableEq K]
  (G : Submonoid (Matrix (Fin n) (Fin n) K))
  (h_group : Group ↥G)
  (B : Matrix (Fin n) (Fin n) K)
  (hB : B ∈ G)
  (h_eig : ∀ x, Module.End.HasEigenvalue (Matrix.toLin' B) x ↔ x = 0) :
  False := by
  sorry

theorem theorem_59661_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (B : V → V → F)
  (σ : F ≃+* F)
  (h : ∀ (v : V) (β₁ β₂ : F), B (β₁ • v) (β₂ • v) = β₁ * (σ β₂) * (B v v))
  (v : V)
  (hv : B v v = 0) :
  ∀ (β₁ β₂ : F), B (β₁ • v) (β₂ • v) = 0 := by
  sorry



theorem theorem_60566_problem {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  (A : V →ₗ[𝕜] V) (e_k : Set V)
  (h1 : (LinearMap.range A : Set V) ⊆ closure (Submodule.span 𝕜 e_k : Set V))
  (h2 : Dense (LinearMap.range A : Set V)) :
  Dense (Submodule.span 𝕜 e_k : Set V) := by
  sorry





theorem theorem_60474_problem (m : ℕ) (f : ℝ → ℝ) (g : ℝ → (Fin m → ℝ))
  (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
  deriv (fun x => f x • g x) = fun x => (deriv f x) • g x + f x • (deriv g x) := by
  sorry

theorem theorem_59792_problem (F : Type) [Field F] :
  ∃ (n : ℕ) (A B : Matrix (Fin n) (Fin n) F), A * B ≠ B * A := by
  sorry

theorem theorem_59859_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (X : ℕ → E)
  (h_ortho : ∀ n m, n ≠ m → ⟪X n, X m⟫_ℝ = 0)
  (c : ℕ → ℝ)
  (hc_def : ∀ n, c n = ⟪X n, X n⟫_ℝ)
  (hc_pos : ∀ n, c n > 0) :
  Orthonormal ℝ (fun n ↦ (1 / Real.sqrt (c n)) • X n) := by
  sorry









theorem theorem_59236_problem (f : ℂ → ℂ) (z₀ : ℂ)
  (h1 : ∀ z : ℂ, (f z).im = 0)
  (h2 : DifferentiableAt ℂ f z₀) :
  (deriv f z₀).im = 0 := by
  sorry















theorem theorem_60634_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (M : Submodule 𝕜 E) [FiniteDimensional 𝕜 M] :
  ∃ (n : ℕ) (f : Fin n → E →L[𝕜] 𝕜),
    IsCompl M (⨅ i, LinearMap.ker (f i)) := by
  sorry



theorem theorem_61261_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA_sym : A.IsSymm) (hB_sym : B.IsSymm)
  (hA_psd : A.PosSemidef) (hB_psd : B.PosSemidef)
  (hAB : (B - A).PosSemidef) :
  Convex ℝ {X : Matrix (Fin n) (Fin n) ℝ | X.IsSymm ∧ (X - A).PosSemidef ∧ (B - X).PosSemidef} := by
  sorry





theorem theorem_61684_problem
  (n : ℕ)
  (V : Type*)
  [CommRing V] [Algebra ℝ V]
  (D : Fin n → V → V)
  (integral : V → ℝ)
  (a : Fin n → Fin n → V)
  (b : Fin n → V)
  (f : V)
  (L : V → V)
  (L_star : V → V)
  (hL : ∀ u, L u = (∑ i : Fin n, ∑ j : Fin n, a i j * D j (D i u)) + ∑ i : Fin n, b i * D i u)
  (hL_star : ∀ v, L_star v = (∑ i : Fin n, ∑ j : Fin n, D j (D i (a i j * v))) - ∑ i : Fin n, D i (b i * v)) :
  (∃ u, L u = f) ↔ (∀ v, L_star v = 0 → integral (v * f) = 0) := by
  sorry

theorem theorem_60310_problem
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (Y Z : Matrix (Fin n) (Fin n) ℝ)
  (hY_symm : Y.IsSymm) (hY_psd : Y.PosSemidef)
  (hZ_symm : Z.IsSymm) (hZ_psd : Z.PosSemidef)
  (h1_Y : (A.transpose * A * Y * Y.transpose).IsSymm)
  (h1_Z : (A.transpose * A * Z * Z.transpose).IsSymm)
  (h2 : ∀ (μ ν : ℝ),
    Module.End.HasEigenvalue (Matrix.toLin' (Y * Y.transpose)) μ →
    Module.End.HasEigenvalue (Matrix.toLin' (Z * Z.transpose)) ν →
    μ > ν)
  (h3 : (A.transpose * A * (Y * Y.transpose - Z * Z.transpose)).IsSymm) :
  (A.transpose * A * (Y * Y.transpose - Z * Z.transpose)).PosSemidef := by
  sorry

theorem theorem_62345_problem (R S : Type*) [Ring R] [AddCommGroup S] [Module R S] (n : ℕ) :
  ∃ Φ : ((Fin n → S) →ₗ[R] (Fin n → S)) ≃+* Matrix (Fin n) (Fin n) (S →ₗ[R] S),
    ∀ (ϕ : (Fin n → S) →ₗ[R] (Fin n → S)) (i j : Fin n),
      Φ ϕ i j = (LinearMap.proj i).comp (ϕ.comp (LinearMap.stdBasis R (fun _ ↦ S) j)) := by
  sorry











theorem theorem_58902_problem
  (U : Set (ℂ × ℂ))
  (hU_open : IsOpen U)
  (hU_conn : IsConnected U)
  (f : ℂ × ℂ → ℂ)
  (hf_holo : DifferentiableOn ℂ f U)
  (h_zero_locus : ∃ p, {z ∈ U | f z = 0} = {p}) :
  ¬ ∃ g, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, f z * g z = 1 := by
  sorry



theorem theorem_61451_problem (n : ℕ) (z w : EuclideanSpace ℝ (Fin n))
  (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
  ‖z + w‖^2 + ‖z - w‖^2 = 2 * (‖z‖^2 + ‖w‖^2) := by
  sorry

theorem theorem_62025_problem (n : ℕ) :
  let S := MvPolynomial (Fin n × Fin n) ℂ
  let M : Matrix (Fin n) (Fin n) S := fun i j ↦ MvPolynomial.X (i, j)
  let Δ := M.det
  let R := Polynomial S
  let I : Ideal R := Ideal.span {Polynomial.X * Polynomial.C Δ - 1}
  Nonempty ((R ⧸ I) ≃+* Localization.Away Δ) := by
  sorry





theorem theorem_61917_problem
  {X : Type*} [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace X] [TopologicalAddGroup X] [ContinuousSMul ℝ X]
  (M : Submodule ℝ X)
  (hM : (interior (M : Set X)).Nonempty) :
  M = ⊤ := by
  sorry



theorem theorem_62149_problem
  (𝕜 : Type*) [RCLike 𝕜]
  (V : Type*) [AddCommGroup V] [Module 𝕜 V]
  [FiniteDimensional 𝕜 V]
  (n1 n2 : V → ℝ)
  (h_n1_nonneg : ∀ v, 0 ≤ n1 v)
  (h_n1_eq_zero : ∀ v, n1 v = 0 ↔ v = 0)
  (h_n1_smul : ∀ (c : 𝕜) (v : V), n1 (c • v) = ‖c‖ * n1 v)
  (h_n1_triangle : ∀ u v, n1 (u + v) ≤ n1 u + n1 v)
  (h_n2_nonneg : ∀ v, 0 ≤ n2 v)
  (h_n2_eq_zero : ∀ v, n2 v = 0 ↔ v = 0)
  (h_n2_smul : ∀ (c : 𝕜) (v : V), n2 (c • v) = ‖c‖ * n2 v)
  (h_n2_triangle : ∀ u v, n2 (u + v) ≤ n2 u + n2 v) :
  ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ v, A * n1 v ≤ n2 v ∧ n2 v ≤ B * n1 v := by
  sorry



theorem theorem_61931_problem (d : ℕ) (p : ℝ) (hd : 1 ≤ d)
  (P : Matrix (Fin (2 * d)) (Fin (2 * d)) ℝ)
  (hP : P = (1 / (2 * d : ℝ)) • Matrix.of (fun _ _ ↦ 1))
  (A : Matrix (Fin (2 * d)) (Fin (2 * d)) ℝ)
  (hA : A = ((2 * (1 - p) * (d : ℝ)) / ((2 * d : ℝ) - 1)) • P +
            ((2 * (d : ℝ) * p - 1) / ((2 * d : ℝ) - 1)) • 1) :
  spectrum ℝ (Matrix.toLin' A) = {((2 * (d : ℝ) * p - 1) / ((2 * d : ℝ) - 1)), 1} := by
  sorry





theorem theorem_61329_problem
  (p : ℝ) (hp : 1 ≤ p)
  (a b : ℝ) (hab : a < b)
  -- We model the ambient Sobolev space W^{1,p}(a,b) as a NormedAddCommGroup W.
  (W : Type*) [NormedAddCommGroup W]
  -- C corresponds to the subspace of test functions C_0^\infty(a,b)
  (C : Set W)
  -- W₀ corresponds to the Sobolev space W_0^{1,p}(a,b)
  (W₀ : Set W)
  -- The solution utilizes the definition that W_0^{1,p} is the closure of C_0^\infty
  (hW₀ : W₀ = closure C)
  -- The specific claim: for every u in W₀ and ε > 0, we can approximate u by v in C
  (u : W) (hu : u ∈ W₀)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ v ∈ C, dist u v < ε := by
  sorry



theorem theorem_61898_problem
  (N M : ℕ)
  (X : Type*)
  (x : Fin N → X)
  (φ : X → Fin M → ℝ)
  (Φ : Matrix (Fin N) (Fin M) ℝ)
  (hΦ : ∀ i j, Φ i j = φ (x i) j) :
  Φ.transpose * Φ = ∑ i : Fin N, Matrix.vecMulVec (φ (x i)) (φ (x i)) := by
  sorry

theorem theorem_62424_problem
  {α : Type*}
  (U : Set α)
  (f : α → ℝ)
  (ϕ : ℕ → α → ℝ)
  (N : ℕ)
  (h_bdd : BddAbove (f '' U))
  (h_sup : sSup (f '' U) ≤ 2 ^ N)
  (h_ineq : ∀ n, n ≥ N → ∀ x ∈ U, 0 ≤ f x - ϕ n x ∧ f x - ϕ n x ≤ (2 : ℝ) ^ (-(n : ℝ))) :
  TendstoUniformlyOn ϕ f Filter.atTop U := by
  sorry





theorem theorem_62725_problem (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
  (h : M.transpose * M = 1) :
  M.det = 1 ∨ M.det = -1 := by
  sorry













theorem theorem_62956_problem
  {K : Type*} [Field K]
  {m k n : Type*} [Fintype m] [Fintype k] [Fintype n]
  [DecidableEq m] [DecidableEq k] [DecidableEq n]
  (A : Matrix m k K) (B : Matrix k n K) :
  Matrix.rank (A * B) ≤ min (Matrix.rank A) (Matrix.rank B) := by
  sorry



theorem theorem_62813_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  (k : ℕ)
  (v : Fin k → V)
  (hv : LinearIndependent K v)
  (w : V)
  (h : ∃ a : Fin k → K, a ≠ 0 ∧ ∑ i, a i • (v i + w) = 0) :
  w ∈ Submodule.span K (Set.range v) := by
  sorry





theorem theorem_63401_problem
  {R n m : Type*} [CommRing R] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]
  (A : Matrix n n R)
  (B : Matrix m n R) :
  Matrix.trace (B * A * B.transpose) = Matrix.trace (A * B.transpose * B) ∧
  Matrix.trace (A * B.transpose * B) = Matrix.trace (B.transpose * B * A) := by
  sorry

theorem theorem_63174_problem (m n : ℕ) (hm : m < n)
  (B : Matrix (Fin m) (Fin n) ℝ)
  (A : Matrix (Fin m) (Fin m) ℝ)
  (hA : A.IsSymm) :
  ¬ (B.transpose * A * B).PosDef := by
  sorry









theorem theorem_63128_problem
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  (σ : V → Matrix (Fin 2) (Fin 2) ℂ)
  (L : List V) :
  let ϕ : List V → ℂ := λ l => Matrix.trace (l.map σ).prod
  ϕ L = ϕ (L.rotate 1) := by
  sorry



theorem theorem_64559_problem (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] (n : ℕ) (h_dim : FiniteDimensional.finrank F V = n) :
  (Nontrivial (Module.End F V) ∧ ∀ f : Module.End F V, f ≠ 0 → IsUnit f) ↔ n = 1 := by
  sorry

theorem theorem_63736_problem {n : Type*} [Fintype n] [DecidableEq n]
  (A Q Λ : Matrix n n ℂ) (f : ℂ → ℂ) (c : ℕ → ℂ)
  (h_diag : Λ.IsDiag)
  (h_inv : Invertible Q)
  (h_decomp : A = Q * Λ * Q⁻¹)
  (h_f_eigen : ∀ i, HasSum (fun k => c k * (Λ i i) ^ k) (f (Λ i i)))
  (fA : Matrix n n ℂ)
  (h_fA_def : HasSum (fun k => c k • (A ^ k)) fA) :
  fA = Q * (Matrix.diagonal (fun i => f (Λ i i))) * Q⁻¹ := by
  sorry

