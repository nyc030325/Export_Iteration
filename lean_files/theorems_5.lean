import Mathlib
import Mathlib.Tactic

theorem theorem_21053_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  (T : V →ₗ[K] W)
  (β β' : Basis n K V)
  (γ γ' : Basis m K W)
  (P : Matrix n n K) (hP : P = LinearMap.toMatrix β β' LinearMap.id)
  (Q : Matrix m m K) (hQ : Q = LinearMap.toMatrix γ γ' LinearMap.id) :
  LinearMap.toMatrix β' γ' T = Q * (LinearMap.toMatrix β γ T) * P⁻¹ := by
  sorry





theorem theorem_21232_problem (N F : ℕ) (w : Fin N → ℝ) (X : Matrix (Fin N) (Fin F) ℝ)
  (r : Fin N) (c : Fin F) :
  ∑ j : Fin N, w j * X r c * X j c = X r c * ∑ j : Fin N, w j * X j c := by
  sorry



theorem theorem_21396_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (p q : ℝ → E)
  (t : ℝ)
  (h_smooth_p : ContDiff ℝ ⊤ p)
  (h_smooth_q : ContDiff ℝ ⊤ q)
  (h_ne : p t ≠ q t) :
  deriv (fun x => ‖p x - q x‖) t =
    inner (p t - q t) (deriv p t - deriv q t) / ‖p t - q t‖ := by
  sorry



theorem theorem_21328_problem
  (V : Type*) [Ring V] [Algebra ℝ V]
  (K : Submodule ℝ V)
  (hK : IsCoatom K)
  (e_x τ : V →ₗ[ℝ] ℝ)
  (h_agree : ∀ f ∈ K, e_x f = τ f)
  (hex1 : e_x 1 = 1)
  (htau1 : τ 1 = 1)
  (htau_mult : ∀ x y, τ (x * y) = τ x * τ y) :
  e_x = τ := by
  sorry



theorem theorem_21166_problem (n : ℕ) (F Λ : Matrix (Fin n) (Fin n) ℝ)
  (hF : F.IsSymm) (hΛ : Invertible Λ) :
  (Λ * F * Λ.transpose).IsSymm := by
  sorry









theorem theorem_21785_problem (f : ℂ → ℂ)
  (h_holo : DifferentiableOn ℂ f (Metric.ball 0 1))
  (h_range : Set.MapsTo f (Metric.ball 0 1) (Metric.ball 0 1))
  (h_zero : f 0 = 0)
  (h_deriv : Complex.abs (deriv f 0) ≤ 1) :
  ∀ z ∈ Metric.ball 0 1, Complex.abs (f z) ≤ Complex.abs z := by
  sorry





theorem theorem_21787_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (Y : Submodule 𝕜 X)
  (F : Y →L[𝕜] 𝕜) :
  ∃ G : X →L[𝕜] 𝕜, (∀ y : Y, G y = F y) ∧ ‖G‖ = ‖F‖ := by
  sorry

theorem theorem_21680_problem
  (F : Type*) [Field F]
  (V W : Type*)
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W] :
  ∃ π : (W →ₗ[F] Module.Dual F V) ≃ₗ[F] (V →ₗ[F] Module.Dual F W),
    ∀ (f : W →ₗ[F] Module.Dual F V) (v : V) (w : W),
      π f v w = f w v := by
  sorry



theorem theorem_22213_problem
  (d : ℕ)
  (M : Matrix (Fin d) (Fin d) ℂ)
  (norm_M : ℝ)
  (h_norm : norm_M = Real.sqrt (∑ i, ∑ j, (Complex.abs (M i j)) ^ 2)) :
  ∑ i, ∑ j, (Complex.abs (M i j)) ^ 2 = norm_M ^ 2 := by
  sorry





theorem theorem_21649_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
  |inner x y / (‖x‖ * ‖y‖)| ≤ 1 := by
  sorry

theorem theorem_21763_problem
  (e : Fin 3 → (Fin 3 → ℝ))
  (he : e = Pi.basisFun ℝ (Fin 3))
  (w₁ w₂ : Fin 3 → ℝ)
  (hw₁ : w₁ = e 0 - e 1)
  (hw₂ : w₂ = e 1 - e 2)
  (σ : Equiv.Perm (Fin 3))
  (hσ : σ = Equiv.swap 0 1)
  (T : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
  (hT : T = { toFun := λ v ↦ v ∘ σ, map_add' := λ _ _ ↦ rfl, map_smul' := λ _ _ ↦ rfl })
  (M : Matrix (Fin 2) (Fin 2) ℝ)
  (hM : M = !![-1, 1; 0, 1]) :
  T w₁ = M 0 0 • w₁ + M 1 0 • w₂ ∧
  T w₂ = M 0 1 • w₁ + M 1 1 • w₂ := by
  sorry

theorem theorem_22230_problem
  (n : ℕ) (hn : 0 < n)
  (y : ℝ) (hy : -1 ≤ y ∧ y ≤ 1)
  (k : Fin n)
  (x : Fin n → ℝ)
  -- The problem states x_i are in [-1, 1], though the algebraic identity holds generally.
  (hx : ∀ i, i ≠ k → -1 ≤ x i ∧ x i ≤ 1)
  -- The denominator must be non-zero for the normalization to be well-defined.
  (h_denom : ∑ j in Finset.univ.erase k, (x j)^2 ≠ 0)
  -- Definition of x'
  (x' : Fin n → ℝ)
  (h_x' : ∀ i, x' i = if i = k then y 
                      else x i * Real.sqrt ((1 - y^2) / (∑ j in Finset.univ.erase k, (x j)^2))) :
  ∑ i, (x' i)^2 = 1 := by
  sorry





theorem theorem_21800_problem
  {E : Type*} [AddCommGroup E] [Module ℂ E] [StarAddMonoid E] [StarModule ℂ E] [InvolutiveStar E]
  (V : E)
  (V₁ V₂ : E)
  (hV₁ : V₁ = V + star V)
  (hV₂ : V₂ = -Complex.I • (V - star V))
  (h_basis : LinearIndependent ℂ ![V₁, V₂])
  (a b : ℂ)
  (W : E)
  (hW_def : W = a • V₁ + b • V₂)
  (hW_real : star W = W) :
  a.im = 0 ∧ b.im = 0 := by
  sorry







theorem theorem_22167_problem
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix m n ℝ)
  (D : Matrix n n ℝ)
  (γ : ℝ)
  (hγ : 0 < γ)
  (hD_diag : D.IsDiag)
  (hD_pd : D.PosDef) :
  let sqrtD := Matrix.diagonal (fun i => Real.sqrt (D i i))
  let I := (1 : Matrix n n ℝ)
  (A.transpose * A + γ • D)⁻¹ =
    sqrtD⁻¹ * ((A * sqrtD⁻¹).transpose * (A * sqrtD⁻¹) + γ • I)⁻¹ * sqrtD⁻¹.transpose := by
  sorry



theorem theorem_21839_problem {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]
  (A B C : Matrix n n K)
  (hC : IsUnit C)
  (h : A = C * B * C⁻¹) :
  spectrum K A = spectrum K B := by
  sorry



theorem theorem_22755_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
  Matrix.trace (Matrix.adjugate A) = (-1 : ℝ) ^ (n - 1) * (Matrix.charpoly A).coeff 1 := by
  sorry

theorem theorem_22540_problem
  (d : ℕ)
  (a : Fin d → ℝ)
  (s t : Fin d → Fin d → ℝ)
  -- We abstract the random variables as elements of a commutative ring R that is an algebra over ℝ
  (R : Type*) [CommRing R] [Algebra ℝ R]
  (x : Fin d → R)
  (E : R → ℝ) -- The expectation operator
  (X Y : Fin d → R)
  -- Definition of X and Y as linear combinations
  (hX : ∀ r, X r = ∑ k, s r k • x k)
  (hY : ∀ r, Y r = ∑ l, t r l • x l)
  -- The zero-mean jointly normal condition implies Isserlis' theorem for 4th moments
  (h_isserlis : ∀ i j r, E (x i * x j * X r * Y r) =
    E (x i * x j) * E (X r * Y r) +
    E (x i * X r) * E (x j * Y r) +
    E (x i * Y r) * E (x j * X r))
  -- Definition of u
  (u : Fin d → Fin d → ℝ)
  (hu : ∀ i j, u i j = ∑ r, a r * E (x i * x j * X r * Y r)) :
  ∀ i j, u i j =
    E (x i * x j) * (∑ r, a r * E (X r * Y r)) +
    ∑ r, a r * E (x i * X r) * E (x j * Y r) +
    ∑ r, a r * E (x i * Y r) * E (x j * X r) := by
  sorry



theorem theorem_22767_problem (C : Set (ℝ × ℝ × ℝ × ℝ))
  (hC : C = { x | x.1 * x.2.2.1 + x.2.1 * x.2.2.2 = 1 }) :
  ¬ Convex ℝ C := by
  sorry

theorem theorem_22300_problem
  (K : Type*) [Field K]
  (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  -- Z(Σ_f) is the TQFT invariant of Σ_f (a scalar)
  (z_sigma_f : K)
  -- Σ(f) is the linear map induced by the diffeomorphism f
  (sigma_f_map : V →ₗ[K] V)
  -- We abstract the TQFT operation of "identifying boundaries" of a cobordism.
  -- This function maps the operator associated with the cobordism (Σ × I twisted by f)
  -- to the invariant of the resulting closed manifold.
  (identify_boundaries : (V →ₗ[K] V) → K)
  -- Condition 1: Σ_f is obtained by identifying the boundaries of Σ × I using f.
  -- This implies the invariant z_sigma_f is the result of this operation on sigma_f_map.
  (h_construction : z_sigma_f = identify_boundaries sigma_f_map)
  -- Condition 2: Z is a TQFT.
  -- The axioms of TQFT imply that the invariant of a manifold formed by identifying boundaries
  -- (a mapping torus) is the trace of the induced linear map.
  (h_tqft : ∀ (L : V →ₗ[K] V), identify_boundaries L = LinearMap.trace K V L) :
  -- Conclusion: The invariant is the trace of the map.
  z_sigma_f = LinearMap.trace K V sigma_f_map := by
  sorry

theorem theorem_22796_problem :
  let A : Matrix (Fin 3) (Fin 3) ℚ := !![3, 10, 5; 4, 3, 3; 15, 4, 14]
  let b : Fin 3 → ℚ := ![20, -24, -180]
  let x : Fin 3 → ℚ := ![-4.7273, 8.5333, -10.2303]
  (Matrix.mulVec A x = b) ∧ (∀ y, Matrix.mulVec A y = b → y = x) := by
  sorry



theorem theorem_23043_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
  A.det = A.transpose.det := by
  sorry

theorem theorem_23409_problem (a1 a2 b1 b2 : ℝ)
  (h1 : a1 + a2 = 100)
  (h2 : b1 + b2 = 80) :
  a1 * b2 - a2 * b1 = 80 * a1 - 100 * b1 := by
  sorry



















theorem theorem_23576_problem
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (G : Type*) [Group G] [Fintype G]
  (ρ : Representation ℂ G V)
  (inner_rho : V → V → ℂ)
  (h_inner_rho : ∀ u v, inner_rho u v = ∑ x : G, ⟪ρ x u, ρ x v⟫_ℂ)
  (A : V →ₗ[ℂ] V)
  (g : G)
  (rho_g_star : V →ₗ[ℂ] V)
  (h_rho_g_star : ∀ u v, inner_rho (ρ g u) v = inner_rho u (rho_g_star v)) :
  LinearMap.trace ℂ V (A * rho_g_star) = LinearMap.trace ℂ V (A * (ρ g⁻¹)) := by
  sorry

















theorem theorem_24271_problem
  {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (Γ : Set E)
  (hΓ : ∀ u ∈ Γ, ‖u‖ = 1)
  (ι : Type*) (F : Finset ι)
  (a : ι → 𝕜)
  (u : ι → E)
  (hu : ∀ i ∈ F, u i ∈ Γ)
  (x : E)
  (hx : x = ∑ i in F, a i • u i) :
  ‖x‖ ≤ ∑ i in F, ‖a i‖ := by
  sorry



















theorem theorem_24697_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  (T : V →ₗ[K] V) :
  LinearMap.range (T ^ 2) ≤ LinearMap.range T := by
  sorry





theorem theorem_24769_problem
  {K : Type*} [RCLike K]
  {X : Type*} [AddCommGroup X] [Module K X]
  [FiniteDimensional K X]
  (n₁ n₂ : X → ℝ)
  (h1_nonneg : ∀ x, 0 ≤ n₁ x)
  (h1_def : ∀ x, n₁ x = 0 ↔ x = 0)
  (h1_hom : ∀ (c : K) x, n₁ (c • x) = ‖c‖ * n₁ x)
  (h1_tri : ∀ x y, n₁ (x + y) ≤ n₁ x + n₁ y)
  (h2_nonneg : ∀ x, 0 ≤ n₂ x)
  (h2_def : ∀ x, n₂ x = 0 ↔ x = 0)
  (h2_hom : ∀ (c : K) x, n₂ (c • x) = ‖c‖ * n₂ x)
  (h2_tri : ∀ x y, n₂ (x + y) ≤ n₂ x + n₂ y) :
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ x : X, C₁ * n₁ x ≤ n₂ x ∧ n₂ x ≤ C₂ * n₁ x := by
  sorry



theorem theorem_25117_problem
  (n k : ℕ)
  (X : ℕ → ℝ)
  (w : EuclideanSpace ℝ (Fin k))
  (R : EuclideanSpace ℝ (Fin n) → ℝ)
  (s : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n))
  (h_s : ∀ (w' : EuclideanSpace ℝ (Fin k)) (i : Fin n), s w' i = ∑ j : Fin k, w' j * X ((i : ℕ) + (j : ℕ)))
  (hR : DifferentiableAt ℝ R (s w))
  (a : Fin k) :
  gradient (fun w' => R (s w')) w a = ∑ i : Fin n, gradient R (s w) i * X ((i : ℕ) + (a : ℕ)) := by
  sorry











theorem theorem_25553_problem (a b c : ℝ) :
  let D : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; a, 1, 0; b, c, 1]
  let J : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  let Φ := - (D⁻¹ * D.transpose)
  Φ⁻¹ = J * Φ * J ↔ a = c := by
  sorry



theorem theorem_25549_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (A B : Set V)
  (h1 : B ⊆ Submodule.span K A)
  (h2 : LinearIndependent K (Subtype.val : A → V))
  (h3 : LinearIndependent K (Subtype.val : B → V)) :
  Cardinal.mk B ≤ Cardinal.mk A := by
  sorry



theorem theorem_25373_problem
  -- S is the Schwartz space, represented by SchwartzMap ℝ ℝ
  (D : Submodule ℝ (SchwartzMap ℝ ℝ))
  -- D represents the space of compactly supported functions
  (hD : ∀ φ, φ ∈ D ↔ HasCompactSupport φ)
  -- f is a linear functional on D
  (f : D →ₗ[ℝ] ℝ)
  -- f is discontinuous
  (hf : ¬ Continuous f) :
  -- Conclusion: f cannot have a continuous extension to the closure of D
  ¬ ∃ (F : D.topologicalClosure →L[ℝ] ℝ),
    ∀ (x : D), F (Submodule.inclusion D.le_topologicalClosure x) = f x := by
  sorry













theorem theorem_26445_problem
  (r : ℕ)
  (x : Fin r → ℝ)
  (ρ μ : ℝ)
  (hx_pos : ∀ i, x i > 0)
  (hρ_pos : ρ > 0)
  (h_sum : ∑ i, (μ - 1 / (ρ * x i)) = 1) :
  μ * (r : ℝ) - (1 / ρ) * ∑ i, (1 / x i) = 1 := by
  sorry







theorem theorem_26787_problem
  {K : Type*} [Field K]
  {m k p : Type*} [Fintype m] [Fintype k] [Fintype p]
  [DecidableEq m] [DecidableEq k] [DecidableEq p]
  {n : ℕ}
  (A : Matrix m k K)
  (U : Submodule K (k → K))
  (hU : U = LinearMap.ker (Matrix.toLin' A))
  (u : Basis (Fin n) K U)
  (BaseU : Matrix p k K)
  (hBaseU : LinearMap.ker (Matrix.toLin' BaseU) = ⊥)
  (w : Fin n → (p → K))
  (hw : ∀ i, w i = Matrix.mulVec BaseU (u i)) :
  LinearIndependent K w := by
  sorry

