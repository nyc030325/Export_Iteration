import Mathlib
import Mathlib.Tactic





theorem theorem_361983_problem
  {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]
  {I : Type*} [Fintype I]
  {J : Type*} [Fintype J]
  (A : I → M)
  (B : J → N) :
  (∑ i : I, A i) ⊗ₜ[R] (∑ j : J, B j) = ∑ i : I, ∑ j : J, A i ⊗ₜ[R] B j := by
  sorry



theorem theorem_362884_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (A : X →L[ℂ] X)
  (z : ℂ)
  (hz : z ≠ 0)
  (hzA : z ∉ spectrum ℂ A)
  (hA : 0 ∉ spectrum ℂ A) :
  ‖Ring.inverse (z⁻¹ • (1 : X →L[ℂ] X) - Ring.inverse A)‖ ≤
    Complex.abs z * ‖A‖ * ‖Ring.inverse (z • (1 : X →L[ℂ] X) - A)‖ := by
  sorry





theorem theorem_363106_problem
  (n : ℕ)
  (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (c : ℝ)
  (hc : 0 < c)
  (h_diff : Differentiable ℝ F)
  (h_orth : ∀ x,
    let J := fderiv ℝ F x
    let sJ := (Real.sqrt c) • J
    sJ.adjoint.comp sJ = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) :
  ∃ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin n)),
    A.adjoint.comp A = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) ∧
    ∀ x, F x = (1 / Real.sqrt c) • (A x + b) := by
  sorry





theorem theorem_363181_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (h_inf : ¬ FiniteDimensional 𝕜 X) :
  ¬ Function.Surjective (Module.Dual.eval 𝕜 X) := by
  sorry

theorem theorem_362728_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (a : V →L[ℝ] V →L[ℝ] ℝ)
  (b : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
  (l : V →L[ℝ] ℝ)
  (nu alpha : ℝ)
  (h_alpha_pos : 0 < alpha)
  (h_a_coercive : ∀ u, alpha * ‖u‖^2 ≤ a u u)
  (Phi : V → V)
  (h_Phi : ∀ u, (∀ v, nu * a (Phi u) v + b u (Phi u) v = l v) ∧
                (∀ w, (∀ v, nu * a w v + b u w v = l v) → w = Phi u)) :
  ∃ u_star, Phi u_star = u_star := by
  sorry



theorem theorem_362994_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : Type*} [Fintype n] [DecidableEq n]
  (b : Basis n K V) (b' : Basis n K V)
  (T : V →ₗ[K] V)
  (M M' P : Matrix n n K)
  (hM : M = LinearMap.toMatrix b b T)
  (hM' : M' = LinearMap.toMatrix b' b' T)
  (hP : P = b.toMatrix b') :
  M' = P * M * P⁻¹ := by
  sorry





theorem theorem_363404_problem (n : ℕ)
  (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  (B : Set (Fin n → ℝ))
  (hB : B.Nonempty) :
  ∃ f : (Fin n → ℝ) → Set (Fin n → ℝ), ∀ x, f x = { y | ∃ u ∈ B, y = A x + u } := by
  sorry





theorem theorem_362976_problem
  (n : ℕ)
  (v₀ v₁ : EuclideanSpace ℝ (Fin n))
  (h₁ : ‖v₀‖ ≠ ‖v₁‖)
  (h₂ : v₀ ≠ -v₁) :
  let E : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun _ ↦
    ‖v₁ - v₀‖ • (v₀ + v₁) - Real.sqrt (‖v₁‖^2 - 2 * inner v₁ v₀ + ‖v₀‖^2) • (v₀ + v₁)
  ∃ v, ∀ w, ‖E v‖ ≤ ‖E w‖ := by
  sorry



theorem theorem_364055_problem {R : Type*} [CommRing R] {n : ℕ}
  (A : Matrix (Fin n) (Fin n) R)
  (i j : Fin n) (h_neq : i ≠ j) (h_eq : A i = A j) :
  A.det = 0 := by
  sorry



theorem theorem_363333_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {T : Type*}
  (m : ℕ)
  (x y : E)
  (z : Fin m → ℝ)
  (f : Fin m → T → E → ℝ)
  (t : T)
  (s : ℝ)
  (hf : ∀ i, DifferentiableAt ℝ (fun u ↦ f i t u) ((1 - s) • x + s • y)) :
  deriv (fun σ ↦ ∑ i : Fin m, z i * f i t ((1 - σ) • x + σ • y)) s =
  ∑ i : Fin m, z i * (fderiv ℝ (fun u ↦ f i t u) ((1 - s) • x + s • y) (y - x)) := by
  sorry





theorem theorem_363913_problem (n : ℕ) (hn : 2 ≤ n) :
  ¬ ∃ (f : Fin n → ℝ → ℝ), ∀ (A : Matrix (Fin n) (Fin n) ℝ),
    0 < Matrix.det (1 + A) →
    Real.log (Matrix.det (1 + A)) = ∑ i : Fin n, f i (A i i) := by
  sorry









theorem theorem_365020_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : IsUnit A)
  (B : Matrix (Fin n) (Fin n) ℝ) (hB : B = A.transpose * A)
  (μ : ℝ) (hμ : Module.End.HasEigenvalue (Matrix.toLin' B) μ) :
  Module.End.HasEigenvalue (Matrix.toLin' B⁻¹) (1 / μ) := by
  sorry

theorem theorem_364712_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
  (T : H₁ →L[𝕜] H₂) :
  (LinearMap.ker (ContinuousLinearMap.adjoint T)).orthogonal =
  (LinearMap.range T).topologicalClosure := by
  sorry

theorem theorem_364674_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (w : ℕ → E) (w_star : E) (gamma : ℝ)
  (h_gamma : gamma > 0)
  (h_w1 : w 1 = 0)
  (h_step : ∀ k : ℕ, 1 ≤ k → inner (w (k + 1)) w_star > inner (w k) w_star + gamma) :
  ∀ k : ℕ, 2 ≤ k → inner (w k) w_star > ((k : ℝ) - 1) * gamma := by
  sorry











theorem theorem_364926_problem (A B C : ℤ)
  (h_gcd : Int.gcd A (Int.gcd B C) = 1)
  (h_pos_def : A * C - B^2 > 0)
  (h_min_length : ∀ (x y : ℤ), (x ≠ 0 ∨ y ≠ 0) → A * x^2 + 2 * B * x * y + C * y^2 ≥ A)
  (h_div : A ∣ B) :
  let G : Matrix (Fin 2) (Fin 2) ℤ := !![A, B; B, C]
  ∃ U : Matrix.SpecialLinearGroup (Fin 2) ℤ,
    let G_new := (U : Matrix (Fin 2) (Fin 2) ℤ).transpose * G * (U : Matrix (Fin 2) (Fin 2) ℤ)
    G_new 0 1 = 0 ∧ G_new 1 0 = 0 := by
  sorry





theorem theorem_365278_problem
  {R : Type*} [CommRing R]
  {V : Type*} [AddCommGroup V] [Module R V]
  (T : Module.End R V)
  (P Q : Polynomial R) :
  (Polynomial.aeval T P) * (Polynomial.aeval T Q) = (Polynomial.aeval T Q) * (Polynomial.aeval T P) := by
  sorry

theorem theorem_364869_problem
  {F : Type*} [Field F]
  {V W : Type*}
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]
  (T : V →ₗ[F] W) :
  (LinearMap.range T).dualAnnihilator = LinearMap.ker (LinearMap.dualMap T) := by
  sorry



theorem theorem_365617_problem (n p q : ℕ)
  (rx : Matrix (Fin n) (Fin p) ℝ)
  (v : Matrix (Fin n) (Fin q) ℝ)
  (hn : 1 < n)
  -- Assumption from solution: Columns are mean-centered
  (h_rx_centered : ∀ j, ∑ i, rx i j = 0)
  (h_v_centered : ∀ j, ∑ i, v i j = 0)
  -- Definition of Covariance Matrix C
  (C : Matrix (Fin p) (Fin q) ℝ)
  (hC : ∀ i j, C i j = (1 / ((n : ℝ) - 1)) * ∑ k, (rx k i - (1 / (n : ℝ)) * ∑ l, rx l i) * (v k j - (1 / (n : ℝ)) * ∑ l, v l j)) :
  C = (1 / ((n : ℝ) - 1)) • (rx.transpose * v) := by
  sorry

theorem theorem_364514_problem (d1 d2 p1 p2 : ℝ × ℝ) :
  let l : ℝ × ℝ := (d1.2, -d1.1)
  let r : ℝ × ℝ := (-d2.2, d2.1)
  let dot (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2
  let p (t : ℝ) : ℝ × ℝ := ((1 - t) * p1.1 + t * p2.1, (1 - t) * p1.2 + t * p2.2)
  let tl := dot l p1 / (dot l p1 - dot l p2)
  let tr := dot r p1 / (dot r p1 - dot r p2)
  (dot l p1 - dot l p2 ≠ 0) →
  (dot r p1 - dot r p2 ≠ 0) →
  dot l (p tl) = 0 ∧ dot r (p tr) = 0 := by
  sorry





theorem theorem_365477_problem
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (Theta : Set E)
  (c : E → F)
  (L : E → ℝ)
  (theta_mle : E)
  (h_theta_in : theta_mle ∈ Theta)
  (h_c_cont : ContinuousOn c Theta)
  (h_interior : c theta_mle ∈ interior (c '' Theta))
  (h_conc : StrictConcaveOn ℝ Theta L)
  (h_mle : ∀ θ ∈ Theta, L θ ≤ L theta_mle) :
  ∀ θ' ∈ Theta, (∀ θ ∈ Theta, L θ ≤ L θ') → θ' = theta_mle := by
  sorry

theorem theorem_365205_problem
  {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [TopologicalRing 𝕜]
  {X Y : Type*}
  [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [TopologicalAddGroup X] [ContinuousSMul 𝕜 X]
  [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y] [TopologicalAddGroup Y] [ContinuousSMul 𝕜 Y]
  (T : X →L[𝕜] Y)
  (h_surj : Function.Surjective T) :
  IsOpenMap T := by
  sorry



theorem theorem_365692_problem
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (c : Fin n → ℝ)
  (b b' : Fin m → ℝ)
  (basis : Fin m → Fin n)
  (B : Matrix (Fin m) (Fin m) ℝ)
  (hB_def : B = A.submatrix id basis)
  (hB_inv : Invertible B)
  -- Condition: B is an optimal basis for the problem min c^Tx s.t. Ax=b, x ≥ 0
  -- 1. Primal Feasibility: x_B = B⁻¹b ≥ 0
  (h_primal : 0 ≤ Matrix.mulVec (⅟B) b)
  -- 2. Dual Feasibility: πA ≤ c, where π = c_B * B⁻¹
  (h_dual : Matrix.vecMul (Matrix.vecMul (c ∘ basis) (⅟B)) A ≤ c) :
  -- Conclusion: B is dual feasible for the modified problem min c^Tx s.t. Ax=b', x ≥ 0
  -- The condition for dual feasibility is the same: πA ≤ c
  Matrix.vecMul (Matrix.vecMul (c ∘ basis) (⅟B)) A ≤ c := by
  sorry





theorem theorem_366032_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (v : Fin n → (Fin n → ℝ))
  -- Condition: A is an upper triangular matrix
  (hA_tri : ∀ i j : Fin n, j < i → A i j = 0)
  -- Condition: v_i are eigenvectors
  (h_eigen : ∀ i, ∃ μ : ℝ, Matrix.toLin' A (v i) = μ • v i)
  -- Condition: v_i span the whole space (implied by Vn = R^n)
  (h_span : Submodule.span ℝ (Set.range v) = ⊤)
  -- Definition: V_j is the span of the first j vectors
  (V : ℕ → Submodule ℝ (Fin n → ℝ))
  (hV : ∀ j, V j = Submodule.span ℝ (v '' {i | ↑i < j})) :
  -- Conclusion: A(V_j) ⊆ V_j
  ∀ j, j ≤ n → Submodule.map (Matrix.toLin' A) (V j) ≤ V j := by
  sorry

theorem theorem_366157_problem
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  (Y : Submodule ℝ Z)
  (hY : IsClosed (Y : Set Z))
  (v : Z)
  (hv : v ∉ Y) :
  0 < Metric.infDist v Y := by
  sorry

theorem theorem_365853_problem {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
  Polynomial.aeval A (Matrix.charpoly A) = 0 := by
  sorry

theorem theorem_366274_problem (f : ℂ → ℂ)
  (hf : Differentiable ℝ f)
  (h_cr1 : ∀ z : ℂ, (fderiv ℝ f z 1).re = (fderiv ℝ f z Complex.I).im)
  (h_cr2 : ∀ z : ℂ, (fderiv ℝ f z Complex.I).re = -(fderiv ℝ f z 1).im) :
  ∀ z : ℂ, (1 : ℂ) / 2 * (fderiv ℝ (fun w ↦ star (f w)) z 1 - Complex.I * fderiv ℝ (fun w ↦ star (f w)) z Complex.I) = 0 := by
  sorry

theorem theorem_366346_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (h : (Matrix.charpoly A).rootMultiplicity 0 = n) :
  A ^ n = 0 := by
  sorry

theorem theorem_366183_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : ℕ}
  (E : Basis (Fin n) K V)
  (B : Basis (Fin n) K V)
  (T : V →ₗ[K] V) :
  LinearMap.toMatrix E E T =
    (LinearMap.toMatrix B E LinearMap.id) *
    (LinearMap.toMatrix B B T) *
    (LinearMap.toMatrix E B LinearMap.id) := by
  sorry

theorem theorem_366486_problem (n : ℕ) [NeZero n]
  (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
  (h1 : ∀ i j : Fin n, i ≠ j → f (Matrix.stdBasisMatrix i j 1) = 0)
  (h2 : ∀ i : Fin n, f (Matrix.stdBasisMatrix i i 1) = f (Matrix.stdBasisMatrix 0 0 1)) :
  ∀ C : Matrix (Fin n) (Fin n) ℝ, f C = f (Matrix.stdBasisMatrix 0 0 1) * Matrix.trace C := by
  sorry

theorem theorem_366391_problem
  (F : Type*) [Field F]
  (V : Type*) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (G : Type*) [Group G] [MulAction G V]
  (v : V) (hv : v ≠ 0) :
  MulAction.orbit G v = {x | ∃ g : G, g • v = x} := by
  sorry

theorem theorem_366591_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (h1 : A * A.transpose = 1)
  (h2 : A.IsSymm)
  (h3 : A.PosDef) :
  A = 1 := by
  sorry















theorem theorem_366796_problem (p : ℕ) [Fact p.Prime]
  (V W : Type*)
  [NormedAddCommGroup V] [NormedSpace ℚ_[p] V]
  [NormedAddCommGroup W] [NormedSpace ℚ_[p] W]
  (hV : FiniteDimensional ℚ_[p] V)
  (hW : FiniteDimensional ℚ_[p] W)
  (f : V →ₗ[ℚ_[p]] W) :
  Continuous f := by
  sorry

theorem theorem_366526_problem
  {I V : Type*}
  [NormedAddCommGroup V]
  [InnerProductSpace ℂ V]
  [Fintype I]
  (u : I → V)
  (hu : Orthonormal ℂ u)
  (c : I → ℂ)
  (x : V)
  (hx : x = ∑ i, c i • u i) :
  ‖x‖^2 = ∑ i, Complex.abs (c i) ^ 2 := by
  sorry





theorem theorem_367046_problem
  (n : ℕ)
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (hK_conv : Convex ℝ K)
  (hK_cp : IsCompact K)
  (L : ℝ)
  (hL : L > 0)
  (h_iso : ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 → ∫ x in K, (inner x u)^2 = L * ‖u‖^2) :
  ∀ v : EuclideanSpace ℝ (Fin n), ∫ x in K, (inner x v)^2 = L * ‖v‖^2 := by
  sorry

theorem theorem_366839_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E →ₗ[ℝ] E)
  (h_orth : ∀ u v : E, ⟪u, v⟫_ℝ = 0 → ⟪f u, f v⟫_ℝ = 0) :
  ∃ (c : ℝ) (σ : E ≃ₗᵢ[ℝ] E), f = c • σ.toLinearMap := by
  sorry

theorem theorem_366794_problem (f : ℂ → ℂ) (c : ℝ)
  (h_holo : DifferentiableOn ℂ f {z | z ≠ 0})
  (hc : c > 0)
  (h_bound : ∀ z, z ≠ 0 → Complex.abs (f z) ≤ 2 * c * Real.log (Complex.abs z))
  (h_roots : ∀ z, Complex.abs z = 1 → f z = 0) :
  ∀ z, z ≠ 0 → f z = 0 := by
  sorry











theorem theorem_367561_problem
  (n k : ℕ)
  (X_1 : Matrix (Fin n) (Fin k) ℝ)
  (x_k : Matrix (Fin n) (Fin 1) ℝ)
  (h_inv_X1 : Invertible (X_1.transpose * X_1))
  (X : Matrix (Fin n) (Fin (k + 1)) ℝ := Matrix.of (fun i j => Fin.addCases (X_1 i) (x_k i) j))
  (h_inv_X : Invertible (X.transpose * X))
  (M_1 : Matrix (Fin n) (Fin n) ℝ := (1 : Matrix (Fin n) (Fin n) ℝ) - X_1 * ⅟(X_1.transpose * X_1) * X_1.transpose) :
  (⅟(X.transpose * X)) (Fin.last k) (Fin.last k) = 1 / (x_k.transpose * M_1 * x_k) 0 0 := by
  sorry





theorem theorem_368055_problem 
  {n : Type*} [DecidableEq n] [Fintype n] 
  {R : Type*} [CommRing R] 
  (T P T' : Matrix n n R) 
  [Invertible P] 
  (h_eq : T' = P * T * ⅟P) 
  (k : ℕ) (hk : 0 < k) : 
  T' ^ k = P * (T ^ k) * ⅟P := by
  sorry







theorem theorem_368257_problem
  (h : ℝ → ℂ)
  (s : ℂ)
  (x : ℝ → ℂ)
  (y : ℝ → ℂ)
  (H : ℂ)
  (hx : ∀ t, x t = Complex.exp (s * ↑t))
  (hH : H = ∫ τ, h τ * Complex.exp (-s * ↑τ))
  (hy : ∀ t, y t = ∫ τ, h τ * x (t - τ)) :
  ∀ t, y t = H * x t := by
  sorry



theorem theorem_367868_problem (n : ℕ) (A B C D : Matrix (Fin n) (Fin n) ℝ)
  (hA_symm : A.IsSymm) (hB_symm : B.IsSymm)
  (hC_symm : C.IsSymm) (hD_symm : D.IsSymm)
  (hA_psd : A.PosSemidef) (hB_psd : B.PosSemidef)
  (hC_psd : C.PosSemidef) (hD_psd : D.PosSemidef) :
  (Matrix.hadamard (A - B) C + Matrix.hadamard B (C - D) + Matrix.hadamard B D).PosSemidef := by
  sorry

theorem theorem_368322_problem
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (K : E →L[ℝ] F)
  (f : F)
  (x : E)
  (α : ℝ) :
  ‖(f, (0 : E)) - (K x, α • x)‖^2 = ‖K x - f‖^2 + α^2 * ‖x‖^2 := by
  sorry













