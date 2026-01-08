import Mathlib
import Mathlib.Tactic

theorem theorem_411136_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (a : H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
  (h_bounded : ∃ M > 0, ∀ u v, |a u v| ≤ M * ‖u‖ * ‖v‖)
  (h_symm : ∀ u v, a u v = a v u)
  (h_coercive : ∃ α > 0, ∀ u, α * ‖u‖^2 ≤ a u u)
  (f : H →L[ℝ] ℝ) :
  ∃! u, ∀ v, a u v = f v := by
  sorry





theorem theorem_410940_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  {W : Type*} [AddCommGroup W] [Module F W]
  {n : Type*} [Fintype n] [DecidableEq n]
  {m : Type*} [Fintype m] [DecidableEq m]
  (β : Basis n F V)
  (γ : Basis m F W)
  (T : V →ₗ[F] W)
  (u : V) :
  Matrix.mulVec (LinearMap.toMatrix β γ T) (β.repr u) = γ.repr (T u) := by
  sorry







theorem theorem_411219_problem
  {R : Type*} [Ring R]
  {M : Type*} [AddCommGroup M] [Module R M]
  (N P : Submodule R M)
  (h : IsCompl N P) :
  ¬ ∃ N' : Submodule R M, N' < N ∧ IsCompl N' P := by
  sorry











theorem theorem_411952_problem
  (ι₁ ι₂ : Type*)
  [Fintype ι₁] [Fintype ι₂]
  (w : ι₁ → ι₂ → ℝ)
  (f : ℝ → ℝ)
  (h : ∀ M, f M = ∑ i, ∑ j, w i j * M) :
  ConvexOn ℝ Set.univ f := by
  sorry

theorem theorem_411527_problem
  (m : ℕ)
  (F : ℝ × (Fin m → ℝ) → (Fin m → ℝ))
  (n_vec : ℝ × (Fin m → ℝ))
  (h_diff : ContDiff ℝ 1 F)
  (h_root : F n_vec = 0)
  (h_rank : IsUnit (fderiv ℝ (fun y => F (n_vec.1, y)) n_vec.2)) :
  ∃ U : Set ℝ, ∃ V : Set (Fin m → ℝ),
    IsOpen U ∧ IsOpen V ∧ n_vec.1 ∈ U ∧ n_vec.2 ∈ V ∧
    ∃ φ : ℝ → (Fin m → ℝ),
      ContDiffOn ℝ 1 φ U ∧
      (∀ x ∈ U, φ x ∈ V) ∧
      (∀ x ∈ U, F (x, φ x) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ V, F (x, y) = 0 → y = φ x) := by
  sorry

theorem theorem_411360_problem (A B : Matrix (Fin 2) (Fin 2) ℝ)
  (hA : A = 1)
  (hB : B = A + !![1, 1; 1, 1]) :
  B.det = 3 := by
  sorry



theorem theorem_411560_problem
  (K : Type*) [Field K]
  (n m : ℕ)
  (V : Fin n → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  (W : Fin m → Type*) [∀ j, AddCommGroup (W j)] [∀ j, Module K (W j)]
  (J : Fin n → Type*) [∀ i, Fintype (J i)]
  (I : Fin m → Type*) [∀ j, Fintype (I j)]
  (hV : ∀ i, Basis (J i) K (V i))
  (hW : ∀ j, Basis (I j) K (W j)) :
  Nonempty (PiTensorProduct K V ≃ₗ[K] PiTensorProduct K W) ↔
  Fintype.card (Π i, J i) = Fintype.card (Π j, I j) := by
  sorry



theorem theorem_411770_problem
  {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  (u u_sqrt p : H →L[𝕜] H)
  (h_sqrt : u_sqrt * u_sqrt = u)
  (h_range : LinearMap.range u_sqrt = LinearMap.range u)
  (h_p : ∀ x ∈ LinearMap.range u_sqrt, p x = x) :
  u_sqrt * p * u_sqrt = u := by
  sorry



theorem theorem_411720_problem
  (A C R L : Matrix (Fin 3) (Fin 3) ℤ)
  (hA : IsUnit A) (hC : IsUnit C)
  (hR : IsUnit R) (hL : IsUnit L)
  (h_eq : C = L * A * R) :
  Nonempty (( (Fin 3 → ℤ) ⧸ LinearMap.range (Matrix.toLin' A) ) ≃+
            ( (Fin 3 → ℤ) ⧸ LinearMap.range (Matrix.toLin' C) )) := by
  sorry











theorem theorem_412188_problem
  (n k₁ k₂ : ℕ)
  (X₁ : Matrix (Fin n) (Fin k₁) ℝ)
  (X₂ : Matrix (Fin n) (Fin k₂) ℝ)
  (h_centered_1 : ∀ j, (∑ i, X₁ i j) / (n : ℝ) = 0)
  (h_centered_2 : ∀ j, (∑ i, X₂ i j) / (n : ℝ) = 0)
  (h_orth : ∀ j₁ j₂, ∑ i, (X₁ i j₁) * (X₂ i j₂) = 0) :
  ∀ j₁ j₂,
    let col₁ := fun i => X₁ i j₁
    let col₂ := fun i => X₂ i j₂
    let mean₁ := (∑ i, col₁ i) / (n : ℝ)
    let mean₂ := (∑ i, col₂ i) / (n : ℝ)
    let cov := (∑ i, (col₁ i - mean₁) * (col₂ i - mean₂)) / (n : ℝ)
    let var₁ := (∑ i, (col₁ i - mean₁) ^ 2) / (n : ℝ)
    let var₂ := (∑ i, (col₂ i - mean₂) ^ 2) / (n : ℝ)
    let rho := cov / (Real.sqrt var₁ * Real.sqrt var₂)
    rho = 0 := by
  sorry





theorem theorem_412808_problem
  (x y : EuclideanSpace ℝ (Fin 2))
  (g : ℝ → ℝ)
  (h_g : ∀ t, g t = ‖t • y + (1 - t) • x‖ ^ 2)
  (t : ℝ) :
  deriv g t = 2 * inner (t • y + (1 - t) • x) (y - x) := by
  sorry











theorem theorem_413002_problem
  (V : Type*) [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (A : Matrix V V ℕ)
  (hA : A = G.adjMatrix ℕ)
  (n : ℕ) (hn : n ≥ 1)
  (i j : V) :
  Fintype.card { w : G.Walk i j | w.length = n } = (A ^ n) i j := by
  sorry



theorem theorem_412966_problem :
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (N : Type) (_ : AddCommGroup N) (_ : Module A N),
    ¬ Nonempty (TensorProduct A I N ≃ₗ[A] (I • ⊤ : Submodule A N)) := by
  sorry

theorem theorem_412864_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (h_irr : ∀ i j : Fin n, Relation.ReflTransGen (fun a b => A a b ≠ 0) i j)
  (h_nil : IsNilpotent A) :
  ∀ P : Equiv.Perm (Fin n), ¬ (∀ i j : Fin n, j < i → A (P i) (P j) = 0) := by
  sorry

theorem theorem_412774_problem (a b c : ℝ) (f g : ℝ → ℝ)
  (hab : a < b) (hbc : b < c)
  (h_dep_ab : ∃ c1 c2 : ℝ, (c1 ≠ 0 ∨ c2 ≠ 0) ∧ ∀ x ∈ Set.Ioc a b, c1 * f x + c2 * g x = 0)
  (h_dep_bc : ∃ d1 d2 : ℝ, (d1 ≠ 0 ∨ d2 ≠ 0) ∧ ∀ x ∈ Set.Ico b c, d1 * f x + d2 * g x = 0)
  (hfb : f b ≠ 0) (hgb : g b ≠ 0) :
  ∃ k1 k2 : ℝ, (k1 ≠ 0 ∨ k2 ≠ 0) ∧ ∀ x ∈ Set.Ioo a c, k1 * f x + k2 * g x = 0 := by
  sorry







theorem theorem_412939_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (H : E → ℝ) (y : E) (G : ℝ)
  (hH : StrictConvexOn ℝ Set.univ H)
  (hG : IsGreatest (Set.range (fun x => inner x y - H x)) G) :
  ∃! x, inner x y - H x = G := by
  sorry



theorem theorem_413406_problem {n : Type*} [Fintype n] [DecidableEq n]
  (A : Matrix n n ℂ)
  (h1 : A.IsHermitian)
  (h2 : A ^ 2 = 0) :
  A = 0 := by
  sorry

theorem theorem_413751_problem
  (n : ℕ)
  (R : Type*) [CommRing R]
  (A B C B' : Matrix (Fin n) (Fin n) R)
  (h1 : B * C = A)
  (h2 : A = C * B')
  (hC : IsUnit C) :
  B' = C⁻¹ * B * C := by
  sorry











theorem theorem_413713_problem (n : ℕ) (R : Type*) [CommRing R]
  (A M : Matrix (Fin n) (Fin n) R)
  (i l : Fin n) :
  (M * A * M.transpose) i l = ∑ j, ∑ k, M i j * A j k * M l k := by
  sorry

theorem theorem_413697_problem :
  ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin m) (Fin m) ℝ) (x : Fin n → ℝ),
  ∀ (c : Fin n → ℝ), A.mulVec c ≠ B.mulVec (A.mulVec x) := by
  sorry

theorem theorem_413944_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (F : Set (X →L[ℝ] ℝ))
  (n : ℕ) :
  IsClosed {x : X | ∀ T ∈ F, ‖T x‖ ≤ (n : ℝ)} := by
  sorry



theorem theorem_414105_problem (A D Z : ℝ) 
  (hZ : Z = 0 ∨ Z = 1) 
  (h1 : A ≥ D * Z) 
  (h2 : Z = 1) : 
  A ≥ D := by
  sorry



theorem theorem_414255_problem
  {R : Type*} [Ring R]
  {V : Type*} [AddCommGroup V] [Module R V]
  {W : Type*} [AddCommGroup W] [Module R W]
  (x : V →ₗ[R] W)
  (v₁ v₂ : V)
  (η₀ η₂ : W)
  (h₁ : x v₁ = η₀)
  (h₂ : x v₂ = η₂) :
  x (v₁ - v₂) = η₀ - η₂ := by
  sorry





theorem theorem_414280_problem (n q : ℕ) (hn : 0 < n) (hq : 1 < q)
  (E : ℕ → ℝ)
  (h1 : E n = 0)
  (h2 : ∀ k, k < n →
    let p : ℝ := ((q : ℝ) ^ n - (q : ℝ) ^ k) / (q : ℝ) ^ n
    E k = 1 + p * E (k + 1) + (1 - p) * E k) :
  E 0 = ∑ k in Finset.range n, 1 / (1 - (q : ℝ) ^ ((k : ℤ) - (n : ℤ))) := by
  sorry







theorem theorem_414537_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (seq : ℕ → V) (f : V)
  (h : Filter.Tendsto (fun n => ‖seq n - f‖) Filter.atTop (nhds 0)) :
  Filter.Tendsto (fun n => ‖seq n‖) Filter.atTop (nhds ‖f‖) := by
  sorry



theorem theorem_414570_problem (U : Set ℂ) (hU : U = Metric.ball 0 1 \ {0})
  (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
  (h_abs : ∀ z ∈ U, Complex.abs (f z / z) = 1) :
  ∃ α : ℂ, Complex.abs α = 1 ∧ ∀ z ∈ U, f z = α * z := by
  sorry

theorem theorem_414310_problem 
  {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]
  [DecidableEq n] [DecidableEq m] [DecidableEq k]
  (t : ℕ)
  -- Matrices
  (T : Matrix n n ℝ) (R : Matrix n k ℝ) (F : Matrix m n ℝ)
  -- Time-dependent vectors
  (θ : ℕ → Matrix n (Fin 1) ℝ)
  (Y : ℕ → Matrix m (Fin 1) ℝ)
  (ν : ℕ → Matrix k (Fin 1) ℝ)
  (ε : ℕ → Matrix m (Fin 1) ℝ)
  -- Estimators
  (hat_theta : ℕ → Matrix n (Fin 1) ℝ)
  (Y_star : ℕ → Matrix m (Fin 1) ℝ)
  -- State Space Conditions
  (h_state : ∀ t, θ t = T * θ (t-1) + R * ν t)
  (h_obs : ∀ t, Y t = F * θ t + ε t)
  -- Abstract Estimator Operators (Conditional Expectation E[·|Data])
  (E_state : Matrix n (Fin 1) ℝ → Matrix n (Fin 1) ℝ)
  (E_obs : Matrix m (Fin 1) ℝ → Matrix m (Fin 1) ℝ)
  -- Estimator Definitions
  (h_def_hat : hat_theta t = E_state (θ t))
  (h_def_star : Y_star t = E_obs (Y t))
  -- Properties of the Estimator (Linearity and Noise)
  (h_lin_add : ∀ (A B : Matrix m (Fin 1) ℝ), E_obs (A + B) = E_obs A + E_obs B)
  (h_lin_hom : ∀ (A : Matrix n (Fin 1) ℝ), E_obs (F * A) = F * E_state A)
  (h_noise : E_obs (ε t) = 0) :
  Y_star t = F * hat_theta t := by
  sorry



theorem theorem_414833_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V₁ : Type*} [NormedAddCommGroup V₁] [NormedSpace 𝕜 V₁]
  {V₂ : Type*} [NormedAddCommGroup V₂] [NormedSpace 𝕜 V₂]
  (h1 : Nontrivial V₁)
  (h2 : CompleteSpace (V₁ →L[𝕜] V₂)) :
  CompleteSpace V₂ := by
  sorry



theorem theorem_414745_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  (B : Set V)
  (h_indep : LinearIndependent F (fun (b : B) ↦ (b : V)))
  (h_span : Submodule.span F B = ⊤) :
  ∃! φ : (B →₀ F) ≃ₗ[F] V, ∀ (f : B →₀ F), φ f = Finsupp.sum f (fun b a ↦ a • (b : V)) := by
  sorry



theorem theorem_415470_problem (n : ℕ) (A X : Matrix (Fin n) (Fin n) ℝ)
  (hA : A.PosDef) (hX : IsUnit X) :
  Matrix.det (X.transpose * A * X) = Matrix.det A * (Matrix.det X) ^ 2 := by
  sorry







theorem theorem_415433_problem
  (n m : ℕ)
  (q : Fin m → Matrix (Fin n) (Fin 1) ℂ)
  (h_ortho : ∀ i j, (q i).conjTranspose * (q j) = if i = j then (1 : Matrix (Fin 1) (Fin 1) ℂ) else 0)
  (Q : Matrix (Fin n) (Fin n) ℂ)
  (hQ : Q = ∑ k, q k * (q k).conjTranspose)
  (x : Matrix (Fin n) (Fin 1) ℂ)
  (x_parallel x_perp x_reflected : Matrix (Fin n) (Fin 1) ℂ)
  (h_x_parallel : x_parallel = Q * x)
  (h_x_perp : x_perp = x - Q * x)
  (h_x_reflected : x_reflected = x_parallel - x_perp) :
  x_reflected = 2 • (Q * x) - x := by
  sorry

theorem theorem_415163_problem (a : ℕ → ℝ)
  (h : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, a (φ k) ≥ 1) :
  Filter.limsup (fun n ↦ (a n : EReal)) Filter.atTop ≥ 1 := by
  sorry













theorem theorem_415587_problem
  (u : ℝ × ℝ → ℝ)
  (s : Set (ℝ × ℝ))
  (hs : IsOpen s)
  (hu : ContDiffOn ℝ ⊤ u s)
  (h_pde : ∀ x y, (x, y) ∈ s → x * deriv (fun t ↦ u (t, y)) x = y * deriv (fun t ↦ u (x, t)) y) :
  ∀ p ∈ s, ∃ U, IsOpen U ∧ p ∈ U ∧ U ⊆ s ∧
    ∃ v : ℝ → ℝ, ContDiff ℝ ⊤ v ∧ ∀ x y, (x, y) ∈ U → u (x, y) = v (x * y) := by
  sorry



theorem theorem_415312_problem
  (n p : ℕ)
  (Z : Matrix (Fin n) (Fin p) ℝ)
  (σ : ℝ)
  [Invertible (Z.transpose * Z)] :
  let CovU : Matrix (Fin n) (Fin n) ℝ := σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)
  let OLS_transform := (Z.transpose * Z)⁻¹ * Z.transpose
  let CovHatBeta := OLS_transform * CovU * OLS_transform.transpose
  CovHatBeta = σ ^ 2 • (Z.transpose * Z)⁻¹ := by
  sorry



theorem theorem_415483_problem
  (n p : ℕ)
  (RSS : ℝ)
  (Sigma : Fin p → Fin p → ℝ)
  (j : Fin p)
  (h_n_gt_p : n > p)
  (nu : ℝ)
  (h_nu : nu = (n : ℝ) - (p : ℝ))
  (se_j : ℝ)
  (h_se_def : se_j = Real.sqrt ((RSS / nu) * Sigma j j)) :
  se_j = Real.sqrt ((RSS / ((n : ℝ) - (p : ℝ))) * Sigma j j) := by
  sorry



theorem theorem_415854_problem 
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  (d : ℕ → X)
  (d_dual : ℕ → X →L[ℝ] ℝ)
  (h_sphere : ∀ n, ‖d n‖ = 1)
  (h_dense : ∀ x : X, ‖x‖ = 1 → ∀ ε > 0, ∃ n, ‖x - d n‖ < ε)
  (h_dual_norm : ∀ n, ‖d_dual n‖ = 1)
  (h_dual_eval : ∀ n, d_dual n (d n) = 1) :
  ¬ ∃ x : X, ‖x‖ = 1 ∧ (∀ n, d_dual n x = 0) ∧ (∀ n, d_dual n (x - d n) = -1) := by
  sorry







theorem theorem_415703_problem (A : Matrix (Fin 2) (Fin 2) ℂ)
  (T : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
  (hT : ∀ X, T X = A * X + X * A) :
  LinearMap.det T = 4 * A.det * A.trace ^ 2 := by
  sorry

theorem theorem_415829_problem
  {n r : ℕ}
  (U : Set (Fin n → ℝ))
  (φ : (Fin n → ℝ) → (Fin r → ℝ))
  (b : Fin r → (Fin r → ℝ) → ℝ)
  (x : Fin n → ℝ)
  (v : Fin n → ℝ)
  (hU : IsOpen U)
  (hφ : ContDiffOn ℝ ⊤ φ U)
  (hx : x ∈ U) :
  (∑ R : Fin r, b R (φ x) * (fderiv ℝ φ x v R)) =
  ∑ R : Fin r, ∑ j : Fin n, b R (φ x) * (fderiv ℝ φ x (Pi.single j 1) R) * (v j) := by
  sorry

theorem theorem_415448_problem
  {X : Type*} [AddCommGroup X] [Module ℝ X]
  (n1 n2 : X → ℝ)
  (h1_def : ∀ x : X, n1 x = 0 ↔ x = 0)
  (h1_hom : ∀ (c : ℝ) (x : X), n1 (c • x) = |c| * n1 x)
  (h1_tri : ∀ x y : X, n1 (x + y) ≤ n1 x + n1 y)
  (h2_def : ∀ x : X, n2 x = 0 ↔ x = 0)
  (h2_hom : ∀ (c : ℝ) (x : X), n2 (c • x) = |c| * n2 x)
  (h2_tri : ∀ x y : X, n2 (x + y) ≤ n2 x + n2 y)
  (h_imp : ∀ A B : X, n1 A ≤ n1 B → n2 A ≤ n2 B) :
  ∃ C : ℝ, C > 0 ∧ ∀ A : X, n1 A = C * n2 A := by
  sorry

