import Mathlib
import Mathlib.Tactic

theorem theorem_214779_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  (L : V →L[𝕜] W)
  (c : V) :
  fderiv 𝕜 L c = L := by
  sorry





theorem theorem_214723_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
  (h : Commute A B) :
  spectralRadius ℂ (A * B) ≤ spectralRadius ℂ A * spectralRadius ℂ B := by
  sorry









theorem theorem_214263_problem (a b c : Fin 3 → ℝ) :
  crossProduct a (crossProduct b c) = (Matrix.dotProduct a c) • b - (Matrix.dotProduct a b) • c := by
  sorry

theorem theorem_214459_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (S : Set V) (hS : S.Nonempty)
  (f : V → F)
  (h1 : ∀ x ∈ S, (1 : F) • x ∈ S → f ((1 : F) • x) = (1 : F) * f x)
  (h_neg1 : ∀ x ∈ S, (-1 : F) • x ∈ S → f ((-1 : F) • x) = (-1 : F) * f x) :
  ∀ a : F, a ≠ 0 → ∀ x ∈ S, a • x ∈ S → f (a • x) = a * f x := by
  sorry













theorem theorem_215195_problem
  (n : ℕ)
  (F K : Type*) [Field F] [Field K]
  [Algebra F K] [FiniteDimensional F K]
  (A : Matrix (Fin n) (Fin n) F) :
  minpoly K (Matrix.map A (algebraMap F K)) = (minpoly F A).map (algebraMap F K) := by
  sorry

theorem theorem_215229_problem
  (m n : ℕ)
  (X : Matrix (Fin m) (Fin n) ℝ)
  (y : Matrix (Fin m) (Fin 1) ℝ)
  (β : Matrix (Fin n) (Fin 1) ℝ)
  (h_invertible : IsUnit (X.transpose * X).det)
  (h_min : ∀ b : Matrix (Fin n) (Fin 1) ℝ,
    ((y - X * β).transpose * (y - X * β)) 0 0 ≤ ((y - X * b).transpose * (y - X * b)) 0 0) :
  β = (X.transpose * X)⁻¹ * X.transpose * y := by
  sorry

theorem theorem_214897_problem
  (xi0 xi1 xi2 xi3 : ℝ)
  (p_dot : Fin 3 → ℝ)
  (xi_dot : Fin 4 → ℝ)
  (H : Matrix (Fin 3) (Fin 4) ℝ)
  (hH : H = !![ -xi1, xi0, xi3, -xi2;
                -xi2, -xi3, xi0, xi1;
                -xi3, xi2, -xi1, xi0 ])
  (E : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 4) ℝ)
  (hE : E = Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) ℝ) (0 : Matrix (Fin 3) (Fin 4) ℝ)
                              (0 : Matrix (Fin 3) (Fin 3) ℝ) ((-2 : ℝ) • H))
  (omega : Fin 3 → ℝ)
  (h_omega : omega = (-2 : ℝ) • (H.mulVec xi_dot)) :
  E.mulVec (Sum.elim p_dot xi_dot) = Sum.elim p_dot omega := by
  sorry









theorem theorem_215526_problem
  {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
  {n : ℕ}
  (e : Basis (Fin n) F V)
  (T : V →ₗ[F] W)
  (x_coeffs : Fin n → F)
  (x : V)
  (hx : x = ∑ i, x_coeffs i • e i) :
  T x = ∑ i, x_coeffs i • T (e i) := by
  sorry





theorem theorem_216301_problem :
  ∃ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ),
    v ≠ 0 ∧ Matrix.mulVec (A * B) v = v ∧ A * B ≠ 1 := by
  sorry













theorem theorem_216005_problem (A B C D x y z a b c : ℝ)
  (h_plane : A * x + B * y + C * z = D)
  (hz : z ≠ 0)
  (ha : a = x / z)
  (hb : b = y / z)
  (hc : c = z) :
  A * a + B * b - D / c = -C := by
  sorry













theorem theorem_216482_problem
  (k n : ℕ)
  (hkn : k ≤ n)
  (U : Matrix (Fin k) (Fin k) ℝ)
  (D : Matrix (Fin k) (Fin n) ℝ)
  (V : Matrix (Fin n) (Fin n) ℝ)
  (A : Matrix (Fin k) (Fin n) ℝ)
  (hU : U.det ≠ 0)
  (hV : V.det ≠ 0)
  (hD_diag : ∀ (i : Fin k) (j : Fin n), (i : ℕ) ≠ (j : ℕ) → D i j = 0)
  (hD_pos : ∀ (i : Fin k), D i (Fin.castLE hkn i) > 0)
  (hA : A = U * D * V.transpose) :
  (A * A.transpose).det ≠ 0 := by
  sorry









theorem theorem_216687_problem
  (f₁ f₂ : ℝ → ℝ)
  (T₁ T₂ : ℝ)
  (h_cont₁ : Continuous f₁)
  (h_cont₂ : Continuous f₂)
  (h_nconst₁ : ¬ ∀ x y, f₁ x = f₁ y)
  (h_nconst₂ : ¬ ∀ x y, f₂ x = f₂ y)
  (h_T₁_pos : T₁ > 0)
  (h_T₂_pos : T₂ > 0)
  (h_per₁ : Function.Periodic f₁ T₁)
  (h_per₂ : Function.Periodic f₂ T₂)
  (h_lin_indep : ∀ (q₁ q₂ : ℚ), (q₁ : ℝ) * T₁ + (q₂ : ℝ) * T₂ = 0 → q₁ = 0 ∧ q₂ = 0) :
  ¬ ∃ T > 0, Function.Periodic (f₁ + f₂) T := by
  sorry



theorem theorem_216986_problem
  (T : ℝ → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)))
  (h0 : T 0 = 1)
  (ht : ∀ t > 0, T t = -1) :
  ¬ ContinuousAt T 0 := by
  sorry



theorem theorem_216405_problem
  (m n k : ℕ)
  (g : (Fin m → ℝ) → (Fin n → ℝ))
  (u₀ : Fin m → ℝ)
  (s : Set (Fin m → ℝ))
  (h_open : IsOpen s)
  (h_u₀ : u₀ ∈ s)
  (h_diff : DifferentiableOn ℝ g s)
  (h_rank : ∀ u ∈ s, FiniteDimensional.finrank ℝ (LinearMap.range (fderiv ℝ g u)) = k)
  (h_no_invert : ∀ u ∈ s, ∀ p : ℕ, k < p → 
    ∀ (M : Matrix (Fin p) (Fin p) ℝ), 
    (∃ (rows : Fin p → Fin n) (cols : Fin p → Fin m),
      Function.Injective rows ∧ Function.Injective cols ∧
      M = fun a b => fderiv ℝ g u (Pi.single (cols b) 1) (rows a)) → 
    ¬ IsUnit M.det) :
  ∀ u ∈ s, ∀ i : Fin m, ∀ j : Fin n, k ≤ i → k ≤ j → 
  fderiv ℝ g u (Pi.single i 1) j = 0 := by
  sorry

theorem theorem_216811_problem (a R t : ℝ) (hR : 0 < R) :
  Complex.abs (Complex.exp ((a : ℂ) * ((R : ℂ) + (t : ℂ) * Complex.I)) / 
  (1 + Complex.exp ((R : ℂ) + (t : ℂ) * Complex.I))) ≤ 
  Real.exp ((a - 1) * R) / (1 - Real.exp (-R)) := by
  sorry

theorem theorem_217122_problem
  {E D : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [AddCommGroup D] [Module ℝ D]
  (δ : ℝ → D)
  (h_scaling : ∀ (a x : ℝ), a ≠ 0 → δ (a * x) = (1 / |a|) • δ x)
  (ρ ρ' : ℝ) (e e' : E)
  (hρ : 0 < ρ) (hρ' : 0 < ρ') :
  δ (inner (ρ • e) (ρ' • e')) = (1 / (ρ * ρ')) • δ (inner e e') := by
  sorry

theorem theorem_217133_problem (n m : ℕ)
  (A : Set (Fin n → ℝ)) (hA : IsClosed A)
  (f : A → (Fin m → ℝ)) (hf : Continuous f) :
  Embedding (fun (x : A) ↦ (x.val, f x)) := by
  sorry









theorem theorem_217116_problem
  {K : Type*} [Field K]
  (n : ℕ)
  (T : Fin n → Fin n → Fin n → Fin n → K) :
  ∑ i : Fin n, ∑ j : Fin n, T i j i j = ∑ j : Fin n, ∑ i : Fin n, T i j i j := by
  sorry



theorem theorem_217130_problem
  {F V : Type*}
  [Field F]
  [AddCommGroup V]
  [Module F V]
  [FiniteDimensional F V]
  (W : Submodule F V) :
  FiniteDimensional.finrank F W ≤ FiniteDimensional.finrank F V := by
  sorry



theorem theorem_216999_problem
  (x : ℝ)
  (D : ℕ → ℝ)
  (hD1 : D 1 = x + 1)
  (hDn : ∀ n, n > 1 → D n = x * D (n - 1) + 1)
  (n : ℕ)
  (hn : n ≥ 1) :
  D n = ∑ i in Finset.range (n + 1), x ^ i := by
  sorry











theorem theorem_217979_problem
  {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (D : X ≃ₗᵢ[ℝ] Y)
  (y : ℕ → Y)
  (hy : CauchySeq y) :
  CauchySeq (fun n ↦ D.symm (y n)) := by
  sorry

theorem theorem_217996_problem (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ)
  (h_symm : S.IsSymm)
  (h_pos : S.PosDef) :
  ∃ P : Matrix (Fin n) (Fin n) ℝ, P.det ≠ 0 ∧ P.transpose * S * P = 1 := by
  sorry





theorem theorem_217861_problem {n m : ℕ}
  (A : Matrix (Fin n) (Fin n) ℝ)
  (B : Matrix (Fin n) (Fin m) ℝ)
  (C : Matrix (Fin m) (Fin m) ℝ)
  (M : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
  (hM : M = Matrix.fromBlocks A B B.transpose C)
  (hM_pd : M.PosDef) :
  A.PosDef := by
  sorry



theorem theorem_217868_problem
  (n d : ℕ)
  (X : Fin n → Fin d → ℝ)
  (x_star : Fin d → ℝ)
  (f : Matrix (Fin n) (Fin 1) ℝ) -- Observed output vector
  (K : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) -- Kernel function
  -- Definitions of the block covariance matrices derived from K
  (K_XX : Matrix (Fin n) (Fin n) ℝ)
  (hK_XX : K_XX = λ i j => K (X i) (X j))
  (K_X_star : Matrix (Fin n) (Fin 1) ℝ)
  (hK_X_star : K_X_star = λ i j => K (X i) x_star)
  (K_star_X : Matrix (Fin 1) (Fin n) ℝ)
  (hK_star_X : K_star_X = λ i j => K x_star (X j))
  (K_star_star : Matrix (Fin 1) (Fin 1) ℝ)
  (hK_star_star : K_star_star = λ i j => K x_star x_star)
  -- Assumption: The training data covariance matrix is invertible
  [Invertible K_XX]
  -- The predicted mean and variance formulas provided in the problem statement
  (mu_star : Matrix (Fin 1) (Fin 1) ℝ)
  (h_mu_star : mu_star = K_star_X * K_XX⁻¹ * f)
  (sigma_star_sq : Matrix (Fin 1) (Fin 1) ℝ)
  (h_sigma_star_sq : sigma_star_sq = K_star_star - K_star_X * K_XX⁻¹ * K_X_star)
  -- The standard algebraic definition of conditional moments (Schur complement)
  -- for a joint Gaussian with zero mean and block covariance.
  (schur_mean : Matrix (Fin 1) (Fin 1) ℝ := K_star_X * K_XX⁻¹ * f)
  (schur_var : Matrix (Fin 1) (Fin 1) ℝ := K_star_star - K_star_X * K_XX⁻¹ * K_X_star) :
  mu_star = schur_mean ∧ sigma_star_sq = schur_var := by
  sorry













theorem theorem_218521_problem
  (a b : ℝ) (h_ab : a < b)
  (f : ℝ → ℝ)
  (hf_cont : ContinuousOn f (Set.Icc a b))
  (h_orth : ∀ n : ℕ, ∫ x in a..b, f x * x ^ n = 0) :
  ∀ x ∈ Set.Icc a b, f x = 0 := by
  sorry





theorem theorem_218278_problem
  (V : Type*) [AddCommGroup V] [Module ℝ V]
  (φ₁ φ₂ φ₃ : V)
  (i : V ≃ₗ[ℝ] V)
  (h_indep : LinearIndependent ℝ ![φ₁, φ₂, φ₃])
  (h_span : Submodule.span ℝ (Set.range ![φ₁, φ₂, φ₃]) = ⊤) :
  LinearIndependent ℝ ![φ₁, φ₂ + φ₃, i.symm (φ₂ - φ₃)] ∧
  Submodule.span ℝ (Set.range ![φ₁, φ₂ + φ₃, i.symm (φ₂ - φ₃)]) = ⊤ := by
  sorry



theorem theorem_218809_problem
  (n : ℕ)
  (β : ℝ)
  (f : (Fin n → ℝ) → ℝ)
  (x : Fin n → ℝ)
  (hf : Continuous f)
  (hx : 0 < f x)
  (hβ : (n : ℝ) < β) :
  ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-β) * f y) = ⊤ := by
  sorry



theorem theorem_219127_problem
  {F : Type*} [Field F]
  {n r : ℕ}
  (A : Matrix (Fin n) (Fin n) F)
  (h : ∃ (rows : Fin r → Fin n) (cols : Fin r → Fin n),
    Function.Injective rows ∧ Function.Injective cols ∧ (A.submatrix rows cols).det ≠ 0) :
  r ≤ A.rank := by
  sorry





theorem theorem_219117_problem
  (m n k : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (P : Matrix (Fin m) (Fin m) ℝ)
  (hP : P ∈ Matrix.orthogonalGroup (Fin m) ℝ)
  (hk : k ≤ m)
  (row_norm_sq : Fin m → ℝ)
  (h_row_norm : ∀ i, row_norm_sq i = ∑ j, ((P.transpose * A) i j) ^ 2)
  (S_opt : Finset (Fin m))
  (hS_opt_card : S_opt.card = k)
  (hS_opt_min : ∀ i ∈ S_opt, ∀ j ∉ S_opt, row_norm_sq i ≤ row_norm_sq j) :
  ∀ S : Finset (Fin m), S.card = k →
    ∑ i in S_opt, row_norm_sq i ≤ ∑ i in S, row_norm_sq i := by
  sorry













theorem theorem_219201_problem (n : ℕ) (b : ℝ)
  (π : ℝ → (Fin n → ℝ)) (μ : Fin n → ℝ) :
  (∫ u in (0 : ℝ)..b, π u - μ) = fun i => ∫ u in (0 : ℝ)..b, (π u i - μ i) := by
  sorry

theorem theorem_219966_problem (n : ℕ) (a b : Fin n → ℝ) :
  Matrix.dotProduct a b = Matrix.trace (Matrix.vecMulVec a b) := by
  sorry

theorem theorem_219578_problem
  {m n p : Type*} [Fintype n] [Fintype p]
  (A : Matrix m n ℝ) (B : Matrix n p ℝ)
  (h : ∀ j, A.mulVec (B · j) = 0) :
  A * B = 0 := by
  sorry

