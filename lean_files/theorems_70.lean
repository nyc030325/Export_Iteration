import Mathlib
import Mathlib.Tactic



theorem theorem_379428_problem 
  (f : ℂ → ℂ) 
  (M : ℝ) 
  (z₀ : ℂ)
  (h_holo : DifferentiableOn ℂ f (Metric.ball 0 1))
  (h_bound : ∀ z ∈ Metric.ball 0 1, Complex.abs (f z) ≤ M)
  (h_norm : f 0 = 1)
  (h_z₀_in : z₀ ∈ Metric.ball 0 1)
  (h_zero : f z₀ = 0) :
  1 / M ≤ Complex.abs z₀ := by
  sorry



theorem theorem_379602_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (α β : ℝ)
  (R f ε one : V)
  (E : V →ₗ[ℝ] ℝ)
  (h_model : R = α • one + β • f + ε)
  (h_eps : E ε = 0)
  (h_one : E one = 1)
  (h_factor_assumption : E R = β * E f) :
  α = 0 := by
  sorry







theorem theorem_379931_problem (R : Set ℂ) (f : ℂ → ℂ)
  (hR_compact : IsCompact R)
  (hR_int_nonempty : (interior R).Nonempty)
  (hf_cont : ContinuousOn f R)
  (hf_diff : DifferentiableOn ℂ f (interior R)) :
  ∃ z₀ ∈ frontier R, ∀ z ∈ R, Complex.abs (f z) ≤ Complex.abs (f z₀) := by
  sorry

theorem theorem_379334_problem
  (m n r : ℕ)
  (X1 S Sr : Matrix (Fin m) (Fin n) ℝ)
  (U Ur : Matrix (Fin m) (Fin m) ℝ)
  (V Vr : Matrix (Fin n) (Fin n) ℝ)
  (X1r : Matrix (Fin m) (Fin n) ℝ)
  (h_svd : X1 = U * S * V.transpose)
  (h_V_orth : V.transpose * V = 1)
  (h_Ur : ∀ i j, Ur i j = if (j : ℕ) < r then U i j else 0)
  (h_Sr : ∀ i j, Sr i j = if (j : ℕ) < r then S i j else 0)
  (h_Vr : ∀ i j, Vr i j = if (j : ℕ) < r then V i j else 0)
  (h_X1r : X1r = Ur * Sr * Vr.transpose) :
  X1 * Vr = X1r * Vr := by
  sorry







theorem theorem_379806_problem 
  (s_kj : ℝ) -- Schoenfeld residual for covariate j at time t_k
  (V_tk : ℝ) -- risk-weighted covariate covariance (treated as scalar/1D for simplicity)
  (hV : V_tk ≠ 0) -- Assumption that covariance is invertible
  (S_star_kj : ℝ) -- Scaled Schoenfeld residual
  (h_def : S_star_kj = V_tk⁻¹ * s_kj) -- Definition: pre-multiplying by inverse variance
  (beta_j : ℝ) -- time-invariant coefficient estimate
  (beta_j_tk : ℝ) -- time-dependent regression coefficient
  (E_S_star : ℝ) -- Expected value of the scaled Schoenfeld residual
  : 
  -- The relationship to be proved:
  E_S_star + beta_j = beta_j_tk := by
  sorry



theorem theorem_380822_problem
  {F : Type*} [Field F]
  (m n : ℕ)
  (h_ineq : m < n)
  (A : Matrix (Fin m) (Fin n) F) :
  ∃ y : Fin n → F, y ≠ 0 ∧ A.mulVec y = 0 := by
  sorry

theorem theorem_379705_problem
  (n : ℕ)
  (y : Fin n → Fin n → ℝ)
  (x : Fin n → ℝ)
  (c : Fin n → ℝ)
  (p : Fin n → ℝ)
  (z : Fin n → ℝ)
  (h : ∀ i, z i = c i * (p i - Matrix.dotProduct (y i) x)) :
  z = Matrix.mulVec (Matrix.diagonal c) p - 
      Matrix.mulVec (Matrix.diagonal c) (Matrix.mulVec y x) := by
  sorry





theorem theorem_379689_problem 
  (n : ℝ) (hn : 0 < n)
  (d₁ d₂ : ℝ)
  (L₁ L₂ : ℝ) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
  (m₁ m₂ : ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
  (V₁ V₂ : ℝ) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
  (C₁ C₂ R₁ R₂ : ℝ)
  -- Laplace approximation for marginal likelihoods:
  (h_laplace_1 : Real.log m₁ = Real.log L₁ - 1/2 * Real.log V₁ + R₁)
  (h_laplace_2 : Real.log m₂ = Real.log L₂ - 1/2 * Real.log V₂ + R₂)
  -- Asymptotic scaling of the Hessian determinants:
  (h_hess_1 : Real.log V₁ = d₁ * Real.log n + C₁)
  (h_hess_2 : Real.log V₂ = d₂ * Real.log n + C₂) :
  Real.log (m₁ / m₂) = 
    (Real.log (L₁ / L₂) - (d₁ - d₂) / 2 * Real.log n) + 
    (R₁ - R₂ - (C₁ - C₂) / 2) := by
  sorry

theorem theorem_380270_problem (m n k : ℕ) (hk : k < min m n) :
  IsClosed {A : Matrix (Fin m) (Fin n) ℝ | A.rank < k} := by
  sorry

theorem theorem_380758_problem (n : ℕ) [NeZero n]
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA : A.PosDef) (hB : B.PosDef)
  (k : Fin n)
  (eigsA eigsB eigsAB : Fin n → ℝ)
  (h_eigsA : Multiset.map (algebraMap ℝ ℂ) (Multiset.map eigsA Finset.univ.val) = (A.charpoly.map (algebraMap ℝ ℂ)).roots)
  (h_eigsB : Multiset.map (algebraMap ℝ ℂ) (Multiset.map eigsB Finset.univ.val) = (B.charpoly.map (algebraMap ℝ ℂ)).roots)
  (h_eigsAB : Multiset.map (algebraMap ℝ ℂ) (Multiset.map eigsAB Finset.univ.val) = ((A * B).charpoly.map (algebraMap ℝ ℂ)).roots)
  (h_monoA : Monotone eigsA)
  (h_monoB : Monotone eigsB)
  (h_monoAB : Monotone eigsAB) :
  eigsAB k ≥ eigsB 0 * eigsA k := by
  sorry









theorem theorem_380941_problem (n i : ℕ)
  (f : MvPolynomial (Fin (n + 1)) ℝ)
  (h_homog : MvPolynomial.IsHomogeneous f i)
  (x : Fin (n + 1) → ℝ)
  (c : ℝ) :
  MvPolynomial.eval (c • x) f = c ^ i * MvPolynomial.eval x f := by
  sorry





theorem theorem_381323_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (D : Submodule ℂ H)
  (T : H →ₗ[ℂ] H)
  (h1 : ∀ x ∈ D, inner (T x) x = (0 : ℂ))
  (h2 : ∀ x ∈ D, T x ∈ D) :
  ∀ x ∈ D, T x = 0 := by
  sorry

theorem theorem_381314_problem
  (U : Set ℝ) (hU : IsOpen U)
  (fn : ℕ → U → ℝ) (f : U → ℝ)
  (x₀ : U)
  (h_unif : TendstoUniformly fn f Filter.atTop)
  (h_cont : ∀ n, ContinuousAt (fn n) x₀) :
  ContinuousAt f x₀ := by
  sorry





theorem theorem_381408_problem
  {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  (P_pred : Matrix n n ℝ) (H : Matrix m n ℝ) (R : Matrix m m ℝ)
  (P_est : Matrix n n ℝ)
  [Invertible P_pred] [Invertible R]
  [Invertible (H * P_pred * H.transpose + R)]
  [Invertible P_est]
  (h_kalman : P_est = P_pred - P_pred * H.transpose * (H * P_pred * H.transpose + R)⁻¹ * H * P_pred) :
  P_est⁻¹ = P_pred⁻¹ + H.transpose * R⁻¹ * H := by
  sorry

theorem theorem_381162_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (L : H →L[𝕜] H)
  (h : LinearMap.ker L ≠ ⊤) :
  ∃ y : H, y ≠ 0 ∧ y ∈ (LinearMap.ker L).orthogonal := by
  sorry









theorem theorem_382012_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (A : Module.End F V)
  (q : Polynomial F)
  (lam : F)
  (r : ℕ)
  (h : (A - lam • (1 : Module.End F V)) ^ r * (Polynomial.aeval A q) = 0) :
  LinearMap.range (Polynomial.aeval A q) ≤ LinearMap.ker ((A - lam • (1 : Module.End F V)) ^ r) := by
  sorry





theorem theorem_382030_problem (A B : EuclideanSpace ℝ (Fin 3))
  (hA : A ≠ 0) (hB : B ≠ 0) :
  ‖A‖^2 = (inner A B / ‖B‖)^2 + (‖crossProduct A B‖ / ‖B‖)^2 := by
  sorry

theorem theorem_381991_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (P : Set V)
  (hP_cone : ∀ x ∈ P, ∀ r : ℝ, 0 < r → r • x ∈ P)
  (c₁ : V) (hc₁ : c₁ ∈ interior P)
  (a : ℝ) (ha : 0 < a) :
  a • c₁ ∈ interior P := by
  sorry



theorem theorem_381615_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : ℕ}
  (e : Basis (Fin n) K V)
  (ebar : Basis (Fin n) K V)
  (A : Matrix (Fin n) (Fin n) K)
  (g : V →ₗ[K] V →ₗ[K] K)
  (h_trans : ∀ i, ebar i = ∑ j, A i j • e j)
  (h_orth : A⁻¹ = A.transpose) :
  ∑ i : Fin n, ∑ j : Fin n, g (e i) (e j) • (e i ⊗ₜ[K] e j) =
  ∑ i : Fin n, ∑ j : Fin n, g (ebar i) (ebar j) • (ebar i ⊗ₜ[K] ebar j) := by
  sorry





theorem theorem_381664_problem
  (A : Set ℝ)
  (fn : ℕ → ℝ → ℝ)
  (f : ℝ → ℝ)
  (h_pt : ∀ x ∈ A, Filter.Tendsto (fun n ↦ fn n x) Filter.atTop (nhds (f x)))
  (h_cauchy : ∀ ε > 0, ∃ N : ℕ, ∀ n m : ℕ, n > N → m > N → ∀ x ∈ A, |fn n x - fn m x| < ε) :
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n > N → ∀ x ∈ A, |fn n x - f x| < ε := by
  sorry

theorem theorem_382028_problem (M N : ℕ) (hM : M > 0) (hN : N > 0)
  (A : Matrix (Fin (M * N)) (Fin (M * N)) ℝ)
  (hA : ∀ (i j : Fin (M * N)), A i j ≠ 0 → (i : ℕ) % M = (j : ℕ) % M) :
  ∃ σ : Equiv.Perm (Fin (M * N)),
    let B := A.submatrix σ σ
    ∀ (i j : Fin (M * N)), B i j ≠ 0 → (i : ℕ) / N = (j : ℕ) / N := by
  sorry





theorem theorem_382761_problem (n p : ℕ)
  (X : Matrix (Fin n) (Fin p) ℝ)
  (y : Matrix (Fin n) (Fin 1) ℝ)
  (h_inv : Invertible (X.transpose * X))
  (hat_beta : Matrix (Fin p) (Fin 1) ℝ)
  (h_beta : hat_beta = (X.transpose * X)⁻¹ * (X.transpose * y))
  (hat_epsilon : Matrix (Fin n) (Fin 1) ℝ)
  (h_epsilon : hat_epsilon = y - X * hat_beta) :
  X.transpose * hat_epsilon = 0 := by
  sorry



theorem theorem_382181_problem
  (ε : ℝ) (hε : ε ≠ 0)
  (v : ℝ → ℝ)
  (hv : ContDiff ℝ 1 v)
  (h_opt : ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → u 0 = 0 → u 1 = 0 → 
    (-ε * v 1 * deriv u 1) - (-ε * v 0 * deriv u 0) = 0) :
  v 0 = 0 ∧ v 1 = 0 := by
  sorry

theorem theorem_382521_problem
  {n k : ℕ}
  {K : Type*} [Field K]
  (A : Fin k → Matrix (Fin n) (Fin n) K)
  (h_indep : LinearIndependent K A)
  (h_strict_upper : ∀ (j : Fin k) (r c : Fin n), c ≤ r → A j r c = 0) :
  ∀ (j : Fin k), (A j) ^ n = 0 := by
  sorry







































theorem theorem_383453_problem
  (n m : ℕ)
  (F : (Fin n → ℝ) → (Fin m → ℝ))
  (hF : Differentiable ℝ F)
  (β : (Fin m → ℝ) → ((Fin m → ℝ) →L[ℝ] ℝ))
  (x : Fin n → ℝ)
  (i : Fin n) :
  let e_i := Pi.single i 1
  let v := fderiv ℝ F x e_i
  let β_comps := fun j => β (F x) (Pi.single j 1)
  β (F x) v = Matrix.dotProduct β_comps v := by
  sorry









theorem theorem_384028_problem (K : Type*) [CommRing K] (p : Ideal (Polynomial K)) :
  ∃! ϕ : Polynomial (Polynomial K) →+* Polynomial (Polynomial K ⧸ p),
    (∀ f : Polynomial K, ϕ (Polynomial.C f) = Polynomial.C (Ideal.Quotient.mk p f)) ∧
    (ϕ Polynomial.X = Polynomial.X) := by
  sorry

theorem theorem_383749_problem
  (d : ℕ)
  (p : EuclideanSpace ℝ (Fin d) → ℝ)
  (T : EuclideanSpace ℝ (Fin d) × ℝ → EuclideanSpace ℝ (Fin d))
  (x : EuclideanSpace ℝ (Fin d))
  (ε : ℝ)
  (hp : Differentiable ℝ p)
  (hT : Differentiable ℝ T) :
  deriv (fun t => p (T (x, t))) ε =
  inner (gradient p (T (x, ε))) (deriv (fun t => T (x, t)) ε) := by
  sorry

theorem theorem_383858_problem (r : ℝ) (hr : r > 1) :
  ∃ f : ℝ → ℝ, TendstoUniformlyOn
    (fun N x ↦ ∑ n in Finset.range N, (n : ℝ) * Real.log (1 + (n : ℝ) * x) / x ^ n)
    f atTop (Set.Ici r) := by
  sorry

theorem theorem_383710_problem 
  (TestFun Distr : Type*) 
  [AddCommGroup TestFun] [Module ℝ TestFun]
  (pair : Distr → TestFun → ℝ)
  (h_pair_lin : ∀ (φ : Distr) (c : ℝ) (f : TestFun), pair φ (c • f) = c * pair φ f)
  (n : ℕ)
  (Dn_test : TestFun → TestFun)
  (Dn_dist : Distr → Distr)
  (h_def : ∀ (φ : Distr) (f : TestFun), pair (Dn_dist φ) f = pair φ ((-1 : ℝ)^n • Dn_test f))
  (δ : Distr) :
  ∀ (f : TestFun), pair (Dn_dist δ) f = (-1 : ℝ)^n * pair δ (Dn_test f) := by
  sorry

theorem theorem_383929_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (A : E ≃L[ℝ] E)
  (x b y r : E)
  (hx : x ≠ 0)
  (h_exact : A x = b)
  (h_resid : r = A y - b)
  (k : ℝ)
  (hk : k = ‖(A : E →L[ℝ] E)‖ * ‖(A.symm : E →L[ℝ] E)‖) :
  ‖y - x‖ / ‖x‖ ≤ k * (‖r‖ / ‖b‖) := by
  sorry













theorem theorem_383982_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (p : V → ℝ)
  (h_sub : ∀ x y : V, p (x + y) ≤ p x + p y)
  (h_hom : ∀ (x : V) (c : ℝ), 0 ≤ c → p (c • x) = c * p x) :
  ∀ x : V, p x = sSup {r : ℝ | ∃ (Λ : V →ₗ[ℝ] ℝ), (∀ v : V, Λ v ≤ p v) ∧ r = Λ x} := by
  sorry



















