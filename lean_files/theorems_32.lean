import Mathlib
import Mathlib.Tactic

theorem theorem_168202_problem 
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (Cov : V → V → ℝ)
  (const : ℝ → V)
  (X Z u W e : V)
  (beta1 beta2 eta eta3 : ℝ)
  (hX : X = const beta1 + beta2 • Z + u)
  (hZu : Cov Z u = 0)
  (hW : W = eta • X + eta3 • u + e)
  (hXe : Cov X e = 0)
  (hZe : Cov Z e = 0) :
  Cov X e = 0 := by
  sorry







theorem theorem_168789_problem (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : Invertible M) :
  ∃! (TQ : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ),
    let T := TQ.1
    let Q := TQ.2
    M = T * Q ∧
    (∀ i j, i > j → T i j = 0) ∧
    (∀ i, 0 < T i i) ∧
    Q.transpose * Q = 1 := by
  sorry











theorem theorem_168861_problem
  {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (A : V →ₗ[ℝ] W) :
  sSup { n | ∃ x : V, ‖x‖ ≤ 1 ∧ n = ‖A x‖ } = sSup { n | ∃ x : V, ‖x‖ = 1 ∧ n = ‖A x‖ } := by
  sorry

theorem theorem_168491_problem {n : Type*} [Fintype n] [DecidableEq n]
  (f : Matrix n n ℝ × Matrix n n ℝ → ℝ)
  (S : Set (Matrix n n ℝ × Matrix n n ℝ))
  (hS : S = {p | p.1.PosSemidef ∧ p.2.PosSemidef})
  (h_boundary_1 : ∀ X : Matrix n n ℝ, X.PosSemidef → f ((2 : ℝ) • X, 0) = 0)
  (h_boundary_2 : ∀ Y : Matrix n n ℝ, Y.PosSemidef → f (0, (2 : ℝ) • Y) = 0)
  (g : Matrix n n ℝ × Matrix n n ℝ → ℝ)
  (hg_convex : ConvexOn ℝ S g)
  (hg_le : ∀ p ∈ S, g p ≤ f p)
  (hg_greatest : ∀ h, ConvexOn ℝ S h → (∀ p ∈ S, h p ≤ f p) → ∀ p ∈ S, h p ≤ g p) :
  ∀ p ∈ S, g p = 0 := by
  sorry





theorem theorem_169127_problem {K m n : Type*} [Field K]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  (C : Matrix m n K) (D : Matrix n m K)
  (μ : K) (hμ : μ ≠ 0) :
  Module.End.HasEigenvalue (Matrix.toLin' (C * D)) μ ↔
  Module.End.HasEigenvalue (Matrix.toLin' (D * C)) μ := by
  sorry

theorem theorem_169252_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (r : ℝ → E)
  (t : ℝ)
  (h_diff_r : DifferentiableAt ℝ r t)
  (h_diff_dr : DifferentiableAt ℝ (deriv r) t)
  (h_nonzero : ‖deriv r t‖ ≠ 0) :
  deriv (fun x => ‖deriv r x‖) t =
  (1 / ‖deriv r t‖) * inner (deriv r t) (deriv (deriv r) t) := by
  sorry



theorem theorem_169404_problem (n : ℕ)
  (A B X Y : Matrix (Fin n) (Fin n) ℝ)
  (hA : A.IsSymm) (hB : B.IsSymm) (hX : X.IsSymm) (hY : Y.IsSymm)
  (hAX : (X - A).PosSemidef)
  (hXAB : (A + B - X).PosSemidef)
  (hBX : (X - B).PosSemidef)
  (hAY : (Y - A).PosSemidef)
  (hYAB : (A + B - Y).PosSemidef)
  (hBY : (Y - B).PosSemidef)
  (hXY : ¬ (Y - X).PosSemidef)
  (hYX : ¬ (X - Y).PosSemidef) :
  ¬ ∃ C : Matrix (Fin n) (Fin n) ℝ, C.IsSymm ∧
    (C - B).PosSemidef ∧ (X - C).PosSemidef ∧
    (C - A).PosSemidef ∧ (Y - C).PosSemidef := by
  sorry









theorem theorem_169736_problem (n : ℕ) (hn : Odd n)
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA_inv : IsUnit A.det)
  (hB_inv : IsUnit B.det)
  (hA_sym : A.IsSymm)
  (hB_sym : B.IsSymm) :
  ∃ x : ℝ, x ≠ 0 ∧ Module.End.HasEigenvalue (Matrix.toLin' (A⁻¹ * B)) x := by
  sorry

theorem theorem_169597_problem
  (n l : ℕ) (k : ℝ)
  (C_inf C_l H_k : Type*)
  [NormedAddCommGroup C_inf] [NormedSpace ℝ C_inf]
  [NormedAddCommGroup C_l] [NormedSpace ℝ C_l] [CompleteSpace C_l]
  [NormedAddCommGroup H_k] [NormedSpace ℝ H_k] [CompleteSpace H_k]
  -- Topology on C_inf is induced by H_k (isometric embedding into dense subspace)
  (ι : C_inf →L[ℝ] H_k)
  (h_dense : DenseRange ι)
  (h_norm : ∀ x, ‖ι x‖ = ‖x‖)
  -- T is a linear operator
  (T : C_inf →ₗ[ℝ] C_l)
  -- The Sobolev embedding implication: if indices satisfy condition, T is bounded w.r.t H^k norm
  (h_sobolev : k > (n : ℝ) / 2 + l → ∃ C > 0, ∀ x, ‖T x‖ ≤ C * ‖x‖)
  -- The condition k > n/2 + l
  (hk : k > (n : ℝ) / 2 + l) :
  -- Conclusion: T extends to a bounded operator on Hk
  ∃ T_ext : H_k →L[ℝ] C_l, ∀ x, T_ext (ι x) = T x := by
  sorry





theorem theorem_169552_problem
  (n : ℕ)
  (x₂ x₃ y : Fin n → ℝ)
  -- Helper for sum of products (dot product)
  (S : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := λ u v ↦ ∑ i, u i * v i)
  -- Non-degeneracy assumptions (variances non-zero)
  (h₂ : S x₂ x₂ ≠ 0)
  (h₃ : S x₃ x₃ ≠ 0)
  -- Definition of coefficient of determination r²
  (r2_23 : ℝ := (S x₂ x₃)^2 / ((S x₂ x₂) * (S x₃ x₃)))
  -- Assumption that variables are not perfectly correlated
  (h_denom : 1 - r2_23 ≠ 0)
  -- Definitions of simple regression coefficients
  (b_Y2 : ℝ := S x₂ y / S x₂ x₂)
  (b_Y3 : ℝ := S x₃ y / S x₃ x₃)
  (b_32 : ℝ := S x₂ x₃ / S x₂ x₂)
  -- Joint regression coefficients satisfying OLS Normal Equations
  (b_Y2_3 b_Y3_2 : ℝ)
  (h_ols_1 : (S x₂ x₂) * b_Y2_3 + (S x₂ x₃) * b_Y3_2 = S x₂ y)
  (h_ols_2 : (S x₂ x₃) * b_Y2_3 + (S x₃ x₃) * b_Y3_2 = S x₃ y) :
  b_Y2_3 = (b_Y2 - b_Y3 * b_32) / (1 - r2_23) := by
  sorry















theorem theorem_170589_problem
  {F : Type*} [Field F]
  {m n : ℕ}
  (A : Fin n → Matrix (Fin m) (Fin m) F) :
  ¬ IsUnit (List.ofFn A).prod ↔ ∃ i, ¬ IsUnit (A i) := by
  sorry

theorem theorem_170697_problem (A : Matrix (Fin 2) (Fin 2) ℝ)
  (hA : A = !![1, 0; 0, 0]) :
  ¬ ∃ (α : ℝ) (r : ℕ), r > 0 ∧ (A - α • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ^ r = 0 := by
  sorry





theorem theorem_170448_problem
  (n p m T : ℕ)
  (hT : T > 0)
  (y : Fin T → Fin n → ℝ)
  (x : Fin T → Fin (n * p + 1) → ℝ)
  (s : Fin T → Fin m)
  (B : Fin m → Matrix (Fin (n * p + 1)) (Fin n) ℝ)
  (Sigma : Fin m → Matrix (Fin n) (Fin n) ℝ)
  (Pi : Matrix (Fin m) (Fin m) ℝ)
  -- Abstract density function phi(y, mean, covariance)
  (phi : (Fin n → ℝ) → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ → ℝ)
  (hPi_nonneg : ∀ i j, 0 ≤ Pi i j)
  (hPi_sum : ∀ i, ∑ j, Pi i j = 1) :
  -- LHS: The natural likelihood derived from model assumptions
  (∏ t : Fin T, phi (y t) ((B (s t)).transpose.mulVec (x t)) (Sigma (s t))) *
  (∏ t : Fin T, if h : t.val > 0 then Pi (s ⟨t.val - 1, by omega⟩) (s t) else 1) =
  -- RHS: The likelihood formula stated in the problem using indicators
  (∏ t : Fin T, ∏ j : Fin m,
    if s t = j then phi (y t) ((B j).transpose.mulVec (x t)) (Sigma j) else 1) *
  (∏ t : Fin T, if h : t.val > 0 then
    ∏ i : Fin m, ∏ j : Fin m,
      if s ⟨t.val - 1, by omega⟩ = i ∧ s t = j then Pi i j else 1
   else 1) := by
  sorry

theorem theorem_170904_problem
  {X : Type*} [AddCommGroup X] [Module ℝ X]
  (Y : Subspace ℝ X)
  (x_star : X →ₗ[ℝ] ℝ)
  (h1 : ∃ y ∈ Y, x_star y = 1)
  (h2 : ∀ z : X, x_star z = 1 → z ∈ Y) :
  Y = ⊤ := by
  sorry

theorem theorem_170675_problem (n : ℕ) (hn : n > 0)
  (ones : Fin n → ℝ) (h_ones : ones = fun _ ↦ 1)
  (I : Matrix (Fin n) (Fin n) ℝ) (hI : I = 1)
  (J : Matrix (Fin n) (Fin n) ℝ)
  (hJ : J = I - (1 / (n : ℝ)) • Matrix.vecMulVec ones ones) :
  Matrix.mulVec J ones = 0 := by
  sorry



theorem theorem_170231_problem
  (l m n : ℕ)
  (x1 : Fin l → ℝ)
  (x2 : Fin m → ℝ)
  (x3 : Fin n → ℝ)
  (g : ℕ) (hg : g = max l (max m n))
  (h : ℕ) (hh : h = l + m + n)
  (a1 a2 a3 : ℝ)
  (ha : a1 = 1 ∧ a2 = 1 ∧ a3 = 1) :
  let x_hat_k (dim : ℕ) (v : Fin dim → ℝ) : Fin g → ℝ :=
    fun i => if h_idx : i < dim then v ⟨i, h_idx⟩ else 0
  let x_hat : Fin (3 * g) → ℝ := fun i =>
    if h1 : i < g then a1 * x_hat_k l x1 ⟨i, h1⟩
    else if h2 : i < 2 * g then a2 * x_hat_k m x2 ⟨i - g, by omega⟩
    else a3 * x_hat_k n x3 ⟨i - 2 * g, by omega⟩
  let P : Matrix (Fin (3 * g)) (Fin h) ℝ := fun i j =>
    if i < g then
      if j < l ∧ (i : ℕ) = (j : ℕ) then 1 else 0
    else if i < 2 * g then
      if (l ≤ j ∧ j < l + m) ∧ (i - g : ℕ) = (j - l : ℕ) then 1 else 0
    else
      if (l + m ≤ j) ∧ (i - 2 * g : ℕ) = (j - (l + m) : ℕ) then 1 else 0
  let x_target : Fin h → ℝ := fun i =>
    if h1 : (i : ℕ) < l then x1 ⟨i, h1⟩
    else if h2 : (i : ℕ) < l + m then x2 ⟨i - l, by omega⟩
    else x3 ⟨i - (l + m), by omega⟩
  P.transpose.mulVec x_hat = x_target := by
  sorry















theorem theorem_171364_problem
  (n p : ℕ)
  (ε : Matrix (Fin n) (Fin 1) ℝ)
  (V V_hat A_n : Matrix (Fin n) (Fin n) ℝ)
  (Z : Matrix (Fin n) (Fin p) ℝ)
  (l : Matrix (Fin p) (Fin 1) ℝ)
  (V_half_inv : Matrix (Fin n) (Fin n) ℝ)
  [Invertible V]
  [Invertible V_hat]
  [Invertible (Z.transpose * V_hat⁻¹ * Z)]
  (h_V_sqrt : V_half_inv * V_half_inv = V⁻¹)
  (h_V_sqrt_symm : V_half_inv.IsSymm)
  (h_V_hat_symm : V_hat.IsSymm)
  (h_A_n_symm : A_n.IsSymm) :
  let T := l.transpose * (Z.transpose * V_hat⁻¹ * Z)⁻¹ * Z.transpose * V_half_inv * A_n * V_half_inv * ε
  let bound := (ε.transpose * V⁻¹ * ε) * (l.transpose * (Z.transpose * V_hat⁻¹ * Z)⁻¹ * Z.transpose * V_half_inv * (A_n ^ 2) * V_half_inv * Z * (Z.transpose * V_hat⁻¹ * Z)⁻¹ * l)
  (T 0 0) ^ 2 ≤ (bound 0 0) := by
  sorry

theorem theorem_171494_problem
  (E : Submodule ℝ C(unitInterval, ℝ))
  (hE : FiniteDimensional ℝ E)
  (T : C(unitInterval, ℝ) →L[ℝ] E)
  (hT : T ≠ 0) :
  ∃ f₀ : C(unitInterval, ℝ), ‖f₀ - (T f₀ : C(unitInterval, ℝ))‖ > ‖f₀‖ := by
  sorry



theorem theorem_171368_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (m n : H →L[ℂ] H) (lam mu : ℂ) :
  ContinuousLinearMap.adjoint (lam • m + mu • n) =
  (star lam) • ContinuousLinearMap.adjoint m + (star mu) • ContinuousLinearMap.adjoint n := by
  sorry

theorem theorem_171521_problem
  {K V W : Type*}
  [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (T : V →ₗ[K] W)
  {k : ℕ}
  (v : Fin k → V)
  (h : ¬ LinearIndependent K v) :
  ¬ LinearIndependent K (T ∘ v) := by
  sorry















theorem theorem_172353_problem
  (m : ℝ → ℝ)
  (x₁ x₂ : ℝ)
  (hx : x₁^2 + x₂^2 ≠ 0)
  (hm : DifferentiableAt ℝ m (Real.sqrt (x₁^2 + x₂^2))) :
  let x := Real.sqrt (x₁^2 + x₂^2)
  deriv (fun t => (m (Real.sqrt (t^2 + x₂^2)) / (Real.sqrt (t^2 + x₂^2))^2) * t) x₁ =
  (x₁^2 / x^3) * deriv m x + ((x₂^2 - x₁^2) / x^4) * m x := by
  sorry





theorem theorem_172383_problem
  (p ν : ℝ)
  (hp : 2 < p)
  (hν : ν < 1)
  (u : ℂ)
  (hu : |u.re| < 1 / 2 - 1 / p) :
  ∃ x : ℕ → ℂ,
    Summable (fun n => (Complex.abs (x n)) ^ p) ∧
    x ≠ 0 ∧
    ∀ k : ℕ, (∑' n : ℕ, x n / ((1 : ℝ) - ν + k + n : ℂ)) = (π / Complex.cos (π * u)) * x k := by
  sorry

theorem theorem_172596_problem
  {V : Type*}
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  (x y : V)
  (h : inner x y = (0 : ℝ)) :
  ‖x + y‖^2 = ‖x‖^2 + ‖y‖^2 := by
  sorry







theorem theorem_172774_problem
  (n : ℕ)
  (X : Matrix (Fin n) (Fin 3) ℝ)
  (y : Matrix (Fin n) (Fin 1) ℝ)
  (β : Matrix (Fin 3) (Fin 1) ℝ)
  (ε : Matrix (Fin n) (Fin 1) ℝ)
  -- Conditions from the problem
  (h_model : y = X * β + ε)
  (h_inv : Invertible (X.transpose * X))
  -- Abstract Expectation operators and properties derived from solution context
  (E_vec : Matrix (Fin n) (Fin 1) ℝ → Matrix (Fin n) (Fin 1) ℝ)
  (E_param : Matrix (Fin 3) (Fin 1) ℝ → Matrix (Fin 3) (Fin 1) ℝ)
  (h_mean_zero : E_vec ε = 0)
  (h_lin : ∀ (A : Matrix (Fin 3) (Fin n) ℝ) (v : Matrix (Fin n) (Fin 1) ℝ),
    E_param (A * v) = A * E_vec v)
  (h_add : ∀ (u v : Matrix (Fin 3) (Fin 1) ℝ), E_param (u + v) = E_param u + E_param v)
  (h_const : E_param β = β) :
  -- Conclusion: The OLS estimator is unbiased
  E_param ((X.transpose * X)⁻¹ * X.transpose * y) = β := by
  sorry









theorem theorem_172880_problem :
  ∃ (n : ℕ) (A A_tilde B : Matrix (Fin n) (Fin n) ℝ),
    A.charpoly = A_tilde.charpoly ∧
    (B * A * B).charpoly ≠ (B * A_tilde * B).charpoly := by
  sorry



















theorem theorem_173776_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (x : H →L[𝕜] H) :
  LinearMap.ker (ContinuousLinearMap.adjoint x * x) = LinearMap.ker x := by
  sorry



theorem theorem_173718_problem (A : Matrix (Fin 2) (Fin 2) ℝ) (c C : ℝ)
  (hc : 0 ≤ c) (hC : c ≤ C)
  (h_eig : (A.transpose * A).charpoly = Polynomial.X ^ 2 - Polynomial.C (c ^ 2 + C ^ 2) * Polynomial.X + Polynomial.C (c ^ 2 * C ^ 2)) :
  A.det = c * C ∨ A.det = -(c * C) := by
  sorry











theorem theorem_173534_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {𝕜 : Type*} [RCLike 𝕜]
  (B Q : Matrix n n 𝕜)
  (hB : B.IsHermitian)
  (hQ : IsUnit Q)
  (h_adj : (Q * B * Q⁻¹).IsHermitian) :
  B * Q = Q * B := by
  sorry



theorem theorem_174248_problem (p : ℕ) (hp : 0 < p) :
  let I := {x : Fin p × Fin p // x.1 ≥ x.2}
  let to_T (u : I → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
    fun i j => if h : i ≥ j then u ⟨(i, j), h⟩ else 0
  let to_vec (M : Matrix (Fin p) (Fin p) ℝ) : I → ℝ :=
    fun x => M x.1.1 x.1.2
  let ϕ (u : I → ℝ) : I → ℝ :=
    to_vec ((to_T u) * (to_T u).transpose)
  ∀ t : I → ℝ, (∀ i : Fin p, t ⟨(i, i), le_refl i⟩ > 0) →
    LinearMap.det (fderiv ℝ ϕ t).toLinearMap = 
      2^p * ∏ j : Fin p, (t ⟨(j, j), le_refl j⟩) ^ (p - (j : ℕ)) := by
  sorry

theorem theorem_173972_problem (n : ℕ) (K : Type*) [Field K]
  (s : Finset (MvPolynomial (Fin n) K))
  (h : Ideal.span (s : Set (MvPolynomial (Fin n) K)) = 
       Ideal.span (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) K))) :
  n ≤ s.card := by
  sorry

theorem theorem_174253_problem (n : ℕ) (hn : n > 0)
  (V : Matrix (Fin n) (Fin n) ℤ)
  (hV : ∀ i j, V i j = ((i : ℤ) + 1) ^ (j : ℕ))
  (h_det : V.det ≠ 0)
  (p : Fin n → ℕ)
  (hp_prime : ∀ i, Nat.Prime (p i))
  (hp_mod : ∀ i, V.det ∣ ((p i : ℤ) - 1)) :
  ∃! P : Polynomial ℤ, P.natDegree < n ∧ ∀ i : Fin n, P.eval ((i : ℤ) + 1) = (p i : ℤ) := by
  sorry





