import Mathlib
import Mathlib.Tactic













theorem theorem_142694_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
  (h : Function.Injective (Matrix.mulVec A.transpose)) :
  Function.Injective (Matrix.mulVec (A * A.transpose)) := by
  sorry

theorem theorem_142579_problem (k r : EuclideanSpace ℝ (Fin 3))
  (θ : ℝ) (hθ : θ = InnerProductGeometry.angle k r) :
  inner k r = ‖k‖ * ‖r‖ * Real.cos θ := by
  sorry



theorem theorem_142368_problem (x' y' z' : ℝ) :
  let R : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun v => v - ![x', y', z']
  ∀ v : Fin 3 → ℝ, 
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3)) (fderiv ℝ R v).toLinearMap = 1 := by
  sorry



theorem theorem_142742_problem (n : List ℕ) 
  (h_pos : ∀ x ∈ n, 0 < x)
  (h_sum : n.sum = 4) :
  ∃ l ∈ [[4], [3, 1], [2, 2], [2, 1, 1], [1, 1, 1, 1]], n.Perm l := by
  sorry



theorem theorem_142795_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (M : Set V) (hM_conv : Convex ℝ M) (hM_zero : 0 ∈ M)
  (p : V → ℝ)
  (hp : ∀ x, p x = sInf {t : ℝ | 0 < t ∧ (t⁻¹ • x) ∈ M})
  (l : V →ₗ[ℝ] ℝ)
  (hl : ∀ y ∈ M, |l y| ≤ 1) :
  ∀ x, |l x| ≤ p x := by
  sorry



theorem theorem_142719_problem
  (T : C(Set.Icc (0 : ℝ) 1, ℝ) →L[ℝ] C(Set.Icc (0 : ℝ) 1, ℝ))
  (h : ∃ M : ℝ, ∀ y ∈ T '' (Metric.closedBall 0 1),
    ∃ f : ℝ → ℝ, (∀ t : Set.Icc (0 : ℝ) 1, f t = y t) ∧
    ∃ f' : ℝ → ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt f (f' t) (Set.Icc 0 1) t ∧ |f' t| ≤ M) :
  IsCompact (closure (T '' (Metric.closedBall 0 1))) := by
  sorry

theorem theorem_143062_problem (n : ℕ) (hn : n > 0) (A : Matrix (Fin n) (Fin n) ℝ)
  (h : ∀ j, ∑ i, A i j = 1) :
  Module.End.HasEigenvalue (Matrix.toLin' A) 1 := by
  sorry

theorem theorem_142866_problem
  (a b c d : ℝ)
  (v1 v2 x1 x2 : ℝ)
  (h_det : a * d - b * c ≠ 0)
  (h_eq : Matrix.mulVec !![a, b; c, d] ![x1, x2] = ![v1, v2]) :
  ![x1, x2] = (1 / (a * d - b * c)) • Matrix.mulVec !![d, -b; -c, a] ![v1, v2] := by
  sorry





theorem theorem_143385_problem
  (n p : ℕ)
  (hnp : p ≤ n)
  (X : Matrix (Fin n) (Fin p) ℝ)
  (U : Matrix (Fin n) (Fin n) ℝ)
  (V : Matrix (Fin p) (Fin p) ℝ)
  (σ : Fin p → ℝ)
  (Sigma_mat : Matrix (Fin n) (Fin p) ℝ)
  (hU : U.transpose * U = 1)
  (hV : V.transpose * V = 1)
  (hSigma_mat : ∀ i j, Sigma_mat i j = if i.val = j.val then σ j else 0)
  (hX : X = U * Sigma_mat * V.transpose)
  (A : Matrix (Fin p) (Fin p) ℝ)
  (hA : A = X.transpose * X) :
  A.det = ∏ i, (σ i)^2 := by
  sorry







theorem theorem_143255_problem
  (N L : ℕ)
  (hLN : L ≤ N)
  (A : Matrix (Fin N) (Fin N) ℂ)
  (X : Matrix (Fin N) (Fin L) ℂ)
  (hA : A.IsHermitian)
  (hX_diag : ∀ (i : Fin N) (j : Fin L), i.val ≠ j.val → X i j = 0)
  (hX_mod : ∀ (j : Fin L), Complex.abs (X (Fin.castLE hLN j) j) = 1) :
  (X.conjTranspose * A * X).det = (A.submatrix (Fin.castLE hLN) (Fin.castLE hLN)).det := by
  sorry







theorem theorem_143536_problem
  {K : Type*} [Field K]
  {E : Type*} [AddCommGroup E] [Module K E]
  (X : Set E) :
  (Submodule.span K X : Set E) =
    { v | ∃ (n : ℕ) (c : Fin n → K) (x : Fin n → E),
      (∀ i, x i ∈ X) ∧ v = ∑ i, c i • x i } := by
  sorry





theorem theorem_143932_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (h : IsUnit A) : Matrix.det A⁻¹ = (Matrix.det A)⁻¹ := by
  sorry







theorem theorem_143894_problem (n : ℕ) (D : Fin n → Fin n → ℝ) (r : Fin n → ℝ) (i : Fin n) :
  ∑ j : Fin n, ∑ k : Fin n, D j k * (r k * (if i = j then (1 : ℝ) else 0) - r i * (if j = k then (1 : ℝ) else 0) - r j * (if i = k then (1 : ℝ) else 0)) =
  (∑ k : Fin n, D i k * r k) - (∑ k : Fin n, D k k) * r i - (∑ j : Fin n, D j i * r j) := by
  sorry















theorem theorem_144250_problem
  {K : Type*} [Field K]
  (n : ℕ)
  (x : Fin n → K)
  (a : Fin n → K)
  (P : Fin n → Polynomial K)
  (hx : Function.Injective x)
  (h_deg : ∀ j, (P j).degree = j)
  (h_lead : ∀ j, (P j).leadingCoeff = a j) :
  (Matrix.of (fun i j ↦ (P j).eval (x i))).det =
    (∏ j, a j) * ∏ i : Fin n, ∏ j in Finset.Ioi i, (x j - x i) := by
  sorry







theorem theorem_144955_problem (φ θ ψ : ℝ) :
  let R_X : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, Real.cos φ, -Real.sin φ; 0, Real.sin φ, Real.cos φ]
  let R_Y : Matrix (Fin 3) (Fin 3) ℝ := !![Real.cos θ, 0, Real.sin θ; 0, 1, 0; -Real.sin θ, 0, Real.cos θ]
  let R_Z : Matrix (Fin 3) (Fin 3) ℝ := !![Real.cos ψ, -Real.sin ψ, 0; Real.sin ψ, Real.cos ψ, 0; 0, 0, 1]
  -- The problem claims that applying sequential rotations about local axes (X, then Y, then Z)
  -- results in the matrix given by the reversed order of multiplication: M = R_Z * R_Y * R_X.
  -- Mathematically, sequential local rotations corresponds to post-multiplication: R_X * R_Y * R_Z.
  -- The proof problem is to verify the claimed equality between the sequential process and the formula.
  R_X * R_Y * R_Z = R_Z * R_Y * R_X := by
  sorry





theorem theorem_145275_problem
  (A : Matrix (Fin 3) (Fin 3) ℚ)
  (x y : Fin 3 → ℚ)
  (hA : A = !![0, 0, 0; 0, 0, 1; 0, 0, 0])
  (hx : x = ![0, 0, 1])
  (hy : y = ![1, 0, 1]) :
  (Matrix.mulVec (A ^ 2) x = 0) ∧ (Matrix.mulVec A x ≠ 0) ∧
  (Matrix.mulVec (A ^ 2) y = 0) ∧ (Matrix.mulVec A y ≠ 0) ∧
  (y ∉ Submodule.span ℚ {x, Matrix.mulVec A x}) ∧
  (x ∉ Submodule.span ℚ {y, Matrix.mulVec A y}) := by
  sorry

theorem theorem_145062_problem
  (n : ℕ)
  (log_p : ℕ → ℝ)
  (k_star : ℕ)
  (h_range : k_star ∈ Finset.Icc 1 (n - 1))
  (h_optim : ∀ k ∈ Finset.Icc 1 (n - 1), log_p k ≤ log_p k_star) :
  ∀ k ∈ Finset.Icc 1 (n - 1), log_p k_star ≥ log_p k := by
  sorry

theorem theorem_145137_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (l : H →L[ℝ] ℝ)
  (h₀ : H)
  (h_rep : ∀ u : H, l u = inner u h₀) :
  ∀ v : ℝ, ContinuousLinearMap.adjoint l v = v • h₀ := by
  sorry



theorem theorem_145491_problem
  (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (A : V →ₗ[ℂ] V)
  (m : ℕ)
  (roots : Fin m → ℂ)
  (exps : Fin m → ℕ)
  (h_distinct : Function.Injective roots)
  (h_minpoly : minpoly ℂ A = ∏ i, (Polynomial.X - Polynomial.C (roots i)) ^ (exps i))
  (V_i : Fin m → Submodule ℂ V)
  (h_Vi : ∀ i, V_i i = LinearMap.ker ((A - (roots i) • LinearMap.id) ^ (exps i))) :
  DirectSum.IsInternal V_i := by
  sorry



theorem theorem_145613_problem 
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (n : ℕ)
  (u₁ u₂ : V)
  (w : Fin n → V)
  (h_indep : LinearIndependent K (![u₁, u₂] : Fin 2 → V))
  (h_span : Submodule.span K ({u₁, u₂} ∪ Set.range w) = ⊤)
  (h_dep : u₂ ∈ Submodule.span K ({u₁} ∪ Set.range w)) :
  ∃ j : Fin n, Submodule.span K (({u₁, u₂} ∪ Set.range w) \ {w j}) = ⊤ := by
  sorry









theorem theorem_145785_problem
  (n m p : ℕ)
  (y : Matrix (Fin n) (Fin 1) ℝ)
  (X : Matrix (Fin n) (Fin p) ℝ)
  (X_tilde : Matrix (Fin m) (Fin p) ℝ)
  (Sigma : Matrix (Fin n) (Fin n) ℝ)
  (Sigma_12 : Matrix (Fin n) (Fin m) ℝ)
  (Sigma_21 : Matrix (Fin m) (Fin n) ℝ)
  (Sigma_tilde : Matrix (Fin m) (Fin m) ℝ)
  [Invertible Sigma]
  [Invertible (X.transpose * Sigma⁻¹ * X)]
  (h_Sigma_21 : Sigma_21 = Sigma_12.transpose)
  (beta_hat : Matrix (Fin p) (Fin 1) ℝ)
  (h_beta_hat : beta_hat = (X.transpose * Sigma⁻¹ * X)⁻¹ * X.transpose * Sigma⁻¹ * y)
  -- The target predictive parameters given in the problem statement
  (target_mean : Matrix (Fin m) (Fin 1) ℝ)
  (h_target_mean : target_mean = X_tilde * beta_hat + Sigma_21 * Sigma⁻¹ * (y - X * beta_hat))
  (target_cov : Matrix (Fin m) (Fin m) ℝ)
  (h_target_cov : target_cov = Sigma_tilde - Sigma_21 * Sigma⁻¹ * Sigma_12)
  -- The theoretical properties of the conditional Gaussian distribution given beta
  (cond_mean_func : Matrix (Fin p) (Fin 1) ℝ → Matrix (Fin m) (Fin 1) ℝ)
  (h_cond_mean_func : ∀ b, cond_mean_func b = X_tilde * b + Sigma_21 * Sigma⁻¹ * (y - X * b))
  (cond_cov : Matrix (Fin m) (Fin m) ℝ)
  (h_cond_cov : cond_cov = Sigma_tilde - Sigma_21 * Sigma⁻¹ * Sigma_12) :
  -- Conclusion: The predictive parameters match the conditional parameters evaluated at beta_hat
  target_mean = cond_mean_func beta_hat ∧ target_cov = cond_cov := by
  sorry









theorem theorem_146253_problem (n : ℕ) (u : Fin n → Fin n → ℝ)
  (hn : n % 4 ≠ 0)
  (h_ortho : ∀ i j, ∑ k, u i k * u j k = if i = j then 1 else 0) :
  ∃ i, (∀ j, 0 ≤ u i j) ∨ (∀ j, u i j ≤ 0) := by
  sorry



theorem theorem_146240_problem
  (v : ℕ → (Fin 3 → ℝ))
  (h_base : LinearIndependent ℝ ![v 1, v 2])
  (h_step : ∀ n ≥ 2, ∀ i j, 1 ≤ i → i < j → j ≤ n →
    v (n + 1) ∉ Submodule.span ℝ {v i, v j}) :
  ∀ i j k, 1 ≤ i → i < j → j < k →
    LinearIndependent ℝ ![v i, v j, v k] := by
  sorry





theorem theorem_146262_problem
  {K : Type*} [Field K]
  {n : ℕ}
  (A B : Matrix (Fin n) (Fin n) K)
  (h : A * B = 0) :
  B.rank ≤ FiniteDimensional.finrank K (LinearMap.ker (Matrix.toLin' A)) := by
  sorry









theorem theorem_146490_problem
  (W : Type*) [AddCommGroup W] [Module ℝ W]
  (Λ : Set (Module.Dual ℝ W))
  (h_count : Λ.Countable)
  (h_cond : {φ | ∀ w : W, φ w = 0} ∩ Λ ⊆ {0}) :
  ∃ w : W, {φ | φ w = 0} ∩ Λ ⊆ {0} := by
  sorry











theorem theorem_147124_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : V →L[ℝ] V)
  (x₀ y : V)
  (ε : ℝ)
  (hy : y ≠ 0)
  (hε : ε > 0) :
  ‖(ε / (2 * ‖y‖)) • T y‖ ≤ ‖T x₀‖ + ‖(ε / (2 * ‖y‖)) • T y + T x₀‖ := by
  sorry



theorem theorem_146712_problem
  {m n p q R : Type*}
  [Fintype n] [Fintype p]
  [CommSemiring R]
  (A : Matrix m n R) (B : Matrix n p R) (C : Matrix p q R) :
  (A * B) * C = A * (B * C) ∧
  ∀ (i : m) (j : q), ((A * B) * C) i j = ∑ k : n, ∑ l : p, A i k * B k l * C l j := by
  sorry







theorem theorem_147206_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
  (A : E ≃L[ℝ] E) :
  sSup {x : ℝ | ∃ e b : E, e ≠ 0 ∧ b ≠ 0 ∧
    x = (‖A.symm e‖ / ‖e‖) * (‖b‖ / ‖A.symm b‖)} =
  ‖(A.symm : E →L[ℝ] E)‖ * ‖(A : E →L[ℝ] E)‖ := by
  sorry

theorem theorem_147353_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  (D : Submodule 𝕜 X)
  (A : D →ₗ[𝕜] X)
  (h_dense : Dense (D : Set X))
  (h_unbounded : ¬ ∃ M : ℝ, ∀ x : D, ‖A x‖ ≤ M * ‖x‖) :
  ¬ ∃ (B : X →L[𝕜] X), ∀ x : D, B x = A x := by
  sorry

theorem theorem_147102_problem (r a_r a_theta : ℝ)
  (a_r_phys a_theta_phys : ℝ)
  (h1 : a_r_phys = a_r)
  (h2 : a_theta_phys = r * a_theta) :
  Real.sqrt (a_r_phys ^ 2 + a_theta_phys ^ 2) = Real.sqrt (a_r ^ 2 + r ^ 2 * a_theta ^ 2) := by
  sorry

theorem theorem_147416_problem (M : Matrix (Fin 2) (Fin 2) ℤ)
  (a : Matrix (Fin 2) (Fin 1) ℤ)
  (b : Matrix (Fin 2) (Fin 1) ℤ)
  (hM : M = !![2, -1; -1, 2])
  (ha : a = !![1; 0])
  (hb : b = !![0; 0]) :
  M * a ≠ b := by
  sorry





theorem theorem_147695_problem :
  let delta : Fin 3 → Fin 3 → ℤ := fun i j => if i = j then 1 else 0
  let epsilon : Fin 3 → Fin 3 → Fin 3 → ℤ := fun i j k => Matrix.det (fun r c => delta r (![i, j, k] c))
  ∀ j k m n : Fin 3,
    ∑ i : Fin 3, epsilon i j k * epsilon i m n = delta j m * delta k n - delta j n * delta k m := by
  sorry



theorem theorem_147235_problem {K m n : Type*} [Field K] 
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  (M : Matrix m n K)
  (h1 : IsUnit (1 - M * M.transpose))
  (h2 : IsUnit (1 - M.transpose * M)) :
  (1 - M * M.transpose)⁻¹ * M = M * (1 - M.transpose * M)⁻¹ := by
  sorry



theorem theorem_147489_problem
  (k : Type*) [Field k]
  (M : Type*) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
  (hM : FiniteDimensional.finrank k M ≥ 1) :
  (∀ (N : Type*) [AddCommGroup N] [Module k N] [FiniteDimensional k N],
    FiniteDimensional.finrank k N ≥ 1 →
    (¬ ∃ (S : Submodule k N), S ≠ ⊤ ∧ FiniteDimensional.finrank k (N ⧸ S) < FiniteDimensional.finrank k N) ↔ 
    FiniteDimensional.finrank k N = 1) ∧
  (∀ (N : Type*) [AddCommGroup N] [Module k N] [FiniteDimensional k N],
    FiniteDimensional.finrank k N = 1 → IsSimpleModule k N) := by
  sorry



