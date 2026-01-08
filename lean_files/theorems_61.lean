import Mathlib
import Mathlib.Tactic



theorem theorem_327715_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (B : Set V)
  (hB_ind : LinearIndependent F ((↑) : B → V))
  (hB_span : Submodule.span F B = ⊤)
  (Y : Set V)
  (hY_ind : LinearIndependent F ((↑) : Y → V))
  (h_neq : Cardinal.mk Y ≠ Cardinal.mk B) :
  Cardinal.mk Y < Cardinal.mk B := by
  sorry































theorem theorem_328580_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (P G : V →ₗ[K] V)
  (hP : P ∘ₗ P = P) :
  ((∀ v ∈ LinearMap.range P, G v ∈ LinearMap.range P) ∧
   (∀ v ∈ LinearMap.ker P, G v ∈ LinearMap.ker P)) ↔
  P ∘ₗ G = G ∘ₗ P := by
  sorry

theorem theorem_328418_problem 
  (k : ℕ) 
  (ell : Fin k → ℝ) 
  (d : Fin k → ℕ) 
  (AIC_i : Fin k → ℝ)
  (h_AIC_i : ∀ i, AIC_i i = -2 * ell i + 2 * (d i : ℝ))
  (ell_joint : ℝ)
  (d_joint : ℕ)
  (h_ell_joint : ell_joint = ∑ i, ell i) 
  (h_d_joint : d_joint = ∑ i, d i) : 
  -2 * ell_joint + 2 * (d_joint : ℝ) = ∑ i, AIC_i i := by
  sorry



theorem theorem_328837_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (z : X) (hz : z ≠ 0)
  (Y : Submodule ℝ X) (hY : Y = Submodule.span ℝ {z})
  (f : Y →L[ℝ] ℝ)
  (h_def : ∀ (t : ℝ), f (t • ⟨z, hY.symm ▸ Submodule.mem_span_singleton_self z⟩) = t) :
  ∃ f_tilde : X →L[ℝ] ℝ, (∀ y : Y, f_tilde y = f y) ∧ ‖f_tilde‖ = ‖f‖ := by
  sorry

theorem theorem_328399_problem 
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix m n ℚ) (b : m → ℚ) :
  (∃ x : n → ℤ, Matrix.mulVec A (fun i => (x i : ℚ)) = b) ↔ 
  (∀ y : m → ℚ, (∀ j, ∃ k : ℤ, (Matrix.vecMul y A) j = k) → 
    ∃ k : ℤ, Matrix.dotProduct y b = k) := by
  sorry

theorem theorem_324111_problem
  (F : Type*) [Field F]
  (V : Type*) [AddCommGroup V] [Module F V]
  (W : Type*) [AddCommGroup W] [Module F W]
  (f : V →ₗ[F] W)
  (k : ℕ)
  (A_k : Submodule F V)
  (B_k : Submodule F W)
  (hA_dim : FiniteDimensional.finrank F A_k = k)
  (hB_dim : FiniteDimensional.finrank F B_k = k)
  (h_map : Submodule.map f A_k ≤ B_k)
  (h_strict : Submodule.map f A_k ≠ B_k) :
  ∀ n ≥ k, ∃ (A_succ : Submodule F V) (B_n : Submodule F W),
    FiniteDimensional.finrank F A_succ = n + 1 ∧
    FiniteDimensional.finrank F B_n = n ∧
    A_k ≤ A_succ ∧
    B_k ≤ B_n ∧
    Submodule.map f A_succ ≤ B_n ∧
    Submodule.map f A_succ ≠ B_n := by
  sorry





theorem theorem_328666_problem
  {R : Type*} [Field R]
  {n : Type*} [Fintype n] [DecidableEq n]
  {V : Type*} [AddCommGroup V] [Module R V]
  (L : V →ₗ[R] V)
  (b c : Basis n R V)
  (A : Matrix n n R)
  (hA : A = LinearMap.toMatrix b b L)
  (P : Matrix n n R)
  (hP : P = Basis.toMatrix b c) :
  LinearMap.toMatrix c c L = P⁻¹ * A * P := by
  sorry

theorem theorem_329016_problem
  {n : ℕ} {K : Type*} [Field K]
  (A : Matrix (Fin n) (Fin n) K)
  (h_singular : ¬ IsUnit A)
  (h_trace : Matrix.trace A = 0) :
  ∃ v : Fin n → K, v ≠ 0 ∧ Matrix.mulVec A v = 0 := by
  sorry



theorem theorem_328943_problem
  (n : ℕ)
  (V : Type*) [AddCommGroup V] [Module ℝ V]
  (f : (Fin n → ℝ) →ₗ[ℝ] V)
  (x : Fin n → ℝ)
  (PRF : Fin n → V)
  (hPRF : ∀ i, PRF i = f (Pi.single i 1)) :
  f x = ∑ i : Fin n, x i • PRF i := by
  sorry



theorem theorem_329237_problem (n : ℕ) (p : Polynomial ℝ)
  (h1 : p.degree ≤ n)
  (h2 : ∫ x in (0 : ℝ)..(1 : ℝ), (p.eval x) ^ 2 = 0) :
  p = 0 := by
  sorry

theorem theorem_329053_problem
  (x y : C(Set.Icc (0 : ℝ) 1, ℝ))
  (ε : ℝ)
  (hx_ball : ‖x‖ ≤ 1)
  (hy_ball : ‖y‖ ≤ 1)
  (hx_val : x ⟨0.25, by norm_num⟩ = 1)
  (hy_val : y ⟨0.25, by norm_num⟩ = 1)
  (hε : ε > 0)
  (h_diff : |x ⟨0.75, by norm_num⟩ - y ⟨0.75, by norm_num⟩| ≥ ε) :
  1 - ‖x + y‖ / 2 = 0 := by
  sorry







theorem theorem_329630_problem :
  ∃ (K : Type) (instK : NontriviallyNormedField K)
    (V : Type) (instV : NormedAddCommGroup V) (instVS : NormedSpace K V)
    (A : V →ₗ[K] V) (e : V),
    let W := Submodule.span K (Set.range (fun n : ℕ => (A ^ n) e))
    ¬ IsClosed (W : Set V) := by
  sorry





theorem theorem_329531_problem
  (F : Type*) [Field F]
  (V : Type*) [AddCommGroup V] [Module F V]
  (n : ℕ)
  (e : Basis (Fin n) F V)
  (B : Subgroup (V ≃ₗ[F] V))
  (hB : ∀ T : V ≃ₗ[F] V, T ∈ B ↔ ∀ k : Fin n,
    Submodule.map (T : V →ₗ[F] V) (Submodule.span F (e '' {i | i ≤ k})) =
    Submodule.span F (e '' {i | i ≤ k})) :
  Subgroup.normalizer B = B := by
  sorry

theorem theorem_329703_problem
  (n : ℕ) (hn : 1 < n)
  (x : Fin n → ℝ)
  (x_bar : ℝ) (h_x_bar : x_bar = (1 / (n : ℝ)) * ∑ i, x i)
  (X : Fin n → ℝ) (h_X : X = fun _ ↦ x_bar)
  (f : (Fin n → ℝ) → ℝ)
  (h_f : ∀ v, f v = (1 / ((n : ℝ) - 1)) * ∑ i, (v i)^2) :
  f x = f X + f (x - X) := by
  sorry













theorem theorem_329819_problem (θ : ℝ) (h : 1 + Real.cos θ ≠ 0) :
  let i : Fin 3 → ℝ := Pi.single 0 1
  let j : Fin 3 → ℝ := Pi.single 1 1
  (Real.cos θ • j - Real.sin θ • i) + 
  (Real.sin θ / (1 + Real.cos θ)) • ((1 + Real.cos θ) • i + Real.sin θ • j) = j := by
  sorry





theorem theorem_330478_problem
  (n : ℕ)
  (b : Basis (Fin n) ℝ (Fin n → ℝ))
  (S : Set (Fin n → ℝ))
  (hS_symm : ∀ x ∈ S, -x ∈ S)
  (hS_convex : Convex ℝ S)
  (h_vol : ENNReal.ofReal ((2 : ℝ) ^ n * |Matrix.det (fun i j => b j i)|) < MeasureTheory.volume S) :
  ∃ v ∈ Submodule.span ℤ (Set.range b), v ∈ S ∧ v ≠ 0 := by
  sorry

theorem theorem_330557_problem
  (n : ℕ)
  (T : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
  (h : ∃ X Y : Matrix (Fin n) (Fin n) ℝ, Matrix.trace X = Matrix.trace Y ∧ Matrix.trace (T X) ≠ Matrix.trace (T Y)) :
  ¬ ∃ f : ℝ → ℝ, ∀ A : Matrix (Fin n) (Fin n) ℝ, Matrix.trace (T A) = f (Matrix.trace A) := by
  sorry











theorem theorem_329888_problem
  (n d : ℕ)
  (A S₁ S₂ : Matrix (Fin n) (Fin d) ℝ)
  (G₁ G₂ : Matrix (Fin d) (Fin d) ℝ)
  (R : Matrix (Fin n) (Fin n) ℝ)
  (hA : A.transpose * A = 1)
  (hS₁ : S₁ = A * G₁)
  (hS₂ : S₂ = A * G₂)
  (hG₁ : Invertible G₁)
  (hR : R * S₁ = S₂) :
  A.transpose * R * A = G₂ * G₁⁻¹ := by
  sorry



theorem theorem_330688_problem (a b : Fin 2 → ℂ) :
  let swap := TensorProduct.comm ℂ (Fin 2 → ℂ) (Fin 2 → ℂ)
  let t := a ⊗ₜ[ℂ] b
  let S := (1 / 2 : ℂ) • (t + swap t)
  let A := (1 / 2 : ℂ) • (t - swap t)
  -- 1. The tensor is the sum of the symmetric and antisymmetric parts
  t = S + A ∧
  -- 2. The first part is symmetric (in S^2)
  swap S = S ∧
  -- 3. The second part is antisymmetric (in Λ^2)
  swap A = -A ∧
  -- 4. The decomposition is unique
  ∀ s' a', swap s' = s' → swap a' = -a' → s' + a' = t → s' = S ∧ a' = A := by
  sorry









theorem theorem_330807_problem
  (N p : ℕ)
  (hN : N > 0)
  (hp : p > 0)
  (Y : Fin N → Fin 3 → ℝ)
  (X : Fin N → Fin 3 → Fin p → ℝ)
  (β : Fin p → ℝ)
  (β₀ : ℝ)
  (γ : Fin N → ℝ)
  (ε : Fin N → Fin 3 → ℝ)
  (σ_γ_sq σ_ε_sq : ℝ)
  (IsNormal : ℝ → ℝ → ℝ → Prop)
  (h_model : ∀ i j, Y i j = β₀ + (∑ k, β k * X i j k) + γ i + ε i j)
  (h_gamma_dist : ∀ i, IsNormal (γ i) 0 σ_γ_sq)
  (h_epsilon_dist : ∀ i j, IsNormal (ε i j) 0 σ_ε_sq)
  (EstimationMethod : Type)
  (REML : EstimationMethod)
  (is_optimal_fixed_effects : EstimationMethod → Prop) :
  is_optimal_fixed_effects REML := by
  sorry

theorem theorem_330618_problem
  {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  (T : X →ₗ[ℝ] Y)
  (h_graph_closed : IsClosed {p : X × Y | p.2 = T p.1}) :
  Continuous T := by
  sorry



theorem theorem_330963_problem
  (n m : ℕ)
  (V : Matrix (Fin m) (Fin m) ℝ)
  (Ω : Type*)
  (E : (Ω → ℝ) → ℝ)
  -- Linearity of Expectation
  (hE_linear : ∀ (a b : ℝ) (f g : Ω → ℝ), E (fun ω => a * f ω + b * g ω) = a * E f + b * E g)
  -- X is a random matrix
  (X : Matrix (Fin n) (Fin m) (Ω → ℝ))
  -- Conditions: entries have mean 0 and are uncorrelated with variance 1 (Standard Normal assumption)
  (h_mean : ∀ (i : Fin n) (j : Fin m), E (X i j) = 0)
  (h_cov : ∀ (i k : Fin n) (j l : Fin m), E (fun ω => X i j ω * X k l ω) = if i = k ∧ j = l then 1 else 0) :
  -- Define the matrix product X V^T V X^T in the random variable space
  let V_rv := V.map (fun x => (fun _ : Ω => x))
  let A := X * V_rv.transpose * V_rv * X.transpose
  -- The expected matrix is the element-wise expectation of A
  let ExpA := Matrix.of (fun i j => E (A i j))
  -- Conclusion: E[X V^T V X^T] = Tr(V^T V) * I_n
  ExpA = (Matrix.trace (V.transpose * V)) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  sorry



theorem theorem_331012_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (ψ : X →L[ℝ] ℝ)
  (hψ : ‖ψ‖ = 1) :
  ∃ x : X, ‖x‖ = 1 ∧ ψ x > 3 / 4 := by
  sorry



theorem theorem_331335_problem
  {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (f : H →L[𝕜] 𝕜) (hf : f ≠ 0) (x : H) :
  ‖f x‖ ≤ ‖x‖ * ‖f‖ := by
  sorry







theorem theorem_331505_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (A : H →L[ℂ] H)
  (h_sa : IsSelfAdjoint A)
  (h_pos : 0 ≤ A)
  (h_inj : Function.Injective A)
  (h_not_surj : ¬ Function.Surjective A) :
  LinearMap.range A ≠ LinearMap.range (A ^ 2) := by
  sorry



theorem theorem_330903_problem (n : ℕ) 
  (J : Matrix (Fin n) (Fin n) ℝ)
  (σ : Equiv.Perm (Fin n))
  (J_reordered : Matrix (Fin n) (Fin n) ℝ)
  (h_reordered : ∀ i j, J_reordered i j = J i (σ j)) :
  J_reordered.det = (Equiv.Perm.sign σ : ℝ) * J.det := by
  sorry



















theorem theorem_332283_problem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x y : E) :
  ‖x‖ + ‖y‖ - ‖x + y‖ ≤ ‖x - y‖ := by
  sorry





theorem theorem_332427_problem
  (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (β : ℝ)
  (hβ : 0 < β)
  (hf : ContDiff ℝ ⊤ f)
  (h_lip : ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 → ‖gradient f (x + v) - gradient f x‖ / ‖v‖ ≤ β) :
  ∀ (k : ℝ), Module.End.HasEigenvalue (ContinuousLinearMap.toLinearMap (fderiv ℝ (gradient f) x)) k → |k| ≤ β := by
  sorry









theorem theorem_332762_problem
  (f T : (Fin 2 → ℝ) → (Fin 2 → ℝ))
  (hf : Differentiable ℝ f)
  (hT : Differentiable ℝ T)
  (hJf : ∀ x, fderiv ℝ f x = 0) :
  ∀ x, fderiv ℝ (T ∘ f) x = 0 := by
  sorry

theorem theorem_332709_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (x_seq : ℕ → X) (x : X)
  (f_seq : ℕ → NormedSpace.Dual 𝕜 X) (f : NormedSpace.Dual 𝕜 X)
  (h_x_lim : Filter.Tendsto x_seq Filter.atTop (nhds x))
  (h_f_lim : ∀ y, Filter.Tendsto (fun n => f_seq n y) Filter.atTop (nhds (f y))) :
  Filter.Tendsto (fun n => f_seq n (x_seq n)) Filter.atTop (nhds (f x)) := by
  sorry









