import Mathlib
import Mathlib.Tactic















theorem theorem_351602_problem
  (n : ℕ)
  (V : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℝ → EuclideanSpace ℝ (Fin n))
  (hV : Differentiable ℝ V)
  (hx : Differentiable ℝ x) :
  ∀ t : ℝ, deriv (V ∘ x) t = inner (gradient V (x t)) (deriv x t) := by
  sorry







theorem theorem_351926_problem
  (n : ℕ)
  {K : Type*} [Field K]
  (A Z : Matrix (Fin n) (Fin n) K)
  (lam : K)
  (hZ : IsUnit Z) :
  Z⁻¹ * A * Z - lam • (1 : Matrix (Fin n) (Fin n) K) = Z⁻¹ * (A - lam • (1 : Matrix (Fin n) (Fin n) K)) * Z := by
  sorry







theorem theorem_351749_problem
  (T N B : Fin 3 → ℝ)
  (h_orth_TN : Matrix.dotProduct T N = 0)
  (h_orth_NB : Matrix.dotProduct N B = 0)
  (h_orth_TB : Matrix.dotProduct T B = 0)
  (h_T_nz : T ≠ 0)
  (h_N_norm : Matrix.dotProduct N N = 1)
  (h_cross : crossProduct T N = B)
  (h_B_nz : B ≠ 0) :
  LinearIndependent ℝ ![T, N, B] ∧ Submodule.span ℝ (Set.range ![T, N, B]) = ⊤ := by
  sorry



theorem theorem_352380_problem
  {K : Type*} [Field K]
  {n : ℕ}
  (A B : Matrix (Fin n) (Fin n) K)
  (beta : K)
  (hA : IsUnit A)
  (hB : IsUnit B)
  (hbeta : beta ≠ 0) :
  A = beta • B ↔ A * B⁻¹ = beta • (1 : Matrix (Fin n) (Fin n) K) := by
  sorry











theorem theorem_352653_problem (N r : ℕ)
  (A : Matrix (Fin N) (Fin N) ℝ)
  (C : Matrix (Fin N) (Fin r) ℝ)
  (F : Matrix (Fin r) (Fin N) ℝ)
  (B : Matrix (Fin N) (Fin N) ℝ)
  (h : A = C * F) :
  Matrix.trace (B * A) = Matrix.trace (F * B * C) := by
  sorry



theorem theorem_352401_problem (n : ℕ)
  (R S : Matrix (Fin n) (Fin n) ℝ)
  (a : Matrix (Fin n) (Fin 1) ℝ)
  (h1 : S * a = a)
  (h2 : R.transpose * a = a) :
  a.transpose * R * S * a = a.transpose * a := by
  sorry





theorem theorem_352449_problem
  (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (T : V ≃L[ℝ] V) :
  ∀ (f g : V →L[ℝ] ℝ), f ≠ 0 → g ≠ 0 →
  ContDiffOn ℝ ⊤ (fun u => (g (T u))⁻¹ • T u) {u : V | f u = 1 ∧ g (T u) ≠ 0} := by
  sorry







theorem theorem_353160_problem :
  ∃ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian),
    let evA := List.mergeSort (· ≥ ·) (List.ofFn (hA.eigenvalues))
    let evB := List.mergeSort (· ≥ ·) (List.ofFn (hB.eigenvalues))
    (∀ x ∈ List.zip evA evB, x.1 ≥ x.2) ∧ ¬ (A - B).PosSemidef := by
  sorry



theorem theorem_353217_problem
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (A : E → E)
  (M₁ M₂ : Set ℝ)
  (h₁ : M₁ = { v | ∃ x : E, x ≠ 0 ∧ v = ‖A (‖x‖⁻¹ • x)‖ })
  (h₂ : M₂ = { v | ∃ x : E, 0 < ‖x‖ ∧ ‖x‖ ≤ 1 ∧ v = ‖A (‖x‖⁻¹ • x)‖ }) :
  M₁ = M₂ := by
  sorry







theorem theorem_353892_problem
  (n : ℕ)
  (f : ℝ → EuclideanSpace ℝ (Fin n))
  (h_smooth : ContDiff ℝ ⊤ f)
  (h_norm : ∀ t : ℝ, ‖f t‖ ^ 2 = 1) :
  ∀ t : ℝ, inner (f t) (deriv f t) = (0 : ℝ) := by
  sorry

theorem theorem_353057_problem
  (x₁ x₂ x₃ x₄ : ℝ)
  (a b c d : ℝ)
  (ha : a = -2 * x₁ - 7 * x₂ - 5 * x₃ - 8 * x₄)
  (hb : b = -6 * x₁ + 5 * x₂ - 2 * x₃ + 2 * x₄)
  (hc : c = 9 * x₁ - 14 * x₂ - 10 * x₃ - 3 * x₄)
  (hd : d = -5 * x₁ + 15 * x₂ + 7 * x₃ + 6 * x₄) :
  (a + 2 * c - 2 * b + 3 * d) ^ 3 + (2 * a - b + 2 * c + 4 * d) ^ 3 -
  (a + b + 2 * c + 2 * d) ^ 3 - (3 * a - 2 * b + c + 3 * d) ^ 3 = 0 ↔
  x₁ ^ 3 + x₂ ^ 3 + x₃ ^ 3 + x₄ ^ 3 = 0 := by
  sorry



theorem theorem_353590_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (f : V →ₗ[ℝ] ℝ) :
  sSup ((fun x => |f x| / ‖x‖) '' {x | x ≠ 0}) = sSup ((fun x => |f x|) '' {x | ‖x‖ = 1}) := by
  sorry



theorem theorem_353935_problem
  {n : ℕ}
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  (e : Basis (Fin n) F V)
  (A : Matrix (Fin n) (Fin n) F)
  (f : Fin n → Module.Dual F V)
  (h_def : ∀ (i : Fin n) (x : V), f i x = ∑ j : Fin n, A i j * e.repr x j) :
  ∀ i : Fin n, f i = ∑ j : Fin n, A i j • e.coord j := by
  sorry



theorem theorem_353609_problem
  {X : Type*}
  (f : ℕ → X → ℝ)
  (h : ∀ (s : ℕ →₀ ℝ), (∀ x, s.sum (λ i c ↦ c * f i x) = 0) → s = 0) :
  LinearIndependent ℝ f := by
  sorry

theorem theorem_353800_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (a b : H →L[ℂ] H)
  (h_pos : 0 ≤ a)
  (h_bound : 0 ≤ algebraMap ℝ (H →L[ℂ] H) ‖b‖ - a) :
  spectralRadius ℂ a ≤ ENNReal.ofReal ‖b‖ := by
  sorry



theorem theorem_353915_problem (g : ℕ → ℝ → ℝ)
  (h_def : ∀ n, ∀ x ∈ Set.Icc (0 : ℝ) 1, g n x = if x = 1 then 0 else x ^ n) :
  ¬ TendstoUniformlyOn g 0 Filter.atTop (Set.Icc 0 1) := by
  sorry

theorem theorem_353546_problem
  {U : Type*} [AddCommGroup U] [Module ℝ U]
  (Φ : LinearMap.BilinForm ℝ U)
  (h_symm : Φ.IsSymm)
  (m : ℕ)
  (e : Fin m → U)
  (h_e_ortho : ∀ i j, i ≠ j → Φ (e i) (e j) = 0)
  (w : U)
  (h_w_ortho : ∀ v ∈ Submodule.span ℝ (Set.range e), Φ v w = 0) :
  ∀ j : Fin m, Φ (e j) w = 0 := by
  sorry







theorem theorem_354098_problem
  (n r : ℕ)
  (a b : ℝ)
  (M : ℝ → Matrix (Fin n) (Fin n) ℝ)
  (h_cont : ContinuousOn M (Set.Ioo a b))
  (h_rank : ∀ x ∈ Set.Ioo a b, (M x).rank = r) :
  ∃ v : Fin (n - r) → ℝ → (Fin n → ℝ),
    (∀ i, ContinuousOn (v i) (Set.Ioo a b)) ∧
    (∀ x ∈ Set.Ioo a b,
      LinearIndependent ℝ (λ i ↦ v i x) ∧
      Submodule.span ℝ (Set.range (λ i ↦ v i x)) = LinearMap.ker (Matrix.toLin' (M x))) := by
  sorry







theorem theorem_354434_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (grad_f : V →L[ℝ] W)
  (L : ℝ)
  (hL : L = sSup {k : ℝ | ∃ x : V, x ≠ 0 ∧ k = ‖grad_f x‖ / ‖x‖}) :
  ∀ x : V, ‖grad_f x‖ ≤ L * ‖x‖ := by
  sorry

theorem theorem_354957_problem
  {K : Type*} [Field K]
  {m n p : ℕ}
  (A : Matrix (Fin m) (Fin n) K)
  (B : Matrix (Fin n) (Fin p) K)
  (h : A.rank = n) :
  (A * B).rank = B.rank := by
  sorry







theorem theorem_355149_problem (n : ℕ)
  (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (h : ∀ x y, ‖T x + T y‖ = ‖x + y‖) :
  IsLinearMap ℝ T := by
  sorry





theorem theorem_355585_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : ∑ i, ∑ j, A i j = 0)
  (x : Fin n → ℝ)
  (hx : ∀ i, x i = ∑ j, A i j)
  (ones : Fin n → ℝ)
  (hones : ∀ i, ones i = 1) :
  Matrix.dotProduct x ones = 0 := by
  sorry

theorem theorem_355362_problem
  {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  (I : Set ℝ)
  (f : ℕ → ℝ → E)
  (M : ℕ → ℝ)
  (hM_nonneg : ∀ n, 0 ≤ M n)
  (h_bound : ∀ x ∈ I, ∀ n, ‖f n x‖ ≤ M n)
  (h_conv : Summable M) :
  TendstoUniformlyOn (fun N x ↦ ∑ n in Finset.range N, f n x) (fun x ↦ ∑' n, f n x) atTop I := by
  sorry





theorem theorem_355107_problem (n : ℕ) (u : (Fin n → ℝ) → ℝ)
  (h_diff : ContDiff ℝ 2 u) (h_supp : HasCompactSupport u) :
  ∫ x, (∑ i : Fin n, fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1)) ^ 2 =
  ∫ x, ∑ i : Fin n, ∑ j : Fin n, (fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single j 1)) ^ 2 := by
  sorry











theorem theorem_356309_problem
  (n : ℕ)
  (A₁ : Matrix (Fin n) (Fin n) ℝ)
  (d x : Matrix (Fin n) (Fin 1) ℝ) :
  d.transpose * A₁ * x = x.transpose * A₁.transpose * d := by
  sorry

theorem theorem_356426_problem (n : ℕ) (x : Fin n → ℝ) (hn : n ≠ 0) :
  Filter.Tendsto (fun p : ℝ ↦ (∑ i, |x i| ^ p) ^ (1 / p)) Filter.atTop (nhds (⨆ i, |x i|)) := by
  sorry



theorem theorem_356295_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (Y : Submodule 𝕜 X)
  (f : X →L[𝕜] 𝕜) :
  ‖f.comp Y.subtypeL‖ ≤ ‖f‖ := by
  sorry

theorem theorem_356279_problem
  (p : ℕ)
  (hp : 2 ≤ p)
  (beta_0 beta_1 : ℝ)
  (beta gamma : ℕ → ℝ)
  (model : (ℕ → ℝ) → ℝ)
  (h_model : ∀ x, model x = beta_0 + beta_1 * (x 1) +
    (∑ j in Finset.Icc 2 p, beta j * (x j)) +
    (∑ j in Finset.Icc 2 p, gamma j * (x 1) * (x j))) :
  (∀ x y : ℕ → ℝ, (∀ j ∈ Finset.Icc 2 p, x j = y j) → model x = model y) ↔
  (beta_1 = 0 ∧ ∀ j ∈ Finset.Icc 2 p, gamma j = 0) := by
  sorry

theorem theorem_356174_problem
  {K : Type*} [Field K]
  {ι₁ ι₂ κ₁ κ₂ : Type*}
  [Fintype ι₁] [DecidableEq ι₁]
  [Fintype ι₂] [DecidableEq ι₂]
  [Fintype κ₁] [DecidableEq κ₁]
  [Fintype κ₂] [DecidableEq κ₂]
  {V₁ V₂ W₁ W₂ : Type*}
  [AddCommGroup V₁] [Module K V₁]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup W₁] [Module K W₁]
  [AddCommGroup W₂] [Module K W₂]
  (f₁ : V₁ →ₗ[K] W₁) (f₂ : V₂ →ₗ[K] W₂)
  (bV₁ : Basis ι₁ K V₁) (bW₁ : Basis κ₁ K W₁)
  (bV₂ : Basis ι₂ K V₂) (bW₂ : Basis κ₂ K W₂)
  (A : Matrix κ₁ ι₁ K) (B : Matrix κ₂ ι₂ K)
  (hA : A = LinearMap.toMatrix bV₁ bW₁ f₁)
  (hB : B = LinearMap.toMatrix bV₂ bW₂ f₂) :
  LinearMap.toMatrix (Basis.tensorProduct bV₁ bV₂) (Basis.tensorProduct bW₁ bW₂) (TensorProduct.map f₁ f₂) =
  Matrix.kronecker A B := by
  sorry

theorem theorem_356445_problem (f : ℂ → ℝ)
  (h_cont : Continuous f)
  (h_entire : Differentiable ℂ (fun z => Complex.exp (↑(f z) * Complex.I)))
  (h_bounded : ∃ M : ℝ, ∀ z : ℂ, Complex.abs (Complex.exp (↑(f z) * Complex.I)) ≤ M) :
  ∃ c : ℝ, ∀ z : ℂ, f z = c := by
  sorry

theorem theorem_356845_problem (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (C : Matrix (Fin n) (Fin n) ℝ)
  (X Y : Matrix (Fin n) (Fin 1) ℝ)
  (hA : A.IsSymm)
  (hC : Invertible C)
  (hX : X = C * Y) :
  X.transpose * A * X = Y.transpose * (C.transpose * A * C) * Y := by
  sorry

theorem theorem_356454_problem
  (r : ℕ → ℝ)
  (h_r : ∀ n, ¬ Irrational (r n)) :
  let f := fun (x : ℝ) ↦ ∑' n : ℕ, (1 / (2 : ℝ) ^ (n + 1)) * (if r n < x then 1 else 0)
  ∀ x₀, Irrational x₀ → ContinuousAt f x₀ := by
  sorry





theorem theorem_355941_problem
  (n : ℕ)
  (a b : ℝ)
  (F : ℝ × ℝ → (Fin n → ℝ))
  (Ω : Set (Fin n → ℝ))
  (hF : ContinuousOn F (Set.Icc 0 1 ×ˢ Set.Icc a b))
  (hΩ : IsOpen Ω)
  (h_sub : F '' (Set.Icc 0 1 ×ˢ Set.Icc a b) ⊆ Ω) :
  ∀ p ∈ F '' (Set.Icc 0 1 ×ˢ Set.Icc a b), ∃ ε > 0, Metric.ball p (3 * ε) ⊆ Ω := by
  sorry









theorem theorem_356788_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (r : ℝ → E) (t : ℝ)
  (h_diff : DifferentiableAt ℝ r t)
  (h_nz : r t ≠ 0) :
  deriv (fun s => (‖r s‖)⁻¹) t = - (inner (r t) (deriv r t)) / (‖r t‖ ^ 3) := by
  sorry



theorem theorem_357032_problem
  (f : EuclideanSpace ℝ (Fin 3) → ℝ)
  (v : EuclideanSpace ℝ (Fin 3))
  (a : EuclideanSpace ℝ (Fin 3))
  (h_diff : DifferentiableAt ℝ f a) :
  deriv (fun t : ℝ => f (a + t • v)) 0 = inner (gradient f a) v := by
  sorry



theorem theorem_356968_problem (f : ℂ → ℂ)
  (h_entire : Differentiable ℂ f)
  (h_bounded : ∃ M : ℝ, 0 < M ∧ ∀ z : ℂ, Complex.abs (f z) ≤ M) :
  ∃ c : ℂ, ∀ z : ℂ, f z = c := by
  sorry









