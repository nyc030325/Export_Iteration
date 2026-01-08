import Mathlib
import Mathlib.Tactic



theorem theorem_405625_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (A : Matrix n n ℝ)
  (hA : A.PosDef) :
  (Matrix.hadamard A A).PosDef := by
  sorry





theorem theorem_405752_problem
  (m n : ℕ)
  (a : Fin m → ℝ)
  (c : Fin n → Fin m → ℝ)
  (x : Fin n → ℝ)
  (t : ℝ)
  (h_c_nonneg : ∀ i j, 0 ≤ c i j)
  (h_x : ∀ i, x i = ∑ j, c i j * a j) :
  (∀ i, t ≤ x i) ↔ (∀ i, t ≤ ∑ j, c i j * a j) := by
  sorry

theorem theorem_406445_problem
  (F : Type*) [Field F]
  (V : Type*) [AddCommGroup V]
  [Module F V]
  [Module (Polynomial F) V]
  [IsScalarTower F (Polynomial F) V]
  (h_fin : FiniteDimensional F V) :
  Module.Free (Polynomial F) V ↔ Subsingleton V := by
  sorry

theorem theorem_406332_problem (ι : Type*) (b : Basis ι ℚ (ℂ × ℂ)) :
  ¬ Countable ι := by
  sorry



theorem theorem_406583_problem
  {R : Type*} [CommRing R]
  (avg : R → R)
  (ui uj ui_bar uj_bar ui_prime uj_prime : R)
  (h_decomp_i : ui = ui_bar + ui_prime)
  (h_decomp_j : uj = uj_bar + uj_prime)
  (h_linear : ∀ x y, avg (x + y) = avg x + avg y)
  (h_avg_ui_prime : avg ui_prime = 0)
  (h_avg_uj_prime : avg uj_prime = 0)
  (h_avg_means : avg (ui_bar * uj_bar) = ui_bar * uj_bar)
  (h_avg_mix_1 : avg (ui_bar * uj_prime) = ui_bar * avg uj_prime)
  (h_avg_mix_2 : avg (ui_prime * uj_bar) = avg ui_prime * uj_bar) :
  avg (ui * uj) = ui_bar * uj_bar + avg (ui_prime * uj_prime) := by
  sorry





theorem theorem_406420_problem (A B : Matrix (Fin 2) (Fin 2) ℝ)
  (h_tr : A.trace = B.trace)
  (h_det : A.det = B.det)
  (k : ℕ) :
  (A ^ k).trace = (B ^ k).trace := by
  sorry

theorem theorem_406678_problem (x y z : ℝ) :
  let A : Matrix (Fin 3) (Fin 3) ℝ := !![1, 2*x, x^2; 1, 2*y, y^2; 1, 2*z, z^2]
  let B : Matrix (Fin 3) (Fin 3) ℝ := !![1, x, x^2; 1, y, y^2; 1, z, z^2]
  Matrix.det (A * B.transpose) = 2 * (x - y)^2 * (y - z)^2 * (z - x)^2 := by
  sorry

theorem theorem_406423_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (l : X →ₗ[ℝ] ℝ)
  (hl_disc : ¬ Continuous l)
  (f : X → ℝ)
  (hf : ∀ x, f x = ‖x‖^2 - l x)
  (x₀ : X)
  (ε : ℝ)
  (hε : 0 < ε) :
  ¬ BddBelow (f '' Metric.ball x₀ ε) := by
  sorry







theorem theorem_406780_problem
  (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x d : EuclideanSpace ℝ (Fin n))
  (hf : Differentiable ℝ f)
  (g : ℝ → EuclideanSpace ℝ (Fin n))
  (hg : g = fun α ↦ x + α • d)
  (ϕ : ℝ → ℝ)
  (hϕ : ϕ = fun α ↦ f (g α)) :
  ∀ α, deriv ϕ α = inner (gradient f (g α)) d := by
  sorry

theorem theorem_406960_problem
  (K : Set ℝ)
  (hK : IsCompact K)
  (f : ℕ → ℝ → ℝ)
  (h_cont : ∀ n, ContinuousOn (f n) K)
  (h_nonneg : ∀ n, ∀ x ∈ K, 0 ≤ f n x)
  (h_mono : ∀ n, ∀ x ∈ K, f (n + 1) x ≤ f n x)
  (h_pointwise : ∀ x ∈ K, Filter.Tendsto (fun n ↦ f n x) Filter.atTop (nhds 0)) :
  TendstoUniformlyOn f 0 Filter.atTop K := by
  sorry



theorem theorem_406967_problem
  {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]
  (T₁ T₂ : V →ₗ[F] W)
  (h : FiniteDimensional.finrank F (LinearMap.range T₁) =
       FiniteDimensional.finrank F (LinearMap.range T₂)) :
  ∃ (φ : V ≃ₗ[F] V) (ψ : W ≃ₗ[F] W), T₁ = ψ.toLinearMap ∘ₗ T₂ ∘ₗ φ.toLinearMap := by
  sorry

theorem theorem_406692_problem (n : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℝ)) :
  IsClosed (G : Set (Matrix.GeneralLinearGroup (Fin n) ℝ)) ↔
  ∀ (A : ℕ → Matrix.GeneralLinearGroup (Fin n) ℝ) (L : Matrix.GeneralLinearGroup (Fin n) ℝ),
    (∀ i, A i ∈ G) → Filter.Tendsto A Filter.atTop (nhds L) → L ∈ G := by
  sorry







theorem theorem_407183_problem
  {m n R : Type*} [CommRing R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (C D E F : Matrix m n R)
  (x' x'' : n → R)
  (y' y'' : m → R)
  (A : Matrix (m ⊕ m) (n ⊕ n) R)
  (x : n ⊕ n → R)
  (y : m ⊕ m → R)
  (hA : A = Matrix.fromBlocks C D E F)
  (hx : x = Sum.elim x' x'')
  (hy : y = Sum.elim y' y'')
  (hAx : A.mulVec x = y)
  (hD : D = 0)
  (hE : E = 0)
  (hCF : C = F) :
  ∃ B : Matrix m n R, B = C ∧ B.mulVec x' = y' ∧ B.mulVec x'' = y'' := by
  sorry









theorem theorem_407525_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (B : V →ₗ[K] V →ₗ[K] K) -- Bilinear form (·, ·)
  (A : V →ₗ[K] V)        -- Linear operator A
  (h_symm : ∀ (x y : V), B x y = B y x) -- Symmetry of the bilinear form
  (h_ortho : ∀ (x : V), B (A x) x = 0)  -- Hypothesis (Ax, x) = 0
  (x y : V) :
  B (A x) y + B x (A y) = 0 := by
  sorry







theorem theorem_407534_problem
  (N n : ℕ)
  (F : Matrix (Fin N) (Fin N) ℝ × (Fin n → ℝ) → ℝ)
  (M : Set (Matrix (Fin N) (Fin N) ℝ))
  (S : Set (Fin n → ℝ))
  (D : Set (Matrix (Fin N) (Fin N) ℝ × (Fin n → ℝ)))
  (hM : M = {A | ∀ i j, A i j = 0 ∨ A i j = 1})
  (hS : S = Set.pi Set.univ (fun _ ↦ Set.Icc 0 (2 * Real.pi)))
  (hD : D = M ×ˢ S)
  (hF_cont : ContinuousOn F D)
  (h_compact : IsCompact D) :
  ∃ p ∈ D, ∀ q ∈ D, F q ≤ F p := by
  sorry

theorem theorem_408006_problem
  {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
  (a : ℕ → V)
  (h : Summable (fun n => ‖a n‖)) :
  Summable a := by
  sorry







theorem theorem_407148_problem
  (n p : ℕ)
  (hn : 0 < n)
  (X : Matrix (Fin n) (Fin p) ℝ)
  (r : Fin n → ℝ)
  -- Condition: r is the residual vector from OLS (Orthogonality)
  (h_resid : ∀ j, ∑ i, X i j * r i = 0)
  -- Condition: OLS regression with an intercept (Existence of a column of ones)
  (h_intercept : ∃ k, ∀ i, X i k = 1) :
  -- Conclusion: cov(X_j, r) = 0 for all j
  ∀ j, let mean_Xj := (∑ i, X i j) / (n : ℝ)
       let mean_r := (∑ i, r i) / (n : ℝ)
       (1 / (n : ℝ)) * ∑ i, (X i j - mean_Xj) * (r i - mean_r) = 0 := by
  sorry

theorem theorem_407530_problem (A B C : ℂ) (lam : ℝ) 
  (F G H : ℂ)
  (hF : F = A + (lam : ℂ) * Complex.I * (C - A))
  (hG : G = B - (lam : ℂ) * Complex.I * (C - B))
  (hH : H = (F + G) / 2) :
  H = (1 / 2 : ℂ) * (A + B) + ((lam : ℂ) * Complex.I / 2) * (B - A) := by
  sorry









theorem theorem_407562_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (Y : Submodule ℝ X)
  (hY_closed : IsClosed (Y : Set X))
  (hY_proper : Y ≠ ⊤)
  (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1) :
  ∃ x : X, ‖x‖ = 1 ∧ ∀ y ∈ Y, ‖x - y‖ > α := by
  sorry



theorem theorem_408464_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (h_symm : A.IsSymm)
  (h_posdef : A.PosDef) :
  ∀ i : Fin n, 0 < A i i := by
  sorry





theorem theorem_407652_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ≠ 0) :
  let D := Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) ℝ) A A.transpose 0
  ¬ D.PosSemidef := by
  sorry



















theorem theorem_408624_problem (x : EuclideanSpace ℝ (Fin 2))
  (a : EuclideanSpace ℝ (Fin 2))
  (h1 : a 0 = 1)
  (h2 : a 1 = -2) :
  |x 0 - 2 * x 1| ≤ ‖a‖ * ‖x‖ := by
  sorry

theorem theorem_408388_problem (ε : ℝ) (hε : ε > 0) :
  ∃ m n : ℤ,
    let P_x := ((m : ℝ) + (n : ℝ) * Real.sqrt 2) / 3
    let P_y := ((m : ℝ) * Real.sqrt 2 + 2 * (n : ℝ)) / 3
    Real.sqrt (P_x ^ 2 + P_y ^ 2) < ε := by
  sorry

theorem theorem_409087_problem
  (d : ℝ → ℝ → ℝ)
  (m : MetricSpace ℝ)
  (h_dist : d = @dist ℝ m.toPseudoMetricSpace.toDist)
  (h_not_complete : ¬ @CompleteSpace ℝ m.toUniformSpace) :
  ¬ ∃ (n : ℝ → ℝ),
    (∀ x, n x = 0 ↔ x = 0) ∧
    (∀ (c : ℝ) x, n (c * x) = |c| * n x) ∧
    (∀ x y, n (x + y) ≤ n x + n y) ∧
    (∀ x y, d x y = n (x - y)) := by
  sorry











theorem theorem_409380_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  (T : X →L[𝕜] Y)
  (h : IsCompact (T '' (Metric.closedBall 0 1))) :
  IsCompactOperator T := by
  sorry

theorem theorem_409319_problem
  {E : Type*} [NormedAddCommGroup E]
  (x y : E) (lambda : ℝ) (h : lambda > 0) :
  ‖x + y‖ ^ lambda ≤ 2 ^ lambda * (‖x‖ ^ lambda + ‖y‖ ^ lambda) := by
  sorry

theorem theorem_409022_problem :
  let f : ℂ → ℂ := fun z ↦ (z + 2) / (z - 2)
  circleIntegral (fun z ↦ (z + 2) / ((z + 1) ^ 2 * (z - 2))) I 2 =
  2 * ↑Real.pi * I * deriv f (-1) := by
  sorry

theorem theorem_409182_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  (A : V →ₗ[K] W)
  (k m : ℕ)
  (hk : FiniteDimensional.finrank K (LinearMap.ker A) = k)
  (hm : FiniteDimensional.finrank K (LinearMap.range A) = m) :
  ∃ (b : Basis (Fin m) K (V ⧸ LinearMap.ker A))
    (b' : Basis (Fin m) K (LinearMap.range A)),
    LinearMap.toMatrix b b' (LinearMap.quotKerEquivRange A) = 1 := by
  sorry

theorem theorem_409287_problem
  (X : Type*)
  (f_n : ℕ → X → ℝ)
  (f : X → ℝ)
  (M : ℝ)
  (hM : M ≥ 0)
  (h_conv : ∀ x, Filter.Tendsto (fun n ↦ f_n n x) Filter.atTop (nhds (f x)))
  (h_bound : ∀ n x, |f_n n x| ≤ M) :
  ∀ x, |f x| ≤ M := by
  sorry

theorem theorem_409303_problem
  (n : ℕ)
  (x₀ a : EuclideanSpace ℝ (Fin n))
  (b : ℝ)
  (ha : a ≠ 0) :
  let H := {x : EuclideanSpace ℝ (Fin n) | inner a x = b}
  let p := x₀ - ((inner a x₀ - b) / ‖a‖^2) • a
  p ∈ H ∧ ∀ x ∈ H, ‖p - x₀‖ ≤ ‖x - x₀‖ := by
  sorry





theorem theorem_409259_problem 
  (f : ℝ × ℝ × ℝ → ℝ) 
  (G_f : Set (ℝ × ℝ × ℝ × ℝ))
  (S_z0 : Set (ℝ × ℝ × ℝ × ℝ))
  (h_G_f : G_f = { p | p.2.2.2 = f (p.1, p.2.1, p.2.2.1) })
  (h_S_z0 : S_z0 = { p | p.2.2.1 = 0 }) :
  S_z0 ∩ G_f = { p | ∃ x y : ℝ, p = (x, y, 0, f (x, y, 0)) } := by
  sorry









theorem theorem_409963_problem
  {K : Type*} [Field K]
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix n m K)
  (p s : m → K)
  (h_p : p ∈ Submodule.span K (Set.range A))
  (h_s : Matrix.mulVec A s = 0) :
  Matrix.dotProduct p s = 0 := by
  sorry







theorem theorem_409757_problem
  (r : ℝ) (hr : r > 0)
  (f : ℂ → ℂ)
  (z₀ : ℂ)
  (h_analytic : AnalyticOn ℂ f (Metric.closedBall 0 r))
  (h_nonconst : ¬ ∀ x y, x ∈ Metric.closedBall 0 r → y ∈ Metric.closedBall 0 r → f x = f y)
  (h_z₀_bd : z₀ ∈ Metric.sphere 0 r)
  (h_max : IsMaxOn (Complex.abs ∘ f) (Metric.closedBall 0 r) z₀) :
  deriv f z₀ ≠ 0 := by
  sorry





theorem theorem_410246_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ)
  (hA : IsUnit A.det) :
  (A + Matrix.vecMulVec u v).det = A.det * (1 + Matrix.dotProduct v (Matrix.mulVec A⁻¹ u)) := by
  sorry







theorem theorem_410093_problem
  (k : Type*) [Field k] [IsAlgClosed k]
  (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (n : ℕ)
  (h_dim : FiniteDimensional.finrank k V = n) :
  ∀ a : k, ∃ M : V →ₗ[k] V, LinearMap.trace k V M = a := by
  sorry

theorem theorem_410345_problem
  (n m : ℕ)
  (f : (Fin n → ℝ) → ℝ)
  (g : (Fin m → ℝ) → (Fin n → ℝ))
  (x : Fin m → ℝ)
  (hg : DifferentiableAt ℝ g x)
  (hf : DifferentiableAt ℝ f (g x)) :
  fderiv ℝ (f ∘ g) x = (fderiv ℝ f (g x)).comp (fderiv ℝ g x) := by
  sorry

theorem theorem_410322_problem
  (k : Type*) [Field k] [CharZero k]
  (G : Type*) [Group G] [Fintype G]
  (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  -- V is a representation of G, modeled as a module over the group algebra
  [Module (MonoidAlgebra k G) V]
  -- Compatibility between the field action and the group algebra action
  [IsScalarTower k (MonoidAlgebra k G) V] :
  (∃ v : V, Submodule.span (MonoidAlgebra k G) {v} = ⊤) ↔
  (∃ f : MonoidAlgebra k G →ₗ[MonoidAlgebra k G] V, Function.Surjective f) := by
  sorry







theorem theorem_410400_problem
  {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x_star : EuclideanSpace ℝ (Fin n))
  (h_diff : ContDiff ℝ 2 f)
  (h_root : gradient f x_star = 0)
  (h_hess : ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 → inner v (fderiv ℝ (gradient f) x_star v) > (0 : ℝ)) :
  ∃ r > 0, ∃ C > 0, ∀ x : EuclideanSpace ℝ (Fin n), ‖x - x_star‖ < r →
    ∃ h : EuclideanSpace ℝ (Fin n),
      (fderiv ℝ (gradient f) x) h = - gradient f x ∧
      ‖x + h - x_star‖ ≤ C * ‖x - x_star‖ ^ 2 := by
  sorry



