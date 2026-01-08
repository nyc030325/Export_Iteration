import Mathlib
import Mathlib.Tactic







theorem theorem_1034962_problem
  {α R : Type*} [CommRing R]
  (S : Finset α)
  (x : α → R) :
  ∑ L in S.powerset, ∏ s in L, (x s - 1) = ∏ s in S, x s := by
  sorry

theorem theorem_1034501_problem
  (Riemann_Hypothesis : Prop)
  (Matomaki_Construction : (ℕ → ℕ) → Prop)
  (g : ℕ → ℕ)
  (hRH : Riemann_Hypothesis)
  (h_g_matomaki : Matomaki_Construction g)
  (h_g_prime : ∀ x, Nat.Prime (g x)) :
  ∀ a b : ℕ, (∃ m : ℕ, a = 2^m) → (∃ n : ℕ, b = 2^n) → a ≤ b →
  ∃ p, Nat.Prime p ∧ ∃ x, a ≤ x ∧ x ≤ b ∧ p = g x := by
  sorry

theorem theorem_1034492_problem (G : Set ℂ) (f : ℚ × ℚ × ℚ → G)
  (h : Function.Surjective f) : Set.Countable G := by
  sorry





theorem theorem_1035107_problem
  {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (D : Matrix V V ℝ)
  (hD : D = Matrix.diagonal (fun v ↦ (G.degree v : ℝ))) :
  (D.charpoly).rootMultiplicity 0 = Fintype.card {v : V // G.degree v = 0} := by
  sorry

theorem theorem_1034853_problem
  (V : ℝ → ℝ → ℝ)
  (δ : ℝ → ℝ)
  -- Assumptions regarding smoothness of V implied by "solution to the PDE"
  (h_diff : ContDiff ℝ 2 (Function.uncurry V))
  -- The Heat Equation: ∂V/∂u = ∂²V/∂x²
  (h_pde : ∀ u > 0, ∀ x > 0, deriv (fun t => V t x) u = deriv (deriv (V u)) x)
  -- Boundary Condition: V(u, 0) = 0
  (h_bc : ∀ u > 0, V u 0 = 0)
  -- Characterization of the Delta function (vanishes away from origin)
  (h_delta : ∀ x ≠ 0, δ x = 0)
  -- Initial Condition: V(0, x) = δ(x)
  (h_ic : ∀ x, V 0 x = δ x) :
  -- Conclusion: V is identically zero
  ∀ u ≥ 0, ∀ x ≥ 0, V u x = 0 := by
  sorry





theorem theorem_1034882_problem (x y : ℚ) (h : 3 * x^2 + 5 * y^2 = 4) : False := by
  sorry

theorem theorem_1035615_problem
  (G : Type*) [Group G] [Finite G]
  (p : ℕ) [Fact p.Prime]
  (h_div : p ∣ Nat.card G)
  (x : G)
  (h_union : ∃ P : Sylow p G, x ∈ P) :
  ∃ k : ℕ, orderOf x = p ^ k := by
  sorry

theorem theorem_1035176_problem
  (q : ℝ → Quaternion ℝ)
  (ω : ℝ → Quaternion ℝ)
  (t₀ t₁ : ℝ)
  (Δt : ℝ)
  (h_dt : Δt = t₁ - t₀)
  -- The angular velocity ω is a vector (pure quaternion)
  (h_pure : (ω t₀).re = 0)
  -- The kinematic differential equation: q̇ = 1/2 * ω * q
  -- Note: Mathlib uses • for scalar multiplication. 
  (h_kinematics : deriv q t₀ = (1 / 2 : ℝ) • (ω t₀ * q t₀)) :
  -- The first-order approximation (Taylor expansion) equals the formula
  q t₀ + Δt • deriv q t₀ = q t₀ + (1 / 2 * Δt) • (ω t₀ * q t₀) := by
  sorry



theorem theorem_1035693_problem
  (N : ℕ)
  (A B : Set (EuclideanSpace ℝ (Fin N)))
  (hA : A ⊆ Metric.sphere 0 1)
  (hB : B ⊆ Metric.sphere 0 1) :
  ∀ u ∈ A, ∀ v ∈ B,
    (∀ u' ∈ A, ∀ v' ∈ B, Real.arccos (inner u v) ≤ Real.arccos (inner u' v')) ↔
    (∀ u' ∈ A, ∀ v' ∈ B, ‖u - v‖ ≤ ‖u' - v'‖) := by
  sorry











theorem theorem_1035880_problem (α : Type) (φ : α → Prop) :
  (∃ x, φ x) ↔ ¬ (∀ x, ¬ φ x) := by
  sorry



theorem theorem_1035791_problem (K L : Type*) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
  (hK : Nonempty (K ≃ₐ[ℚ] AdjoinRoot (X ^ 2 - 2 : Polynomial ℚ)))
  (hL : Nonempty (L ≃ₐ[ℚ] AdjoinRoot (X ^ 2 - 3 : Polynomial ℚ))) :
  ¬ Nonempty (K ≃ₐ[ℚ] L) := by
  sorry

theorem theorem_1035974_problem
  (f : ℝ × ℝ → ℝ)
  (gamma1 gamma2 : ℝ → ℝ × ℝ)
  (L1 L2 : ℝ)
  (h1 : Filter.Tendsto gamma1 (nhds 0) (nhds 0))
  (h2 : Filter.Tendsto gamma2 (nhds 0) (nhds 0))
  (h3 : Filter.Tendsto (f ∘ gamma1) (nhds 0) (nhds L1))
  (h4 : Filter.Tendsto (f ∘ gamma2) (nhds 0) (nhds L2))
  (h5 : L1 ≠ L2) :
  ¬ ∃ L, Filter.Tendsto f (nhds 0) (nhds L) := by
  sorry





theorem theorem_1035960_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (γ : ℝ → E)
  (A : E →L[ℝ] E)
  (hA : ∀ x, ‖A x‖ = ‖x‖)
  (h_diff : ContDiff ℝ 2 γ)
  (h_arclength : ∀ s, ‖deriv γ s‖ = 1)
  (s : ℝ) :
  let γ_A := fun t ↦ A (γ t)
  ‖deriv (deriv γ_A) s‖ = ‖deriv (deriv γ) s‖ := by
  sorry

















theorem theorem_1036483_problem
  (g : ℕ → ℕ × ℕ)
  (hg : Function.Surjective g) :
  let h : ℕ × ℕ → ℚ := fun p => ((p.1 : ℚ) + 1) / ((p.2 : ℚ) + 1)
  let f : ℕ → ℚ := fun n =>
    if n = 0 then 0
    else if n % 2 = 0 then h (g (n / 2))
    else -h (g (n / 2))
  Function.Surjective f := by
  sorry

theorem theorem_1037117_problem (G : Type*) [Group G] (X : Type*) [MulAction G X] :
  {g : G | ∀ x : X, g • x = x} = (MonoidHom.ker (MulAction.toPermHom G X) : Set G) := by
  sorry

theorem theorem_1036942_problem (m : ℕ) (h : m ≥ 1) :
  bernoulli m = - (1 / (m + 1 : ℚ)) * ∑ k in Finset.range m, (Nat.choose (m + 1) k : ℚ) * bernoulli k := by
  sorry







theorem theorem_1036956_problem
  (A : Set (ℝ × ℝ))
  (hA_open : IsOpen A)
  (hA_conn : IsConnected A)
  (y₁ y₂ : ℝ × ℝ → ℝ)
  (hy₁_diff : DifferentiableOn ℝ y₁ A)
  (hy₂_diff : DifferentiableOn ℝ y₂ A)
  (hy₁_nz : ∀ x ∈ A, y₁ x ≠ 0)
  (h_det : ∀ x ∈ A,
    let d1y1 := fderivWithin ℝ y₁ A x (1, 0)
    let d2y1 := fderivWithin ℝ y₁ A x (0, 1)
    let d1y2 := fderivWithin ℝ y₂ A x (1, 0)
    let d2y2 := fderivWithin ℝ y₂ A x (0, 1)
    (y₁ x * d1y2 - y₂ x * d1y1 = 0) ∧
    (y₁ x * d2y2 - y₂ x * d2y1 = 0) ∧
    (d1y1 * d2y2 - d1y2 * d2y1 = 0)) :
  ∃ c : ℝ, ∀ x ∈ A, y₂ x = c * y₁ x := by
  sorry











theorem theorem_1038167_problem
  (f : ℝ × ℝ → ℝ)
  (x₁ y₁ x₂ y₂ : ℝ → ℝ)
  (L₁ L₂ : ℝ)
  (h_path1_lim : Filter.Tendsto (fun t ↦ (x₁ t, y₁ t)) (nhds 0) (nhds 0))
  (h_path2_lim : Filter.Tendsto (fun t ↦ (x₂ t, y₂ t)) (nhds 0) (nhds 0))
  (h_f_lim1 : Filter.Tendsto (fun t ↦ f (x₁ t, y₁ t)) (nhds 0) (nhds L₁))
  (h_f_lim2 : Filter.Tendsto (fun t ↦ f (x₂ t, y₂ t)) (nhds 0) (nhds L₂))
  (h_neq : L₁ ≠ L₂) :
  ¬ ∃ L, Filter.Tendsto f (nhds 0) (nhds L) := by
  sorry





theorem theorem_1037695_problem (N : ℕ) [NeZero N] (i j : Fin N)
  (E : Fin N → Matrix (Fin N) (Fin N) ℤ)
  (hE : ∀ k, E k = Matrix.stdBasisMatrix k 0 1) :
  Matrix.kronecker (E i) (Matrix.transpose (E j)) = Matrix.stdBasisMatrix (i, 0) (0, j) 1 := by
  sorry









theorem theorem_1039062_problem {α : Type*} (A : Set α) : ∅ ⊆ A := by
  sorry

theorem theorem_1038426_problem (α : ℂ) (N : ℕ)
  (h_alg : IsAlgebraic ℤ α)
  (hN : N > 0) :
  ∃ P : Polynomial ℤ, P.natDegree < N ∧ Polynomial.aeval α P = 0 := by
  sorry



theorem theorem_1038852_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M] [CompleteSpace M]
  (h_inf : ¬ FiniteDimensional 𝕜 M) :
  ¬ ∃ (ι : Type*) (_ : Countable ι), Nonempty (Basis ι 𝕜 M) := by
  sorry



theorem theorem_1038609_problem (a b : ℝ)
  (x y : ℝ → ℝ)
  (hx : ∀ t, x t = Real.exp t * (Real.cos t - Real.sin t))
  (hy : ∀ t, y t = Real.exp t * (Real.sin t + Real.cos t)) :
  ∫ t in a..b, Real.sqrt ((x t)^2 + (y t)^2) = Real.sqrt 2 * (Real.exp b - Real.exp a) := by
  sorry



theorem theorem_1038306_problem
  (K : Type*) [Field K]
  (V : Type*) [AddCommGroup V] [Module K V]
  (k : ℕ)
  (α : V)
  (C : (Fin k → K) → (Fin k → V))
  (hC : ∀ x : Fin k → K, C x = fun i => x i • α)
  (f : (Fin k → V) → ℝ)
  (x : Fin k → K) :
  (f ∘ C) x = f (fun i => x i • α) := by
  sorry





theorem theorem_1039262_problem (y : ℝ → ℝ) (u : ℝ → ℝ)
  (h_diff_y : Differentiable ℝ y)
  (h_diff_dy : Differentiable ℝ (deriv y))
  (h_diff_u : Differentiable ℝ u)
  (h_u_def : ∀ x, deriv y x = u (y x))
  (h_ode : ∀ x, y x * deriv (deriv y) x + (deriv y x)^2 + 1 = 0) :
  ∀ x, y x * deriv u (y x) * u (y x) + (u (y x))^2 + 1 = 0 := by
  sorry

theorem theorem_1039110_problem
  (X : Type*) [TopologicalSpace X]
  -- "Bor(X) the Borel sigma-algebra" is represented by the MeasurableSpace instance with BorelSpace
  [MeasurableSpace X] [BorelSpace X]
  -- "ν a measure defined on Bor(X)"
  (ν : MeasureTheory.Measure X)
  -- "ν' is the restriction of ν to Bor(X)"
  -- Since ν is already defined on Bor(X), the restriction is equal to the original measure.
  (ν' : MeasureTheory.Measure X) (h_res : ν' = ν)
  -- "f : X -> R_bar" (Extended Real numbers)
  (f : X → EReal) :
  -- "f is measurable w.r.t ν' iff f is measurable w.r.t ν"
  -- The solution defines "measurable w.r.t measure" as "measurable w.r.t the sigma algebra".
  Measurable f ↔ Measurable f := by
  sorry



theorem theorem_1038463_problem (n : ℕ)
  (A B : Matrix (Fin n) (Fin n) ℂ)
  (U1 U2 V1 V2 : Matrix (Fin n) (Fin n) ℂ)
  (S : Matrix (Fin n) (Fin n) ℝ)
  (hS : S.IsDiag)
  (hU1 : U1 ∈ Matrix.unitaryGroup (Fin n) ℂ)
  (hU2 : U2 ∈ Matrix.unitaryGroup (Fin n) ℂ)
  (hV1 : V1 ∈ Matrix.unitaryGroup (Fin n) ℂ)
  (hV2 : V2 ∈ Matrix.unitaryGroup (Fin n) ℂ)
  (hA : A = U1 * (S.map Complex.ofReal) * V1.conjTranspose)
  (hB : B = U2 * (S.map Complex.ofReal) * V2.conjTranspose) :
  ∃ U V : Matrix (Fin n) (Fin n) ℂ,
    U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
    V ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
    A = U * B * V := by
  sorry

theorem theorem_1038867_problem (k : ℕ) (hk : k > 1) :
  (fun n : ℕ => ((Nat.choose (k * n) n : ℝ) ^ (1 / (n : ℝ))) - ((k : ℝ) ^ k / ((k : ℝ) - 1) ^ (k - 1))) 
    =O[atTop] (fun n => 1 / (n : ℝ)) := by
  sorry

theorem theorem_1039370_problem {Ω : Type*} (I : Set (Set Ω)) :
  @MeasurableSet Ω (MeasurableSpace.generateFrom I) Set.univ := by
  sorry



theorem theorem_1039201_problem
  {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
  (w : V → ℝ) (hw : ∀ v, 0 < w v) :
  ∃ v_star : V, ∀ v : V,
    (∑ u : V, w u * (G.dist v_star u : ENNReal).toReal) ≤
    (∑ u : V, w u * (G.dist v u : ENNReal).toReal) := by
  sorry





theorem theorem_1038962_problem (N M : ℕ) (f : (Fin N → ℝ) → (Fin M → ℝ)) :
  ∃! (F : Fin M → ((Fin N → ℝ) → ℝ)), ∀ (x : Fin N → ℝ), f x = fun i ↦ F i x := by
  sorry













theorem theorem_1039562_problem (A : Type*) [CommRing A] (f g : A) :
  IsClosed {x : PrimeSpectrum A | f ∈ x.asIdeal} ∧
  IsClosed {x : PrimeSpectrum A | g ∈ x.asIdeal} := by
  sorry









theorem theorem_1040166_problem (a b : ℕ → ℝ)
  (h : ∀ ε > 0, ∃ N : ℕ, ∀ m n : ℕ, m ≥ N → n ≥ N →
    |∑ k in Finset.range (m + 1), a k * b k - ∑ k in Finset.range (n + 1), a k * b k| ≤ ε) :
  ∃ L : ℝ, Filter.Tendsto (fun m ↦ ∑ k in Finset.range (m + 1), a k * b k) Filter.atTop (nhds L) := by
  sorry

theorem theorem_1039690_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (P : Set (Module.End F V))
  (h_proj : ∀ p ∈ P, p ^ 2 = p)
  (h_orth : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p * q = 0 ∧ q * p = 0)
  (h_card : Cardinal.mk P ≥ 2 ^ Cardinal.aleph0) :
  ¬ FiniteDimensional F V := by
  sorry



theorem theorem_1040165_problem (r : ℕ) (p t : ℝ)
  (hr : r > 0)
  (hp : 0 < p ∧ p < 1)
  (ht : t < - Real.log (1 - p)) :
  ∑' (y : ℕ), (Nat.choose (r + y - 1) y : ℝ) * p ^ r * (1 - p) ^ y * Real.exp (t * y) =
  p ^ r / (1 - (1 - p) * Real.exp t) ^ r := by
  sorry

theorem theorem_1039494_problem
  (p q : ℝ → ℝ)
  (hp : AnalyticAt ℝ p 0)
  (hq : AnalyticAt ℝ q 0)
  (k₁ : ℝ)
  (h_indicial : k₁ * (k₁ - 1) + p 0 * k₁ + q 0 = 0)
  (h_repeated : 2 * k₁ - 1 + p 0 = 0) :
  ∃ (y₂ : ℝ → ℝ) (c₂ : ℝ) (g : ℝ → ℝ) (R : ℝ),
    R > 0 ∧
    c₂ ≠ 0 ∧
    AnalyticAt ℝ g 0 ∧
    (∀ x ∈ Set.Ioo 0 R,
      x^2 * (deriv^[2] y₂ x) + x * p x * (deriv y₂ x) + q x * y₂ x = 0) ∧
    (∀ x ∈ Set.Ioo 0 R,
      y₂ x = c₂ * x^k₁ * Real.log x + x^k₁ * g x) := by
  sorry

theorem theorem_1040081_problem 
  (X : Type*) 
  (f : ℕ → X → EReal) 
  (g : X → EReal) 
  (h_def : ∀ x, g x = ⨆ n, f n x) 
  (a : ℝ) : 
  g ⁻¹' (Set.Ioi (a : EReal)) = ⋃ n, (f n) ⁻¹' (Set.Ioi (a : EReal)) := by
  sorry

theorem theorem_1040313_problem (β : ℝ) (hβ : β = (1 + Real.sqrt 5) / 2) :
  Real.logb 10 β > 1 / 5 := by
  sorry









