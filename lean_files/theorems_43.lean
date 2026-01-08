import Mathlib
import Mathlib.Tactic

theorem theorem_231495_problem
  {E : Type*} [AddCommGroup E] [Module ℂ E]
  (Δ : E →ₗ[ℂ] E)
  (k : ℂ)
  (p₁ p₂ : E)
  (a₁ a₂ : ℂ)
  (h₁ : Δ p₁ + k^2 • p₁ = 0)
  (h₂ : Δ p₂ + k^2 • p₂ = 0) :
  Δ (a₁ • p₁ + a₂ • p₂) + k^2 • (a₁ • p₁ + a₂ • p₂) = 0 := by
  sorry



theorem theorem_231600_problem (z y x : ℤ)
  (hz : z = 0 ∨ z = 1)
  (hy : y = 0 ∨ y = 1)
  (hx : x = 0 ∨ x = 1) :
  z + y - 1 ≤ x ↔ ((z = 1 ∧ y = 1) → x = 1) := by
  sorry









theorem theorem_231973_problem (n : ℕ) (x u₀ u₁ : EuclideanSpace ℝ (Fin n)) :
  ‖x - u₁‖^2 - ‖x - u₀‖^2 = ‖u₁‖^2 - ‖u₀‖^2 - 2 * inner x (u₁ - u₀) := by
  sorry









theorem theorem_231949_problem (d : ℕ) :
  ∃ C : ℝ, 0 < C ∧ ∀ k : Fin d → ℝ,
    Complex.abs (∫ x in Set.pi Set.univ (fun (j : Fin d) => Set.Icc (-1 : ℝ) 1),
      Complex.exp (Complex.I * ∑ j, (k j : ℂ) * (x j : ℂ))) ≤
    C / ∏ j, (1 + |k j|) := by
  sorry

theorem theorem_232241_problem (X : Matrix (Fin 2) (Fin 2) ℂ) :
  X ^ 2 ≠ !![0, 1; 0, 0] := by
  sorry



theorem theorem_232142_problem
  (G : Type*) [Group G] [Finite G]
  (F : Type*) [Field F]
  (V : Type*) [AddCommGroup V] [Module F V]
  (ρ : G →* (V ≃ₗ[F] V)) :
  ∀ g h : G, ρ (g * h) = ρ g * ρ h := by
  sorry

theorem theorem_232537_problem
  {n : ℕ}
  {X : Type*}
  [MeasurableSpace X]
  (ν : MeasureTheory.Measure X)
  [MeasureTheory.IsProbabilityMeasure ν]
  (f : X → (Fin n → ℝ))
  (h_borel : Measurable f)
  (h_int : MeasureTheory.Integrable f ν) :
  ∫ x, f x ∂ν ∈ closure (convexHull ℝ (Set.range f)) := by
  sorry

theorem theorem_232882_problem
  {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  (X : Matrix n m ℝ)
  (y : Matrix n Unit ℝ)
  (h_inv : IsUnit (X.transpose * X).det) :
  let y_hat := X * (X.transpose * X)⁻¹ * X.transpose * y
  let r := y - y_hat
  X.transpose * r = 0 := by
  sorry



theorem theorem_232756_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  {W : Type*} [AddCommGroup W] [Module K W]
  (h1 : ∃ T : V →ₗ[K] W, Function.Injective T)
  (h2 : ∃ S : W →ₗ[K] V, Function.Injective S) :
  Nonempty (V ≃ₗ[K] W) := by
  sorry



theorem theorem_232883_problem
  (r : EuclideanSpace ℝ (Fin 2))
  (h_nz : r ≠ 0)
  (f : EuclideanSpace ℝ (Fin 2) → ℝ)
  (h_f : ∀ x, f x = -(‖x‖)⁻¹) :
  gradient f r = (‖r‖ ^ 3)⁻¹ • r := by
  sorry



theorem theorem_232511_problem
  (n : ℕ) (hn : 0 < n)
  (x y : Fin n → ℝ)
  (x_bar : ℝ) (hx_bar : x_bar = (∑ i, x i) / n)
  (y_bar : ℝ) (hy_bar : y_bar = (∑ i, y i) / n)
  (xi : Fin n → ℝ) (hxi : ∀ i, xi i = x i - x_bar)
  (xi_bar : ℝ) (hxi_bar : xi_bar = (∑ i, xi i) / n)
  (h_sum_sq : ∑ i, (xi i - xi_bar)^2 = n)
  (h_xi_mean_zero : xi_bar = 0)
  (beta_1 : ℝ)
  (h_beta_1 : beta_1 = (∑ i, (x i - x_bar) * (y i - y_bar)) / (∑ i, (x i - x_bar)^2)) :
  beta_1 = ∑ i, (xi i / n) * y i := by
  sorry

theorem theorem_232894_problem 
  {n : ℕ} 
  (k₁ k₂ : EuclideanSpace ℝ (Fin n)) 
  (h_nonzero : k₁ ≠ 0)
  (h_cond : k₁ + k₂ = 0) : 
  (4 * π) / ‖k₁‖^2 = (4 * π) / (‖k₁‖ * ‖k₂‖) := by
  sorry





theorem theorem_232443_problem (n : ℕ)
  (φ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] ℝ) :
  ∃ v : Fin n → ℝ, φ v v = 0 := by
  sorry

theorem theorem_233308_problem
  {n α : Type*}
  (M : Matrix n n α)
  (C : n → n → α → Prop)
  (hC : ∀ (x y : n) (z : α), C x y z ↔ z = M x y)
  (z : α) :
  (∃ i, M i i = z) ↔ (∃ x, C x x z) := by
  sorry

theorem theorem_233388_problem (n m : ℕ) :
  let V_m := MvPolynomial.homogeneousSubmodule (Fin n) ℚ m
  let V_1 := MvPolynomial.homogeneousSubmodule (Fin n) ℚ 1
  let W := Submodule.span ℚ { p | ∃ l ∈ V_1, p = l ^ m }
  W = V_m := by
  sorry















theorem theorem_233503_problem (n : ℕ) (f : (Fin n → ℝ) → ℝ) (hf : ConvexOn ℝ Set.univ f) :
  ∀ x : Fin n → ℝ, (⨆ i, |x i|) ≤ 1 ↔ ∀ i, -1 ≤ x i ∧ x i ≤ 1 := by
  sorry



theorem theorem_233832_problem
  {k : Type*} [Field k]
  {E : Type*} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
  {P : Type*} [AddTorsor E P]
  (g : P →ᵃ[k] P)
  (h_no_fixed : ∀ x : P, g x ≠ x) :
  Module.End.HasEigenvalue g.linear 1 := by
  sorry

theorem theorem_233858_problem
  (n : ℕ)
  (A B X : Matrix (Fin n) (Fin n) ℝ)
  (hX : X.PosDef)
  (hB : B.PosDef) :
  (X - A.transpose * (A * X⁻¹ * A.transpose + B)⁻¹ * A).PosSemidef := by
  sorry

theorem theorem_233593_problem 
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (A : ℝ → H →L[ℂ] H)
  (hA : Continuous A)
  (ψ₀ : H) :
  ∃! ψ : ℝ → H, ψ 0 = ψ₀ ∧ ∀ t, HasDerivAt ψ (-I • (A t) (ψ t)) t := by
  sorry























theorem theorem_234194_problem
  (fn : ℕ → ℝ → ℝ)
  (f : ℝ → ℝ)
  (h_cont : ∀ n, ContinuousOn (fn n) (Set.Icc (-1) 1))
  (h_pt : ∀ x ∈ Set.Icc (-1 : ℝ) 1, Filter.Tendsto (fun n ↦ fn n x) Filter.atTop (nhds (f x)))
  (h_disc : ¬ ContinuousOn f (Set.Icc (-1) 1)) :
  ¬ TendstoUniformlyOn fn f Filter.atTop (Set.Icc (-1) 1) := by
  sorry





theorem theorem_234671_problem
  {n1 m1 n2 m2 : Type*} [Fintype n1] [Fintype m1] [Fintype n2] [Fintype m2]
  [DecidableEq n1] [DecidableEq m1] [DecidableEq n2] [DecidableEq m2]
  {R : Type*} [CommRing R]
  (Q1 : Matrix n1 n1 R) (S1 : Matrix n1 m1 R) (R1 : Matrix m1 m1 R)
  (Q2 : Matrix n2 n2 R) (S2 : Matrix n2 m2 R) (R2 : Matrix m2 m2 R)
  (P1 : Matrix (n1 ⊕ m1) (n1 ⊕ m1) R)
  (hP1 : P1 = Matrix.fromBlocks Q1 S1 (Matrix.transpose S1) R1)
  (P2 : Matrix (n2 ⊕ m2) (n2 ⊕ m2) R)
  (hP2 : P2 = Matrix.fromBlocks Q2 S2 (Matrix.transpose S2) R2) :
  ∃ (e : (n1 ⊕ m1) ⊕ (n2 ⊕ m2) ≃ (n1 ⊕ n2) ⊕ (m1 ⊕ m2)),
    Matrix.reindex e e (Matrix.fromBlocks P1 0 0 P2) =
    Matrix.fromBlocks
      (Matrix.fromBlocks Q1 0 0 Q2)
      (Matrix.fromBlocks S1 0 0 S2)
      (Matrix.fromBlocks (Matrix.transpose S1) 0 0 (Matrix.transpose S2))
      (Matrix.fromBlocks R1 0 0 R2) := by
  sorry



theorem theorem_234480_problem
  (F : Type*) [Field F] [CharZero F]
  (G : Type*) [Group G] [Finite G]
  (V : Type*) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [DistribMulAction G V] [SMulCommClass G F V]
  (W : Submodule F V)
  (hW : ∀ (g : G) (v : V), v ∈ W → g • v ∈ W) :
  ∃ W' : Submodule F V, (∀ (g : G) (v : V), v ∈ W' → g • v ∈ W') ∧ IsCompl W W' := by
  sorry



theorem theorem_234712_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {D : Type*} [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (ι : D →L[𝕜] H) :
  ∃ ι_t : (H →L[𝕜] 𝕜) →L[𝕜] (D →L[𝕜] 𝕜),
  ∀ (φ : D) (T : H →L[𝕜] 𝕜), ι_t T φ = T (ι φ) := by
  sorry





theorem theorem_234871_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
  let B := Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) ℝ) A.transpose A 0
  Matrix.charpoly B = (Matrix.charpoly (A.transpose * A)).comp (X ^ 2) := by
  sorry

theorem theorem_234764_problem 
  {n : Type*} [Fintype n] [DecidableEq n]
  (u : n → ℝ)
  (G : Matrix n n ℝ)
  (j : ℝ)
  (hG : IsUnit G)
  (H : Matrix n n ℝ)
  (hH : H = j • G⁻¹)
  (i l k : n) :
  u i * H l k = u i * (j • G⁻¹) l k := by
  sorry

theorem theorem_234904_problem (n : ℝ) (A B : Matrix (Fin 2) (Fin 2) ℝ)
  (hA : A = !![1, 1; 0, 1])
  (hB : B = !![1, 0; n, 1]) :
  Matrix.det (A^2 + B^2) = 4 * (1 - n) := by
  sorry





theorem theorem_234992_problem {R : Type*} [CommRing R] {n : ℕ}
  (A : Matrix (Fin n.succ) (Fin n.succ) R) (i : Fin n.succ) :
  A.det = ∑ j : Fin n.succ, (-1 : R) ^ ((i : ℕ) + (j : ℕ)) * A i j * (A.submatrix i.succAbove j.succAbove).det := by
  sorry







theorem theorem_235425_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA_symm : A.IsSymm) (hA_pos : A.PosSemidef)
  (hB_symm : B.IsSymm) (hB_pos : B.PosSemidef) :
  Matrix.trace ((hA_pos.sqrt - hB_pos.sqrt) * (hA_pos.sqrt + hB_pos.sqrt)) ≤
  Real.sqrt (Matrix.trace ((hA_pos.sqrt - hB_pos.sqrt) ^ 2)) *
  Real.sqrt (Matrix.trace ((hA_pos.sqrt + hB_pos.sqrt) ^ 2)) := by
  sorry







theorem theorem_235736_problem :
  Nonempty (AddAut ((ZMod 2) × (ZMod 2)) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) := by
  sorry











theorem theorem_235640_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  {n : Type*} [Fintype n] [DecidableEq n]
  (B : Basis n K V)
  (B' : Basis n K V)
  (T : V →ₗ[K] V) :
  (LinearMap.toMatrix B B T).charpoly = (LinearMap.toMatrix B' B' T).charpoly := by
  sorry



theorem theorem_235668_problem (f : ℝ → ℝ → ℝ)
  (hf : ContDiff ℝ 2 (Function.uncurry f)) :
  let partial_x : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) := fun g x y ↦ deriv (fun u ↦ g u y) x
  let partial_y : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) := fun g x y ↦ deriv (fun v ↦ g x v) y
  let partial_w : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) := fun g x y ↦ partial_x g x y - 2 * x * partial_y g x y
  let partial_z : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) := fun g ↦ partial_y g
  partial_w (partial_z f) = partial_z (partial_w f) := by
  sorry











theorem theorem_236424_problem (C_M C_A C_D C : ℝ) (n_M n_A n_D : ℝ)
  (h1 : C = n_M * C_M + n_A * C_A + n_D * C_D)
  (h2 : C_D = C_M) :
  C = (n_M + n_D) * C_M + n_A * C_A := by
  sorry





theorem theorem_236008_problem (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (c : Fin n → ℝ)
  (x : Fin n → ℝ)
  (B : Finset (Fin n))
  -- Conditions for a Basic Feasible Solution under Non-degeneracy assumption
  (h_nondegenerate : ∀ i ∈ B, x i > 0)
  (h_nonbasic : ∀ i ∉ B, x i = 0)
  -- Definition of entering variable x_e as a nonbasic variable
  (e : Fin n)
  (h_entering : e ∉ B)
  -- Definition of leaving variable x_l as a basic variable
  (l : Fin n)
  (h_leaving : l ∈ B) :
  -- The entering variable and leaving variable are not the same
  e ≠ l := by
  sorry







theorem theorem_236665_problem (F : ℝ → ℝ)
  (h : ∀ t > 0, F t = ∫ x in Set.Ioi 0, Real.exp (-t * x ^ 3)) :
  ContinuousOn F (Set.Ioi 0) := by
  sorry



theorem theorem_237051_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (f : X →ₗ[ℝ] ℝ)
  (h_unbounded : ¬ IsBoundedLinearMap ℝ f) :
  Dense (LinearMap.ker f : Set X) := by
  sorry

