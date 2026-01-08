import Mathlib
import Mathlib.Tactic

theorem theorem_203276_problem
  (norm : Matrix (Fin 2) (Fin 2) ℂ → ℝ)
  (h_def : ∀ A, norm A = 0 ↔ A = 0)
  (h_hom : ∀ (c : ℂ) A, norm (c • A) = Complex.abs c * norm A)
  (h_tri : ∀ A B, norm (A + B) ≤ norm A + norm B)
  (h_cond : ∀ A, IsUnit A.det → ∀ z : ℂ, z^2 = A.det →
    norm A = Complex.abs z * norm (z⁻¹ • A)) :
  False := by
  sorry







theorem theorem_203488_problem (n : ℕ) (hn : n ≥ 2) :
  let U1 : Set (Matrix (Fin n) (Fin n) ℂ) :=
    {A | ∃ θ : ℝ, A = Matrix.diagonal (Function.update (λ _ ↦ 1) ⟨0, by linarith⟩ (Complex.exp (Complex.I * θ)))}
  let SUn : Set (Matrix (Fin n) (Fin n) ℂ) := Matrix.specialUnitaryGroup (Fin n) ℂ
  U1 ∩ SUn = {1} := by
  sorry



theorem theorem_203331_problem (z : ℂ) (hz : 1 < Complex.abs z) :
  let u : ℤ → ℂ := fun n ↦ if n ≥ 0 then 1 else 0
  let x : ℤ → ℂ := fun n ↦ u (n - 1) * (5 - (20 / 3 : ℂ) * (0.6 : ℂ) ^ n)
  let X : ℂ := 5 * z⁻¹ * (z / (z - 1)) - 4 * z⁻¹ * (z / (z - 0.6))
  ∑' n : ℤ, x n * z ^ (-n) = X := by
  sorry

theorem theorem_203790_problem
  {S : Type*} [Fintype S] [DecidableEq S]
  (l : S → ℝ) (z : S → ℂ)
  (h_distinct : Function.Injective l) :
  ∑ s, ∑ t in Finset.univ.erase s, (Complex.normSq (z s) + Complex.normSq (z t)) / (l s - l t)^2 =
  2 * ∑ s, Complex.normSq (z s) * ∑ t in Finset.univ.erase s, 1 / (l s - l t)^2 := by
  sorry

theorem theorem_203378_problem (f : ℝ → ℝ) (x M : ℝ)
  (h_bound : ∃ K, ∀ y, |f y| ≤ K)
  (h_ineq : ∀ t, t ≠ 0 → |(f (x - t) - f x) / Real.sin (t / 2)| ≤ |(M * t) / Real.sin (t / 2)|) :
  ∃ C δ, δ > 0 ∧ ∀ t, t ≠ 0 ∧ |t| < δ → |(f (x - t) - f x) / Real.sin (t / 2)| ≤ C := by
  sorry





theorem theorem_203410_problem 
  (H₁ H₂ : Set (Fin 2 → ℝ))
  -- Conditions: Balanced, Convex, Hexagons
  (h_bal₁ : ∀ x ∈ H₁, -x ∈ H₁)
  (h_bal₂ : ∀ x ∈ H₂, -x ∈ H₁)
  (h_conv₁ : Convex ℝ H₁)
  (h_conv₂ : Convex ℝ H₂)
  -- Hexagon definition: Convex hull of 6 points
  (h_hex₁ : ∃ s : Finset (Fin 2 → ℝ), s.card = 6 ∧ H₁ = convexHull ℝ s)
  (h_hex₂ : ∃ s : Finset (Fin 2 → ℝ), s.card = 6 ∧ H₂ = convexHull ℝ s)
  -- Norms defined on the space
  (n₁ n₂ : (Fin 2 → ℝ) → ℝ)
  -- Properties of norms relevant to the problem (Homogeneity is key for linearity)
  (h_hom₁ : ∀ (c : ℝ) (x : Fin 2 → ℝ), n₁ (c • x) = |c| * n₁ x)
  (h_hom₂ : ∀ (c : ℝ) (x : Fin 2 → ℝ), n₂ (c • x) = |c| * n₂ x)
  -- Norm equals 1 iff on boundary
  (h_n1_bound : ∀ x, n₁ x = 1 ↔ x ∈ frontier H₁)
  (h_n2_bound : ∀ x, n₂ x = 1 ↔ x ∈ frontier H₂)
  -- H1 and H2 are not images of one another under any linear mapping
  (h_not_affine : ¬ ∃ (L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)), L '' H₁ = H₂) :
  -- Conclusion: Not isometric under any linear isometry
  ¬ ∃ (T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)), ∀ x, n₂ (T x) = n₁ x := by
  sorry







theorem theorem_203979_problem
  (F : (m n : ℕ) → Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ)
  (h_mul : ∀ {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ),
    F m p (A * B) = F m n A * F n p B)
  (h_inv : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ), IsUnit A →
    F n n A = (A.transpose)⁻¹) :
  False := by
  sorry





theorem theorem_204408_problem
  (Ω : Set ℂ) (hΩ : IsOpen Ω)
  (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
  (h_holo : ∀ n, DifferentiableOn ℂ (f n) Ω)
  (h_bound : ∃ M, ∀ n, ∀ z ∈ Ω, ‖f n z‖ ≤ M)
  (h_pt : ∀ z ∈ Ω, Filter.Tendsto (fun n ↦ f n z) Filter.atTop (nhds (g z)))
  (h_g_holo : DifferentiableOn ℂ g Ω) :
  ∀ K ⊆ Ω, IsCompact K → TendstoUniformlyOn f g Filter.atTop K := by
  sorry





theorem theorem_203935_problem (n v : EuclideanSpace ℝ (Fin 3))
  (hn : ‖n‖ = 1) :
  ↑(orthogonalProjection (Submodule.span ℝ {n})ᗮ v) = - crossProduct n (crossProduct n v) := by
  sorry



theorem theorem_204308_problem
  (L C R D V₀ I_L : ℝ)
  (s d v_in i_L : ℂ)
  (hL : L > 0)
  (hC : C > 0)
  (hR : R > 0)
  (hD : 0 ≤ D ∧ D ≤ 1)
  (h_constraint : (s * (C : ℂ) + 1 / (R : ℂ)) * v_in = ((1 - (D : ℂ)) * (I_L : ℂ) - 1 / (R : ℂ) * (V₀ : ℂ)) * d)
  (h_iL_def : i_L = (1 / ((L : ℂ) * C * s^2 + (L / R) * s + (1 - (D : ℂ))^2)) *
    ((1 - (D : ℂ)) * ((s * C + 1 / R) * V₀ * d + (s * C + 1 / R) * v_in) - s * L * (-(I_L : ℂ) * d))) :
  i_L = (((s * (C : ℂ) + 1 / (R : ℂ)) * V₀ + (1 - (D : ℂ)) * I_L) * d + (s * C + 1 / R) * v_in) /
    ((L : ℂ) * C * s^2 + (L / R) * s + (1 - (D : ℂ))^2) := by
  sorry





theorem theorem_205032_problem
  {K : Type*} [Field K]
  {m n p : ℕ}
  (F : Matrix (Fin m) (Fin p) K)
  (W : Matrix (Fin n) (Fin p) K)
  (h : W.rank < F.rank) :
  ¬ ∃ (G : Matrix (Fin m) (Fin n) K), F = G * W := by
  sorry

theorem theorem_204600_problem (n k : ℕ) (h : k ≤ n) (v : Fin k → (Fin n → ℝ)) :
  let dx := fun (i : Fin k) (u : Fin n → ℝ) ↦ u (Fin.castLE h i)
  let action := Matrix.det (fun (i j : Fin k) ↦ dx i (v j))
  let projection := fun (u : Fin n → ℝ) (i : Fin k) ↦ u (Fin.castLE h i)
  let signed_volume := Matrix.det (fun (i j : Fin k) ↦ projection (v j) i)
  action = signed_volume := by
  sorry

theorem theorem_204918_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : ℕ} (hn : 0 < n)
  (B : Basis (Fin n) K V)
  (T : V →ₗ[K] V)
  (h_upper : ∀ (i j : Fin n), j < i → LinearMap.toMatrix B B T i j = 0) :
  T (B ⟨0, hn⟩) = (LinearMap.toMatrix B B T ⟨0, hn⟩ ⟨0, hn⟩) • (B ⟨0, hn⟩) := by
  sorry





















theorem theorem_205219_problem
  (M : Type*) [Ring M]
  (H : Type*) [AddCommGroup H] [Module M H]
  (ξ : H)
  (ι : M → H)
  (h_inj : Function.Injective ι)
  (h_xi : ι 1 = ξ)
  (h_act : ∀ x : M, x • ξ = ι x)
  (x : M) :
  x • ξ = ξ ↔ x = 1 := by
  sorry



theorem theorem_205628_problem (A : Set ℝ)
  (hA : Dense A)
  (hAc : Dense Aᶜ) :
  ∀ x : ℝ, ¬ ContinuousAt (Set.indicator A (fun _ ↦ (1 : ℝ))) x := by
  sorry



theorem theorem_205473_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (θ : V →ₗ[F] V) :
  FiniteDimensional.finrank F (LinearMap.ker θ) + FiniteDimensional.finrank F (LinearMap.range θ) =
  FiniteDimensional.finrank F V := by
  sorry

theorem theorem_205356_problem
  (n : ℕ)
  (Q : Matrix (Fin n) (Fin n) ℝ)
  (b : Fin n → ℝ)
  (hQ : Q.IsSymm)
  (f : (Fin n → ℝ) → ℝ)
  (hf : ∀ x, f x = (1 / 2 : ℝ) * Matrix.dotProduct x (Matrix.mulVec Q x) + Matrix.dotProduct x b) :
  ∀ x : Fin n → ℝ, ∀ u v : Fin n → ℝ,
    iteratedFDeriv ℝ 2 f x ![u, v] = Matrix.dotProduct u (Matrix.mulVec Q v) := by
  sorry







theorem theorem_205889_problem
  (T : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ)
  (hT : ∀ p : Polynomial ℂ, T p = 2 • p + Complex.I • Polynomial.derivative p)
  (x : ℂ)
  (hx : x ≠ 0)
  (p : Polynomial ℂ) :
  (T p).eval x = 2 * (p.eval x) + Complex.I * (Polynomial.derivative p).eval x := by
  sorry













theorem theorem_206256_problem {n : Type*} [Fintype n] [DecidableEq n]
  (A : Matrix n n ℝ) (hA : A.IsSymm) :
  ∃ B C : Matrix n n ℝ,
    A = B + C ∧
    (∀ i j, i ≠ j → B i j = 0) ∧
    (∀ i, C i i = 0) := by
  sorry



theorem theorem_206468_problem (n : ℕ)
  (T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  (eigs : Fin n → ℝ)
  (vecs : Fin n → (Fin n → ℝ))
  (h_distinct : Function.Injective eigs)
  (h_eigen_eq : ∀ i, T (vecs i) = eigs i • vecs i)
  (h_nonzero : ∀ i, vecs i ≠ 0) :
  LinearIndependent ℝ vecs := by
  sorry









theorem theorem_206235_problem
  (n : ℕ)
  (A Q Λ Λ_minus A_minus : Matrix (Fin n) (Fin n) ℂ)
  (hQ : Invertible Q)
  (hΛ_diag : Λ.IsDiag)
  (hA : A = Q * Λ * Q⁻¹)
  (hΛ_minus_diag : Λ_minus.IsDiag)
  (hΛ_minus_val : ∀ i, Λ_minus i i = (- (Λ i i).re : ℂ) + ((Λ i i).im : ℂ) * I)
  (hA_minus : A_minus = Q * Λ_minus * Q⁻¹) :
  ∀ i, Module.End.HasEigenvalue (Matrix.toLin' A_minus) (Λ_minus i i) := by
  sorry



theorem theorem_206535_problem
  {K V T : Type*}
  [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]
  [CompleteSpace K] [CompleteSpace V]
  (n : ℕ)
  (l : ℕ → T → K)
  (w : Fin n → V)
  (α : ℕ → Fin n → K)
  (v : T → V)
  (h_indep : LinearIndependent K w)
  (h_summable_scalar : ∀ t j, Summable (fun i => α i j * l i t))
  (hv : ∀ t, v t = ∑' i, ∑ j, (α i j * l i t) • w j) :
  ∀ t, v t = ∑ j, (∑' i, α i j * l i t) • w j := by
  sorry

theorem theorem_206617_problem (R : ℝ) (h : 1 < R) :
  circleIntegral (fun z => 1 / (z ^ 2 * (z - 1) ^ 3)) 0 R = 0 := by
  sorry

theorem theorem_206563_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (T : V →ₗ[K] V)
  (h : ∀ x : V, ∃ c : K, T x = c • x) :
  ∃ c : K, ∀ x : V, T x = c • x := by
  sorry

theorem theorem_206735_problem (n : ℕ) (a b : Fin n → ℝ)
  (h : ∀ i, a i < b i) :
  Convex ℝ (Set.pi Set.univ (fun i => Set.Icc (a i) (b i))) := by
  sorry



theorem theorem_206920_problem
  (F : Type*) [Field F]
  (V : Type*) [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (k : ℕ) :
  Nonempty (MultilinearMap F (fun (_ : Fin k) ↦ V) F ≃ₗ[F]
    Module.Dual F (TensorPower F k V)) := by
  sorry







theorem theorem_206854_problem 
  (a b : ℝ) (hab : a ≤ b)
  (Q : Submodule ℝ C(Set.Icc a b, ℝ))
  [FiniteDimensional ℝ Q]
  (f : C(Set.Icc a b, ℝ))
  (k : ℝ) (hk : 0 < k)
  (h_exist : ∃ p : Q, ‖f - (p : C(Set.Icc a b, ℝ))‖ < k) :
  ∃ q : Q, ‖(q : C(Set.Icc a b, ℝ))‖ ≤ k ∧ 
  ∀ p : Q, ‖(p : C(Set.Icc a b, ℝ))‖ ≤ k → 
    ‖f - (q : C(Set.Icc a b, ℝ))‖ ≤ ‖f - (p : C(Set.Icc a b, ℝ))‖ := by
  sorry





theorem theorem_207072_problem 
  (l_S l_0 l_p : ℝ) 
  (D_res D_tot : ℝ) 
  (h_res : D_res = 2 * (l_S - l_p)) 
  (h_tot : D_tot = 2 * (l_S - l_0)) 
  (h_ne : l_S ≠ l_0) : 
  1 - D_res / D_tot = 1 - (l_S - l_p) / (l_S - l_0) := by
  sorry

theorem theorem_206946_problem (n k : ℕ)
  (π : (Fin n → ℝ) × (Fin k → ℝ) → (Fin n → ℝ))
  (hπ : ∀ (x : Fin n → ℝ) (y : Fin k → ℝ), π (x, y) = x)
  (Ω : Set ((Fin n → ℝ) × (Fin k → ℝ)))
  (hΩ : IsOpen Ω) :
  IsOpen (π '' Ω) := by
  sorry









theorem theorem_207042_problem (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y] :
  Nonempty ((ℝ →L[ℝ] Y) ≃ₗᵢ[ℝ] Y) := by
  sorry













theorem theorem_207949_problem {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (A : Set (Submodule R M)) (hA : A = { N : Submodule R M | IsSimpleModule R (M ⧸ N) })
  (B : Set (Submodule R M)) (hB : B = { N : Submodule R M | IsSemisimpleModule R (M ⧸ N) }) :
  sInf A = sInf B := by
  sorry

theorem theorem_207617_problem (V : Type*) [AddCommGroup V] [Module ℝ V]
  [FiniteDimensional ℝ V] (h_dim : FiniteDimensional.finrank ℝ V = 10)
  (T : V →ₗ[ℝ] V)
  (U₀ U₁ U₂ U₃ : Submodule ℝ V)
  (h_dim0 : FiniteDimensional.finrank ℝ U₀ = 1)
  (h_dim1 : FiniteDimensional.finrank ℝ U₁ = 2)
  (h_dim2 : FiniteDimensional.finrank ℝ U₂ = 3)
  (h_dim3 : FiniteDimensional.finrank ℝ U₃ = 4)
  (h_indep : CompleteLattice.Independent ![U₀, U₁, U₂, U₃])
  (h_span : iSup ![U₀, U₁, U₂, U₃] = ⊤)
  (h_inv0 : Submodule.map T U₀ ≤ U₀)
  (h_inv1 : Submodule.map T U₁ ≤ U₁)
  (h_inv2 : Submodule.map T U₂ ≤ U₂)
  (h_inv3 : Submodule.map T U₃ ≤ U₃) :
  ∃ (b : Basis (Fin 10) ℝ V),
    let M := LinearMap.toMatrix b b T
    let part : Fin 10 → Fin 4 := fun i =>
      if i.val < 1 then 0
      else if i.val < 3 then 1
      else if i.val < 6 then 2
      else 3
    ∀ i j, part i ≠ part j → M i j = 0 := by
  sorry



theorem theorem_208034_problem (n : ℕ)
  (Sigma_mat Omega_mat sigma_I : Matrix (Fin n) (Fin n) ℝ)
  (h1 : Sigma_mat = sigma_I * Omega_mat * sigma_I)
  (h2 : sigma_I = 1) :
  Sigma_mat = Omega_mat := by
  sorry

theorem theorem_207593_problem (a b c : Fin 3 → ℝ) :
  (Matrix.det (Matrix.transpose ![a, b, c]))^2 =
    (Matrix.dotProduct a a) * (Matrix.dotProduct b b) * (Matrix.dotProduct c c) -
    (Matrix.dotProduct a b)^2 * (Matrix.dotProduct c c) -
    (Matrix.dotProduct b c)^2 * (Matrix.dotProduct a a) -
    (Matrix.dotProduct c a)^2 * (Matrix.dotProduct b b) +
    2 * (Matrix.dotProduct a b) * (Matrix.dotProduct b c) * (Matrix.dotProduct c a) := by
  sorry











theorem theorem_208557_problem
  (v : ℝ → ℝ → ℂ)
  (η : ℝ)
  (h_diff_A : ∀ β, Differentiable ℝ (fun A ↦ v A β))
  (h_diff_beta : ∀ A, Differentiable ℝ (fun β ↦ v A β))
  (h_pde : ∀ A β, deriv (fun x ↦ v x β) A = (β : ℂ) * deriv (fun y ↦ v A y) β)
  (h_ic : ∀ β, v 0 β = Complex.exp (Complex.I * (η : ℂ) * (β : ℂ))) :
  ∀ A β, v A β = Complex.exp (Complex.I * (η : ℂ) * (β : ℂ) * (Real.exp A : ℂ)) := by
  sorry

