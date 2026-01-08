import Mathlib
import Mathlib.Tactic



theorem theorem_1950_problem {n : ℕ}
  (g_tensor : Matrix (Fin n) (Fin n) ℝ)
  (A h_tensor : Matrix (Fin n) (Fin n) ℝ)
  (hg_inv : g_tensor.det ≠ 0)
  (hA : A = g_tensor.adjugate) :
  ∑ i, ∑ j, A i j * h_tensor i j = g_tensor.det * ∑ i, ∑ j, g_tensor⁻¹ i j * h_tensor i j := by
  sorry









theorem theorem_918_problem
  {D : Type*} [CommRing D] [IsDomain D]
  {n : ℕ}
  (A B : Set (Matrix (Fin n) (Fin n) D))
  (hA : A ≠ {0})
  (hB : B ≠ {0}) :
  {P | ∃ M ∈ A, ∃ N ∈ B, P = M * N} ≠ {0} := by
  sorry









theorem theorem_2948_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  {n : ℕ} (b : Basis (Fin n) F V)
  (v : V) (ω : Module.Dual F V) :
  ω v = ∑ i : Fin n, (b.dualBasis.repr ω i) * (b.repr v i) := by
  sorry







theorem theorem_882_problem (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x y : EuclideanSpace ℝ (Fin n)) (h : DifferentiableAt ℝ f x) :
  fderiv ℝ f x y = inner (gradient f x) y := by
  sorry

theorem theorem_2225_problem
  (K : Type*) [Field K]
  (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Z : Type*) [Fintype Z] [DecidableEq Z]
  (F : Z → Type*) [∀ z, AddCommGroup (F z)] [∀ z, Module K (F z)] [∀ z, FiniteDimensional K (F z)]
  (n m : ℕ)
  (hV : FiniteDimensional.finrank K V = n)
  (hF : ∀ z, FiniteDimensional.finrank K (F z) = m)
  (h_cond : n < m * Fintype.card Z)
  (φ : V →ₗ[K] DirectSum Z F) :
  ¬ Function.Surjective φ := by
  sorry





theorem theorem_444_problem :
  ∃ (n : ℕ) (T S : Matrix (Fin n) (Fin n) ℝ), T * (S * T) = T ∧ S * T ≠ 1 := by
  sorry



theorem theorem_779_problem 
  {K U V W : Type*} [Field K] 
  [AddCommGroup U] [Module K U] 
  [AddCommGroup V] [Module K V] 
  [AddCommGroup W] [Module K W] 
  (A : V →ₗ[K] W) (B : U →ₗ[K] V) (u : U) 
  (h : ∃ v : V, B u = v ∧ A v = 0) : 
  (A ∘ₗ B) u = 0 := by
  sorry



theorem theorem_203_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (v w : H) :
  inner v w = (1 / 4 : ℂ) * ((‖v + w‖ : ℂ) ^ 2 - (‖v - w‖ : ℂ) ^ 2) +
    (Complex.I / 4) * ((‖v + Complex.I • w‖ : ℂ) ^ 2 - (‖v - Complex.I • w‖ : ℂ) ^ 2) := by
  sorry

theorem theorem_2799_problem
  {R : Type*} [Field R]
  (p k n : ℕ)
  (K : Matrix (Fin p) (Fin k) R)
  (X : Matrix (Fin n) (Fin p) R)
  (h1 : IsUnit (X.transpose * X).det)
  (h2 : IsUnit (K.transpose * (X.transpose * X)⁻¹ * K).det) :
  K.transpose.rank = k := by
  sorry





theorem theorem_2524_problem
  {R : Type*} [CommRing R]
  (m : ℕ)
  (A : ℕ → ℕ → R)
  (i j : ℕ)
  (hj : 1 ≤ j ∧ j ≤ m)
  (delta : ℕ → ℕ → R)
  (h_delta : ∀ a b, delta a b = if a = b then 1 else 0) :
  ∑ k in Finset.Icc 1 m, A k i * delta j k = A j i := by
  sorry





theorem theorem_723_problem (B_z v_dx v_dy : ℝ) :
  let v : Matrix (Fin 2) (Fin 1) ℝ := !![v_dx; v_dy]
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, B_z; -B_z, 0]
  B_z • (!![v_dy; -v_dx] : Matrix (Fin 2) (Fin 1) ℝ) = B * v := by
  sorry











theorem theorem_4229_problem (n m : ℕ)
  (x : Fin m → Fin n → ℝ)
  (θ : Fin n → ℝ)
  (ε : Fin m → ℝ)
  (hε : ∀ i, ε i = -1 ∨ ε i = 1) :
  |∑ i, ε i * (∑ j, x i j * θ j)| ≤
  (∑ j, |θ j|) *
  ((Finset.univ.image (fun i => (Finset.univ.image (fun j => |x i j|)).max.getD 0)).max.getD 0) *
  (∑ i, |ε i|) := by
  sorry





theorem theorem_2063_problem {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] (W₁ W₂ : Submodule F V) :
  (∀ w₁ ∈ W₁, ∀ w₂ ∈ W₂, w₁ + w₂ = 0 → w₁ = 0 ∧ w₂ = 0) ↔ W₁ ⊓ W₂ = ⊥ := by
  sorry



















theorem theorem_3751_problem
  (m n : ℕ)
  (Ω : Type*)
  (E : (Ω → ℝ) → ℝ)
  (Cov : (Ω → ℝ) → (Ω → ℝ) → ℝ)
  (M : Fin m → Fin n → Ω → ℝ)
  (d : Fin n → Ω → ℝ)
  (f : Fin m → Ω → ℝ)
  -- Conditions regarding the Expectation operator (Linearity)
  (h_lin_add : ∀ X Y, E (X + Y) = E X + E Y)
  (h_lin_smul : ∀ (c : ℝ) X, E (fun ω ↦ c * X ω) = c * E X)
  -- Condition defining Covariance
  (h_cov_def : ∀ X Y, Cov X Y = E (X * Y) - E X * E Y)
  -- Definition of the vector f
  (h_f_def : ∀ i, f i = fun ω ↦ ∑ j : Fin n, M i j ω * d j ω)
  -- Condition: Cov[Mij, dk] = 0 for all i, j, k
  (h_uncorr : ∀ i j k, Cov (M i j) (d k) = 0)
  -- Condition: Independence sufficient for higher moments factorization (implied by problem context for product expansions)
  (h_indep : ∀ i j k l, E (M i k * M j l * d k * d l) = E (M i k * M j l) * E (d k * d l))
  -- Condition: Neglecting second-order terms (the approximation assumption)
  (h_approx : ∀ i j k l, Cov (M i k) (M j l) * Cov (d k) (d l) = 0) :
  -- Conclusion: The formula for Cov[fi, fj]
  ∀ i j, Cov (f i) (f j) = 
    ∑ k : Fin n, ∑ l : Fin n, 
      (E (M i k) * E (M j l) * Cov (d k) (d l) + 
       E (d k) * E (d l) * Cov (M i k) (M j l)) := by
  sorry





















theorem theorem_3177_problem (R C : Finset ℝ)
  (hR : ∑ r in R, r = 0)
  (hC : ∑ c in C, c = 0) :
  ∑ r in R, ∑ c in C, r * c = 0 := by
  sorry













theorem theorem_3719_problem (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℝ)
  (h : m = 2) :
  IsUnit (A.transpose * A) ↔ Matrix.det (A.transpose * A) ≠ 0 := by
  sorry





theorem theorem_5752_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (A : V →ₗ[F] V) (u : V)
  (hu : u ≠ 0)
  (h_not_inv : A u ≠ u) :
  A u ≠ (1 : F) • u := by
  sorry

theorem theorem_7472_problem
  (X Y : Type*)
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  (T : X →L[ℝ] Y)
  (h : Function.Surjective T) :
  IsOpenMap T := by
  sorry









theorem theorem_4819_problem (n : ℕ) (a b : Fin n → ℝ) :
  (∑ i, a i * b i)^2 ≤ (∑ j, a j * a j) * (∑ k, b k * b k) := by
  sorry

theorem theorem_5029_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  {G : Type*} [Group G] [Fintype G]
  (ρ : G →* (V ≃ₗ[K] V))
  (v : V)
  (x : V)
  (hx_def : x = ∑ g : G, ρ g v)
  (hx_nonzero : x ≠ 0)
  (W : Submodule K V)
  (hW : W = Submodule.span K (Set.range (fun g ↦ ρ g x))) :
  ∀ g : G, Submodule.map (ρ g).toLinearMap W ≤ W := by
  sorry

theorem theorem_5264_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (ϕ : V →L[ℂ] V)
  (h_normal : Commute ϕ (star ϕ)) :
  ∃ p : Polynomial ℂ, star ϕ = Polynomial.aeval ϕ p := by
  sorry

















theorem theorem_7075_problem 
  {K : Type*} [Field K] 
  (n : ℕ) 
  (A : Matrix (Fin n) (Fin n) K) 
  (h_torsion : (2 : K) ≠ 0)
  (h1 : A * A.transpose = -1) 
  (h2 : A.det = 1) : 
  A.trace = 0 := by
  sorry















theorem theorem_7855_problem
  {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  (T : V →L[𝕜] V) (a : ℕ → V)
  (h : Summable a) :
  T (∑' n, a n) = ∑' n, T (a n) := by
  sorry









