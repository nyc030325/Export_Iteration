import Mathlib
import Mathlib.Tactic











theorem theorem_75294_problem (a b c d : ℝ) :
  let z₁ : ℂ := Complex.mk a b
  let z₂ : ℂ := Complex.mk c d
  LinearIndependent ℝ ![z₁, z₂] ↔ a * d - b * c ≠ 0 := by
  sorry

theorem theorem_75469_problem
  (N d : ℕ)
  (x : Fin N → EuclideanSpace ℝ (Fin d))
  (h_unit : ∀ i, ‖x i‖ = 1)
  (density : Fin N → ℝ)
  (h_def : ∀ i, density i = ∑ j, max 0 (inner (x i) (x j))) :
  ∀ i, density i ≥ 0 := by
  sorry



theorem theorem_75957_problem
  (R : Type*) [CommRing R]
  (x : Fin 3 → R)
  (a : Ideal R)
  (h_indep : LinearIndependent (R ⧸ a) (fun i => Ideal.Quotient.mk a (x i))) :
  let y := fun i => Ideal.Quotient.mk a (x i)
  Ideal.span {y 2} < Ideal.span {y 1, y 2} ∧
  Ideal.span {y 1, y 2} < Ideal.span {y 0, y 1, y 2} := by
  sorry



theorem theorem_75490_problem (n : ℕ) (A C1 C2 C3 : Matrix (Fin n) (Fin n) ℝ) :
  C3 * A^3 + C2 * A^2 + C1 * A = ((C3 * A + C2) * A + C1) * A := by
  sorry



theorem theorem_75438_problem
  (M₁ M₂ K₁ K₂ B : ℝ)
  (s : ℂ)
  (X₁ X₂ F : ℂ)
  (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hB : 0 < B)
  (h_eq1 : F = ↑M₂ * s^2 * X₂ + ↑K₂ * (X₂ - X₁))
  (h_eq2 : 0 = ↑M₁ * s^2 * X₁ + ↑K₂ * (X₁ - X₂) + ↑K₁ * X₁ + ↑B * s * X₁)
  (hF : F ≠ 0)
  (h_denom1 : ↑M₂ * s^2 + ↑K₂ ≠ 0)
  (h_denom2 : ↑M₁ * s^2 + ↑K₂ + ↑K₁ + ↑B * s ≠ 0)
  (h_denom3 : 1 - (↑K₂ ^ 2) / ((↑M₂ * s^2 + ↑K₂) * (↑M₁ * s^2 + ↑K₂ + ↑K₁ + ↑B * s)) ≠ 0) :
  X₁ / F = (↑K₂ / ((↑M₂ * s^2 + ↑K₂) * (↑M₁ * s^2 + ↑K₂ + ↑K₁ + ↑B * s))) /
           (1 - (↑K₂ ^ 2) / ((↑M₂ * s^2 + ↑K₂) * (↑M₁ * s^2 + ↑K₂ + ↑K₁ + ↑B * s))) := by
  sorry













theorem theorem_75819_problem (n : ℕ) (U : Set (Fin n → ℝ))
  (h_open : IsOpen U)
  (h_mid : ∀ x ∈ U, ∀ y ∈ U, midpoint ℝ x y ∈ U) :
  Convex ℝ U := by
  sorry



theorem theorem_76386_problem
  (𝕜 : Type*) [RCLike 𝕜]
  (U : Type*) [NormedAddCommGroup U] [NormedSpace 𝕜 U]
  (h_inf : ¬ FiniteDimensional 𝕜 U) :
  ¬ TopologicalSpace.SeparableSpace (U →L[𝕜] U) := by
  sorry

theorem theorem_76211_problem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] (A : E →L[ℂ] E) :
  spectralRadius ℂ A ≤ ENNReal.ofReal ‖A‖ := by
  sorry







theorem theorem_76814_problem
  {n : Type*} [DecidableEq n] [Fintype n]
  {R : Type*} [CommRing R]
  (P : Matrix n n R)
  (σ : Equiv.Perm n)
  (t : ℕ)
  (hP : ∀ i j, P i j = if j = σ i then (1 : R) else 0)
  (ht : (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ)^t) :
  P.det = (-1 : R)^t := by
  sorry

theorem theorem_76754_problem
  (n : ℕ)
  (p : ℝ) (hp : 1 < p)
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (U : Set E)
  (hU_bounded : Bornology.IsBounded U)
  -- We represent the condition "boundary of class C1" and the specific structure of the spaces abstractly
  (is_C1_boundary : Set E → Prop)
  (hU_C1 : is_C1_boundary U)
  -- The Sobolev Space W^{1,p}(U)
  (W1p : Type*) [NormedAddCommGroup W1p] [NormedSpace ℝ W1p]
  -- The Boundary L^p space L^p(\partial U)
  (Lp_boundary : Type*) [NormedAddCommGroup Lp_boundary] [NormedSpace ℝ Lp_boundary]
  -- The Trace Operator T
  (T : W1p →L[ℝ] Lp_boundary)
  -- The set of smooth functions with compact support C_c^\infty(U) viewed as a subset of W^{1,p}
  (CcInf : Set W1p)
  -- W_0^{1,p}(U) is the closure of C_c^\infty(U)
  (W01p : Set W1p)
  (h_W01p_def : W01p = closure CcInf)
  -- Property of the Trace operator: it vanishes on functions with compact support
  (hT_vanish : ∀ v ∈ CcInf, T v = 0)
  -- The element u
  (u : W1p) :
  u ∈ W01p ↔ T u = 0 := by
  sorry

theorem theorem_76451_problem
  (p y₁ y₂ : ℝ → ℝ)
  (hp : ContDiff ℝ 1 p)
  (hy₁ : ContDiff ℝ 2 y₁)
  (hy₂ : ContDiff ℝ 2 y₂)
  (W : ℝ → ℝ)
  (hW : W = fun x => y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) :
  deriv (fun x => p x * W x) =
    fun x => y₁ x * deriv (fun t => p t * deriv y₂ t) x -
             y₂ x * deriv (fun t => p t * deriv y₁ t) x := by
  sorry

theorem theorem_76577_problem {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (T : V →ₗ[F] V) {ι : Type*} (b : Basis ι F V)
  (h : ∀ i, T (b i) = 0) :
  ∀ w : V, T w = 0 := by
  sorry





theorem theorem_76210_problem (n k : ℕ) (hk : k ≤ n)
  (A : Matrix (Fin n) (Fin n) ℂ)
  (Ak : Matrix (Fin k) (Fin k) ℂ)
  (hAk : Ak = A.submatrix (Fin.castLE hk) (Fin.castLE hk))
  (h_dom : ∀ i : Fin k, ∑ j in Finset.univ.erase i, ‖Ak i j‖ < ‖Ak i i‖) :
  ∀ z ∈ spectrum ℂ Ak, ∃ i : Fin k, ‖z - Ak i i‖ ≤ ∑ j in Finset.univ.erase i, ‖Ak i j‖ := by
  sorry







theorem theorem_76929_problem (A : Matrix (Fin 4) (Fin 4) ℝ)
  (hA : A = !![1, -1, 0, 0;
               -1, 1, 0, 0;
               0, 0, 1, -1;
               0, 0, -1, 1]) :
  FiniteDimensional.finrank ℝ (LinearMap.ker (Matrix.toLin' A)) = 2 := by
  sorry











theorem theorem_76852_problem
  (k n : ℕ)
  (a : Fin k → ℝ)
  (b : Fin n → ℝ)
  (B : Set (Fin k → ℝ))
  (V : Set (Fin n → ℝ))
  (g : (Fin k → ℝ) → (Fin n → ℝ))
  (f : ((Fin k → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ))
  (hB_open : IsOpen B)
  (ha : a ∈ B)
  (hV_open : IsOpen V)
  (hb : b ∈ V)
  (hg_img : ∀ x ∈ B, g x ∈ V)
  (hf_cont : Continuous f)
  (hf_eq : ∀ x ∈ B, f (x, g x) = 0) :
  ∀ x ∈ B, ∀ y ∈ V, f (x, y) = 0 → y = g x := by
  sorry

theorem theorem_76900_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (A : Set E) (hA : IsOpen A)
  (a : E) (ha : a ∈ A)
  (v : E) (hv : v ≠ 0) :
  ∃ r : ℝ, r > 0 ∧ ∀ t : ℝ, 0 ≤ t ∧ t < r / ‖v‖ →
    (a + t • v ∈ A ∧ (t ≠ 0 → a + t • v ≠ a)) := by
  sorry

theorem theorem_77279_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (U : Submodule K V) (u : V) (h : u ∈ U) :
  {w | ∃ v ∈ U, w = u + v} = (U : Set V) := by
  sorry





theorem theorem_77427_problem
  {R : Type*} [CommRing R]
  {n : ℕ}
  (A : Matrix (Fin n) (Fin n) R)
  (q_dot q_ddot : Matrix (Fin n) (Fin 1) R) :
  (q_ddot.transpose * A * q_dot).transpose = q_dot.transpose * A.transpose * q_ddot := by
  sorry



theorem theorem_77176_problem
  (n m : ℕ)
  (f : (Fin n → ℝ) → (Fin m → ℝ))
  (γ : ℝ → (Fin n → ℝ))
  (t₀ : ℝ)
  (hf : Differentiable ℝ f)
  (hγ : Differentiable ℝ γ) :
  fderiv ℝ (f ∘ γ) t₀ = (fderiv ℝ f (γ t₀)).comp (fderiv ℝ γ t₀) := by
  sorry

theorem theorem_77318_problem
  (K : Type*) [Field K]
  (R : Type*) [Ring R]
  (V : Type*) [AddCommGroup V] [Module K V]
  (f : R →+* (V →ₗ[K] V)) :
  { g : V →ₗ[K] V | ∀ (r : R) (v : V), g ((f r) v) = (f r) (g v) } =
  { g : V →ₗ[K] V | ∀ r : R, g * (f r) = (f r) * g } := by
  sorry

theorem theorem_76954_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
  ∑ i : Fin n, ∑ j : Fin n, (if i < j then (A i i * A j j - A i j * A j i) else 0) =
  (1 / 2 : ℝ) * ((Matrix.trace A) ^ 2 - Matrix.trace (A ^ 2)) := by
  sorry





theorem theorem_77798_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
  (h_tri_A : ∃ U : Matrix (Fin n) (Fin n) ℂ, IsUnit U ∧ ∀ i j : Fin n, j < i → (U⁻¹ * A * U) i j = 0)
  (h_tri_B : ∃ V : Matrix (Fin n) (Fin n) ℂ, IsUnit V ∧ ∀ i j : Fin n, j < i → (V⁻¹ * B * V) i j = 0)
  (h_comm : A * B = B * A) :
  ∃ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P ∧
    (∀ i j : Fin n, j < i → (P⁻¹ * A * P) i j = 0) ∧
    (∀ i j : Fin n, j < i → (P⁻¹ * B * P) i j = 0) := by
  sorry





theorem theorem_77642_problem
  (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (f g : V →ₗ[ℝ] ℝ)
  (hf : f ≠ 0)
  (hg : g ≠ 0)
  (h_cond : ∀ x : V, 0 ≤ f x → 0 ≤ g x) :
  ∃ α : ℝ, f = α • g := by
  sorry





theorem theorem_78115_problem (n d : ℕ)
  (T : EuclideanSpace ℝ (Fin n → Fin d)) :
  ‖T‖ ^ 2 = ∑ i, (T i) ^ 2 := by
  sorry





















theorem theorem_78508_problem
  (a b : ℝ)
  (K : Fin 3 → ℝ → ℝ)
  (X : Fin 3 → ℝ)
  -- Assume integrability for the moments to ensure the integrals are well-defined
  (h_int : ∀ i j : Fin 3, IntervalIntegrable (fun x => K i x * x ^ (j : ℕ)) volume a b)
  -- The invertibility assumption derived from the problem/solution context
  (h_nonsingular : (Matrix.of (fun i j : Fin 3 => ∫ x in a..b, K i x * x ^ (j : ℕ))).det ≠ 0) :
  -- The conclusion: The coefficients c are uniquely determined
  ∃! c : Fin 3 → ℝ,
    ∀ i : Fin 3, ∫ x in a..b, K i x * (∑ j : Fin 3, c j * x ^ (j : ℕ)) = X i := by
  sorry

theorem theorem_78386_problem (m n : ℕ) :
  let M : Set ℕ := { k | 1 ≤ k ∧ k ≤ m }
  let N : Set ℕ := { k | 1 ≤ k ∧ k ≤ n }
  Nonempty (↥M × ↥N → ℝ) := by
  sorry





theorem theorem_79039_problem {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]
  (A B : X →ₗ[K] Y) :
  LinearMap.range (A + B) ≤ LinearMap.range A + LinearMap.range B := by
  sorry



theorem theorem_79024_problem {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [CommRing R]
  (A B : Matrix n n R)
  (hA : IsUnit A)
  (hAB : IsUnit (A + B)) :
  (A + B)⁻¹ = A⁻¹ - (A + B)⁻¹ * B * A⁻¹ := by
  sorry



theorem theorem_79060_problem :
  let U : Matrix (Fin 4) (Fin 4) ℂ := (1 / (Real.sqrt 2 : ℂ)) • !![1, 0, 1, 0;
                                                                   0, 1, 0, 1;
                                                                   -Complex.I, 0, Complex.I, 0;
                                                                   0, -Complex.I, 0, Complex.I]
  U * U.conjTranspose = 1 ∧ U.conjTranspose * U = 1 := by
  sorry













theorem theorem_79677_problem (k : ℕ) (hk : 0 < k)
  (t : Fin k → ℝ) (h_distinct : Function.Injective t) :
  LinearIndependent ℝ (fun i : Fin k ↦ (fun j : Fin k ↦ (t i) ^ (j : ℕ))) := by
  sorry



theorem theorem_80089_problem {n : ℕ} {R : Type*} [Field R]
  (K P : Matrix (Fin n) (Fin n) R)
  (h1 : IsUnit (1 - K * P))
  (h2 : IsUnit (1 - P * K)) :
  K = (1 - K * P) * K * (1 - P * K)⁻¹ := by
  sorry

theorem theorem_79685_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  (Λ : V →L[𝕜] V)
  (ε δ : ℝ)
  (hε : 0 < ε)
  (hδ : 0 < δ)
  (h : ∀ x : V, ‖x‖ = δ → ‖Λ x‖ < ε) :
  ‖Λ‖ ≤ ε / δ := by
  sorry







theorem theorem_80113_problem
  (𝕜 : Type*) [Field 𝕜] [TopologicalSpace 𝕜]
  (X : Type*) [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
  [ContinuousAdd X] [ContinuousSMul 𝕜 X]
  (Y : Set X) :
  closure Y ⊆ {x : X | ∀ (l : X →L[𝕜] 𝕜), (∀ y ∈ Y, l y = 0) → l x = 0} := by
  sorry

theorem theorem_80126_problem :
  ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    A.IsSymm ∧
    (∀ i j, 0 ≤ A i j) ∧
    ∃ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' A) μ ∧ μ < 0 := by
  sorry







theorem theorem_80547_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  (T : V →L[𝕜] V)
  (A : Set V)
  (t : ℝ)
  (h1 : ∀ x ∈ A, ‖T x‖ ≤ t)
  (h2 : Metric.ball 0 1 ⊆ A) :
  ‖T‖ ≤ t := by
  sorry

theorem theorem_80185_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (p : V → ℝ)
  (hp_add : ∀ x y : V, p (x + y) ≤ p x + p y)
  (hp_mul : ∀ (c : ℝ) (x : V), 0 ≤ c → p (c • x) = c * p x)
  (W : Subspace ℝ V)
  (f : W →ₗ[ℝ] ℝ)
  (hf : ∀ w : W, f w ≤ p w) :
  ∃ g : V →ₗ[ℝ] ℝ, (∀ w : W, g w = f w) ∧ (∀ v : V, g v ≤ p v) := by
  sorry

