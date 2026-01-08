import Mathlib
import Mathlib.Tactic



theorem theorem_338298_problem
  {R : Type*} [CommRing R]
  {m n : ℕ}
  (H : Matrix (Fin m) (Fin n) R)
  (X : Type*)
  (f : X → (Fin n → R)) :
  IsLinearMap R (fun (v : Fin n → R) ↦ Matrix.mulVec H v) := by
  sorry



theorem theorem_338955_problem (n : ℕ) (d : Fin n → ℝ) :
  sInf { v | ∃ x : Fin n → ℝ, v = 2 * (∑ i, |x i - d i|) + ∑ i, (d i - x i) } =
  sInf { w | ∃ (x y : Fin n → ℝ), (∀ i, -y i ≤ x i - d i ∧ x i - d i ≤ y i) ∧ 
    w = ∑ i, (2 * y i - x i) } + ∑ i, d i := by
  sorry

theorem theorem_338233_problem (ax ay az theta : ℝ)
  (h_unit : ax^2 + ay^2 + az^2 = 1) :
  let c := Real.cos theta
  let s := Real.sin theta
  let R : Matrix (Fin 3) (Fin 3) ℝ := !![
    1 + (1 - c) * (ax^2 - 1), -az * s + (1 - c) * ax * ay, ay * s + (1 - c) * ax * az;
    az * s + (1 - c) * ax * ay, 1 + (1 - c) * (ay^2 - 1), -ax * s + (1 - c) * ay * az;
    -ay * s + (1 - c) * ax * az, ax * s + (1 - c) * ay * az, 1 + (1 - c) * (az^2 - 1)
  ]
  let Rodrigues : Matrix (Fin 3) (Fin 3) ℝ := !![
    c + ax^2 * (1 - c), ax * ay * (1 - c) - az * s, ax * az * (1 - c) + ay * s;
    ax * ay * (1 - c) + az * s, c + ay^2 * (1 - c), ay * az * (1 - c) - ax * s;
    ax * az * (1 - c) - ay * s, ay * az * (1 - c) + ax * s, c + az^2 * (1 - c)
  ]
  R = Rodrigues := by
  sorry

theorem theorem_339171_problem
  {R : Type*} [Ring R]
  {B : Type*}
  {F : Type*} [AddCommGroup F] [Module R F]
  (f : (B →₀ R) →ₗ[R] F)
  (h : ∀ (M : Type*) [AddCommGroup M] [Module R M],
    Function.Bijective (fun (g : F →ₗ[R] M) ↦ g.comp f)) :
  Function.Bijective f := by
  sorry

theorem theorem_338928_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (ip : InnerProductSpace.Core ℝ E)
  (S : Set E) (hS : S = {x : E | ‖x‖ = 1})
  (S_E : Set E) (hS_E : S_E = {x : E | Real.sqrt (ip.inner x x) = 1}) :
  ∃ f : S ≃ₜ S_E, ∀ x : S, (f x : E) = (Real.sqrt (ip.inner x.1 x.1))⁻¹ • x.1 := by
  sorry

theorem theorem_338867_problem
  (c u v n : EuclideanSpace ℝ (Fin 3))
  (r m : ℝ)
  (hr : r > 0)
  (hu : ‖u‖ = 1)
  (hv : ‖v‖ = 1)
  (hn : ‖n‖ = 1)
  (huv : inner u v = (0 : ℝ))
  (hun : inner u n = (0 : ℝ))
  (hvn : inner v n = (0 : ℝ)) :
  let x := c + ((1 - m^2) / (1 + m^2) * r) • u + ((2 * m) / (1 + m^2) * r) • v
  dist x c = r ∧ inner (x - c) n = (0 : ℝ) := by
  sorry

theorem theorem_339602_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
  Matrix.mulVec A (Pi.single i 1) = fun j => A j i := by
  sorry







theorem theorem_340262_problem 
  (n : ℕ) 
  (A B : Fin n → ℝ) 
  (ε : ℝ) 
  (hε : 0 < ε) 
  (c : (Fin n → ℝ) → ℝ)
  (hc : ∀ V, c V = ∑ j, Real.sqrt ((V j)^2 + ε) * (B j)^2) 
  (i : Fin n) : 
  deriv (fun x => c (Function.update A i x)) (A i) = 
  (A i) / Real.sqrt ((A i)^2 + ε) * (B i)^2 := by
  sorry

theorem theorem_339828_problem
  (n : ℕ)
  (ι : Type*) [Fintype ι]
  (α : ι → ℝ)
  (y : ι → ℝ)
  (x : ι → Fin n → ℝ) :
  Matrix.dotProduct (∑ j, (α j * y j) • x j) (∑ i, (α i * y i) • x i) =
  ∑ i, ∑ j, α j * α i * y j * y i * Matrix.dotProduct (x j) (x i) := by
  sorry

theorem theorem_339277_problem 
  (n : ℕ) 
  (Ω : Set (Fin n → ℝ))
  (hΩ_open : IsOpen Ω)
  (hΩ_bounded : Bornology.IsBounded Ω)
  (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
  (Cc_inf : Set H)
  (Cc_2 : Set H)
  (H0 : Set H)
  (h_inf_subset_2 : Cc_inf ⊆ Cc_2)
  (h_2_subset_H0 : Cc_2 ⊆ H0)
  (h_inf_dense : closure Cc_inf = H0) :
  closure Cc_2 = H0 := by
  sorry

theorem theorem_339653_problem
  {R : Type*} [NormedRing R]
  (A B : R)
  (hA : IsUnit A)
  (hB : IsUnit B)
  (h_ne : A ≠ B)
  (h1 : ‖A - B‖ ≤ (‖Ring.inverse A‖)⁻¹)
  (h2 : ‖(1 : R) - Ring.inverse A * B‖ < 1) :
  ‖Ring.inverse A - Ring.inverse B‖ ≤
    ‖Ring.inverse A‖ * (‖(1 : R) - Ring.inverse A * B‖ / (1 - ‖(1 : R) - Ring.inverse A * B‖)) := by
  sorry







theorem theorem_340505_problem
  {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (f : V → W) (q₁ q₂ : V)
  (v : V) (hv : v = q₂ - q₁) :
  let path : ℝ → V := fun x ↦ q₁ + x • v
  let integrand : ℝ → W := fun x ↦ ‖v‖ • f (path x)
  let trapezoidal_approx : W := (1 / 2 : ℝ) • (integrand 0 + integrand 1)
  trapezoidal_approx = ‖v‖ • ((1 / 2 : ℝ) • (f q₁ + f q₂)) := by
  sorry

theorem theorem_339672_problem (x : Fin 242 → ℝ) (p : Fin 121 → ℝ) :
  let L : ℕ → ℝ := λ t => if h : 2 * t < 242 then x ⟨2 * t, h⟩ else 0
  let A : ℕ → ℝ := λ t => if h : 2 * t + 1 < 242 then x ⟨2 * t + 1, h⟩ else 0
  let c : Fin 242 → ℝ := λ i =>
    if h : i.val % 2 = 1 then
      p ⟨(i.val - 1) / 2, by
        have := i.isLt
        omega⟩
    else 0

  let lp_constraints :=
    (∀ t ∈ Finset.range 120, - L t - A t + L (t + 1) = 0) ∧
    (L 0 = 0) ∧
    (∀ t ∈ Finset.range 120, 0 ≤ L (t + 1) ∧ L (t + 1) ≤ 3) ∧
    (∀ t ∈ Finset.range 121, -1 ≤ A t ∧ A t ≤ 1)

  let original_constraints :=
    (L 0 = 0) ∧
    (∀ t ∈ Finset.range 120, L (t + 1) = L t + A t) ∧
    (∀ t ∈ Finset.range 121, 0 ≤ L t ∧ L t ≤ 3) ∧
    (∀ t ∈ Finset.range 121, -1 ≤ A t ∧ A t ≤ 1)

  (lp_constraints ↔ original_constraints) ∧
  ((∑ i : Fin 242, c i * x i) = ∑ t : Fin 121, p t * A t.val) := by
  sorry





theorem theorem_340114_problem
  (V : (Fin 3 → ℝ) → (Fin 3 → ℝ))
  (hV : ContDiff ℝ ⊤ V)
  (x : Fin 3 → ℝ) :
  fderiv ℝ V x = ∑ i : Fin 3, ∑ m : Fin 3,
    (fderiv ℝ (fun p => V p m) x (Pi.basisFun ℝ (Fin 3) i)) •
    (ContinuousLinearMap.smulRight
      (fderiv ℝ (fun q => q i) x)
      (Pi.basisFun ℝ (Fin 3) m)) := by
  sorry

theorem theorem_340627_problem {F : Type*} [Field F]
  (D : Set (F × F)) (hD : D = {x | x.1 = x.2})
  (A B : Set F) :
  D ≠ A ×ˢ B := by
  sorry

theorem theorem_340649_problem
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (h_inf : ¬ FiniteDimensional ℝ E) :
  ¬ ∃ f : E → ℝ, StrictConvexOn ℝ Set.univ f ∧ Continuous (fun x : WeakSpace ℝ E ↦ f x) := by
  sorry



theorem theorem_340925_problem (n : ℕ) (a : Fin n → ℝ) :
  Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.vecMulVec a a) = 1 + Matrix.dotProduct a a := by
  sorry

theorem theorem_340498_problem
  {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
  [TopologicalAddGroup X] [ContinuousSMul ℂ X]
  -- We include the real module structure to define convexity as is standard for complex spaces
  [Module ℝ X] [IsScalarTower ℝ ℂ X]
  (A B : Set X)
  (hA_nonempty : A.Nonempty)
  (hB_nonempty : B.Nonempty)
  (h_disj : Disjoint A B)
  (hA_conv : Convex ℝ A)
  (hB_conv : Convex ℝ B)
  (hA_compact : IsCompact A) :
  ∃ ψ : X →L[ℂ] ℂ, ∃ c : ℝ, ∀ a ∈ A, ∀ b ∈ B, (ψ a).re ≤ c ∧ c < (ψ b).re := by
  sorry















theorem theorem_341406_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [Field K]
  (S A : Matrix n n K)
  (t : K)
  (hS : IsUnit S)
  (h_inv : IsUnit (1 - (2 * t) • (A * S))) :
  (S⁻¹ - (2 * t) • A) * S * (1 - (2 * t) • (A * S))⁻¹ = 1 := by
  sorry















theorem theorem_341380_problem
  (E : Type*) [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E]
  (A : Set E) :
  closure (Submodule.span ℝ A : Set E) =
  ⋂₀ {H : Set E | ∃ (f : E →L[ℝ] ℝ), f ≠ 0 ∧ H = {x | f x = 0} ∧ A ⊆ H} := by
  sorry



























theorem theorem_342418_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (A B : H →L[ℂ] H) :
  ContinuousLinearMap.adjoint (A + B) = ContinuousLinearMap.adjoint A + ContinuousLinearMap.adjoint B := by
  sorry

theorem theorem_342374_problem
  {K : Type*} [Field K]
  {H : Type*} [Group H]
  {V : Type*} [AddCommGroup V] [Module K V]
  (π : Representation K H V)
  (v : V) (hv : v ≠ 0)
  (χ : H → Kˣ)
  (h_eigen : ∀ g : H, π g v = (χ g : K) • v) :
  (χ 1 = 1) ∧ (∀ g h : H, χ (g * h) = χ g * χ h) := by
  sorry



theorem theorem_342705_problem (n : ℕ) (a : Fin n → ℝ)
  (h_distinct : Function.Injective a) :
  LinearIndependent ℝ (fun i x ↦ Real.exp (a i * x)) := by
  sorry

theorem theorem_342617_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {n m : ℕ}
  (v : Basis (Fin n) K V)
  (w : Basis (Fin m) K W)
  (L1 : V →ₗ[K] W)
  (σ : Equiv.Perm (Fin n))
  (φ : V →ₗ[K] V)
  (hφ : ∀ i, φ (v i) = v (σ i))
  (L2 : V →ₗ[K] W)
  (hL2 : L2 = L1.comp φ)
  (M1 : Matrix (Fin m) (Fin n) K)
  (hM1 : M1 = LinearMap.toMatrix v w L1)
  (M2 : Matrix (Fin m) (Fin n) K)
  (hM2 : M2 = LinearMap.toMatrix v w L2) :
  M2 = M1.submatrix id σ := by
  sorry









theorem theorem_342832_problem (n : ℕ) (t : ℕ → ℝ)
  (hn : n ≥ 2)
  (h_sum : ∑ i in Finset.Icc 1 n, t i = 1)
  (h_tn : t n ≠ 1) :
  ∑ i in Finset.Icc 1 (n - 1), (t i / (1 - t n)) = 1 := by
  sorry







theorem theorem_343613_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (T : H →L[ℂ] H)
  (h : star T ∈ Set.centralizer {T}) :
  T * star T = star T * T := by
  sorry



















theorem theorem_343907_problem (t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ)
  (hA : A = !![t, t; 0, t]) :
  ∃! (DO : Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ),
    A = DO.1 + DO.2 ∧
    (∀ i j, i ≠ j → DO.1 i j = 0) ∧
    (∀ i, DO.2 i i = 0) ∧
    DO.1 = !![t, 0; 0, t] ∧
    DO.2 = !![0, t; 0, 0] := by
  sorry









theorem theorem_344263_problem {R : Type*} [CommRing R] {n : ℕ}
  (A : Matrix (Fin n) (Fin n) R) (i : Fin n) (c : R) :
  (Matrix.updateRow A i (c • (A i))).det = c * A.det := by
  sorry

theorem theorem_344328_problem :
  ∃ (n : ℕ) (V W : Matrix (Fin n) (Fin n) ℝ),
    Matrix.trace V = 0 ∧ Matrix.trace W = 0 ∧ Matrix.trace (V * W) ≠ 0 := by
  sorry

theorem theorem_344424_problem
  (R : Type*) [CommRing R]
  (M : Type*) [AddCommGroup M] [Module R M]
  (n : ℕ)
  (h_gen : ∃ f : Fin n → M, Submodule.span R (Set.range f) = ⊤) :
  ¬ ∃ g : (Fin (n + 1) → R) →ₗ[R] M, Function.Injective g := by
  sorry

















theorem theorem_345131_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  (w : V) (u : Module.Dual K V)
  (T : V →ₗ[K] V)
  (hT : ∀ x, T x = (u x) • w)
  (v : V) (z : Module.Dual K V) :
  z (T v) = (u v) * (z w) := by
  sorry



theorem theorem_344819_problem (x₁ x₂ x₃ : ℝ) :
  (abs (2 * x₁ - x₂ + 3 * x₃ + 1) + abs (x₂ + 2 * x₃ - 2) + abs (5 * x₂ - 3 * x₃) ≤ 10) ↔
  (∀ σ₁ σ₂ σ₃ : ℝ, σ₁ ∈ ({-1, 1} : Set ℝ) → σ₂ ∈ ({-1, 1} : Set ℝ) → σ₃ ∈ ({-1, 1} : Set ℝ) →
    σ₁ * (2 * x₁ - x₂ + 3 * x₃ + 1) + σ₂ * (x₂ + 2 * x₃ - 2) + σ₃ * (5 * x₂ - 3 * x₃) ≤ 10) := by
  sorry

