import Mathlib
import Mathlib.Tactic



theorem theorem_357383_problem (A : Matrix (Fin 2) (Fin 2) ℝ) (h : A.det > 0) :
  ∃ path : ℝ → Matrix (Fin 2) (Fin 2) ℝ,
    ContinuousOn path (Set.Icc 0 1) ∧
    path 0 = A ∧
    path 1 = 1 ∧
    ∀ t ∈ Set.Icc 0 1, (path t).det > 0 := by
  sorry









theorem theorem_357722_problem
  (n : ℕ)
  (C : Set (EuclideanSpace ℝ (Fin n)))
  (hC_nonempty : C.Nonempty)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (hP : ∀ z, P z ∈ C ∧ ∀ x ∈ C, ‖z - P z‖ ≤ ‖z - x‖) :
  ∀ z₁ z₂, ‖P z₁ - P z₂‖ ≤ ‖z₁ - z₂‖ := by
  sorry

theorem theorem_357788_problem
  (N n : ℕ)
  (Q : Matrix (Fin N) (Fin N) ℝ)
  (hQ : (1 - Q).det ≠ 0) :
  let I_N : Matrix (Fin N) (Fin N) ℝ := 1
  let M := (1 - Q)⁻¹ * (Q.transpose - 1)
  let A : Matrix (Fin n × Fin N) (Fin n × Fin N) ℝ := fun (i, k) (j, l) =>
    if i = j then I_N k l
    else if i < j then Q k l
    else Q.transpose k l
  let sum_M := ∑ k in Finset.Icc 1 (n - 1), (-M)^k
  A.det = (1 + Q * sum_M).det * ((1 - Q).det) ^ (n - 1) := by
  sorry





theorem theorem_358048_problem (n : ℕ) (hn : n ≥ 2) (M : Matrix (Fin n) (Fin n) ℝ)
  (hM : M.det = 1) :
  ∃ L : List (Matrix (Fin n) (Fin n) ℝ),
    (∀ E ∈ L, ∃ (i j : Fin n) (a : ℝ), i ≠ j ∧ E = 1 + Matrix.stdBasisMatrix i j a) ∧
    L.prod = M := by
  sorry



















theorem theorem_358550_problem (k : Type*) [Field k] :
  Nonempty ((Module.Dual k (Polynomial k)) ≃ₗ[k] (PowerSeries k)) := by
  sorry







theorem theorem_358546_problem (N M K P Q R : ℕ)
  (X : Fin P → Fin N → ℝ)
  (Y : Fin Q → Fin M → ℝ)
  (Z : Fin R → Fin K → ℝ)
  (hX : ∀ p i, X p i = (i : ℝ) ^ (p : ℕ))
  (hY : ∀ q j, Y q j = (j : ℝ) ^ (q : ℕ))
  (hZ : ∀ r k, Z r k = (k : ℝ) ^ (r : ℕ))
  (f : Fin N → Fin M → Fin K → ℝ)
  (m : Fin P → Fin Q → Fin R → ℝ)
  (hm : ∀ p q r, m p q r = ∑ i : Fin N, ∑ j : Fin M, ∑ k : Fin K,
    X p i * Y q j * Z r k * f i j k) :
  ∃ (L1 : (Fin N → ℝ) →ₗ[ℝ] (Fin P → ℝ))
    (L2 : (Fin M → ℝ) →ₗ[ℝ] (Fin Q → ℝ))
    (L3 : (Fin K → ℝ) →ₗ[ℝ] (Fin R → ℝ)),
    let f_tens := ∑ i : Fin N, ∑ j : Fin M, ∑ k : Fin K,
      f i j k • (Pi.single i 1 ⊗ₜ[ℝ] (Pi.single j 1 ⊗ₜ[ℝ] Pi.single k 1))
    let m_tens := ∑ p : Fin P, ∑ q : Fin Q, ∑ r : Fin R,
      m p q r • (Pi.single p 1 ⊗ₜ[ℝ] (Pi.single q 1 ⊗ₜ[ℝ] Pi.single r 1))
    TensorProduct.map L1 (TensorProduct.map L2 L3) f_tens = m_tens := by
  sorry

theorem theorem_358615_problem
  {R : Type*} [CommRing R]
  {V : Type*} [AddCommGroup V] [Module R V]
  (P : V →ₗ[R] V)
  (G_plus : V →ₗ[R] V)
  (h : P.comp G_plus = LinearMap.id) :
  ∀ φ : V, P (G_plus φ) = φ := by
  sorry







theorem theorem_358627_problem (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
  IsMinOn (fun z => (1 / 2 : ℝ) * ‖z - (x - y)‖ ^ 2) 
    {z : EuclideanSpace ℝ (Fin n) | ‖z‖ ≤ 1} 
    ((min 1 (‖x - y‖)⁻¹) • (x - y)) := by
  sorry



theorem theorem_358570_problem (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) :
  ∃ C : Matrix (Fin n) (Fin n) ℝ, IsUnit C ∧ C * B * C⁻¹ = B.transpose := by
  sorry



theorem theorem_359051_problem
  (F : Type*) [RCLike F]
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace F V]
  [FiniteDimensional F V] :
  ∃ (n : ℕ) (e : Basis (Fin n) F V), Orthonormal F e := by
  sorry





theorem theorem_358776_problem
  {K : Type*} [NontriviallyNormedField K]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y]
  (f : X →L[K] Y) (x : X) :
  ‖f x‖ ≤ ‖f‖ * ‖x‖ := by
  sorry



theorem theorem_358949_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (x₁ x_j x_k : E)
  (x₁j x₁k : E)
  (d₁j d₁k d_jk : ℝ)
  (h₁ : x₁j = x_j - x₁)
  (h₂ : x₁k = x_k - x₁)
  (h₃ : d₁j = ‖x_j - x₁‖)
  (h₄ : d₁k = ‖x_k - x₁‖)
  (h₅ : d_jk = ‖x_k - x_j‖) :
  inner x₁j x₁k = (1 / 2 : ℝ) * (d₁j ^ 2 + d₁k ^ 2 - d_jk ^ 2) := by
  sorry







theorem theorem_359107_problem (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
  (hB : IsUnit B)
  (norm : Matrix (Fin n) (Fin n) ℝ → ℝ)
  (h_norm_nonneg : ∀ X, 0 ≤ norm X)
  (h_norm_submul : ∀ X Y, norm (X * Y) ≤ norm X * norm Y)
  (h_norm_def : ∀ X, norm X = 0 ↔ X = 0) :
  (norm B)⁻¹ ≤ norm (B⁻¹) := by
  sorry



theorem theorem_359211_problem :
  ∃ v1 v2 v3 : Fin 3 → ℝ, crossProduct v1 v2 = crossProduct v1 v3 ∧ crossProduct v2 v3 ≠ 0 := by
  sorry





theorem theorem_360052_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (C₁ C₂ : Set E)
  (hC₁_comp : IsCompact C₁) (hC₁_conv : Convex ℝ C₁)
  (hC₂_comp : IsCompact C₂) (hC₂_conv : Convex ℝ C₂)
  (a : E) (b : ℝ)
  (h_sep1 : ∀ x ∈ C₁, inner a x < b)
  (h_sep2 : ∀ x ∈ C₂, inner a x > b) :
  ∃ ε > 0, ∀ x ∈ C₁, ∀ y ∈ C₂, dist x y ≥ ε := by
  sorry















theorem theorem_359665_problem
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix m n ℂ)
  (norm : Matrix m n ℂ → ℝ)
  (h_norm_def : ∀ M, norm M = 0 ↔ M = 0)
  (h_norm_smul : ∀ (c : ℂ) (M : Matrix m n ℂ), norm (c • M) = Complex.abs c * norm M)
  (h_norm_tri : ∀ M N, norm (M + N) ≤ norm M + norm N)
  (h_norm_inv : ∀ (U : Matrix m m ℂ) (V : Matrix n n ℂ) (M : Matrix m n ℂ),
    U ∈ Matrix.unitaryGroup m ℂ → V ∈ Matrix.unitaryGroup n ℂ → norm (U * M * V) = norm M)
  (h_norm_std : ∀ i j, norm (Matrix.stdBasisMatrix i j 1) = 1) :
  ∀ i j, norm A ≥ Complex.abs (A i j) := by
  sorry



theorem theorem_360200_problem (n : ℕ)
  (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  (v₁ v₂ : Fin n → ℝ) :
  A '' {x | ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ x = (1 - t) • v₁ + t • v₂} =
  {x | ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ x = (1 - t) • (A v₁) + t • (A v₂)} := by
  sorry













theorem theorem_360134_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (v : V)
  (c : ℝ → (V →L[ℝ] V))
  (t : ℝ)
  (hc : DifferentiableAt ℝ c t) :
  deriv (fun s => c s v) t = (deriv c t) v := by
  sorry

theorem theorem_360720_problem
  (K : Type*) [Field K]
  (R : Type*) [CommRing R] [Algebra R K]
  (A : Type*) [Ring A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Module.Finite K A]
  (a : A) (h : IsIntegral R a) :
  IsIntegral R (LinearMap.trace K A (LinearMap.mulLeft K a)) := by
  sorry





theorem theorem_360242_problem (x₁ y₁ x₂ y₂ u₁ v₁ : ℝ)
  (l₁ : ℝ → ℝ × ℝ)
  (l₂ : ℝ → ℝ × ℝ)
  (h_l₁ : ∀ t, l₁ t = ((x₁ + x₂) / 2 + t * (y₁ - y₂), (y₁ + y₂) / 2 + t * (x₂ - x₁)))
  (h_l₂ : ∀ t, l₂ t = (x₁ + t * u₁, y₁ + t * v₁))
  (C : ℝ × ℝ)
  (h_dist : dist C (x₁, y₁) = dist C (x₂, y₂))
  (h_on_l₂ : ∃ t, l₂ t = C)
  (h_distinct : (x₁, y₁) ≠ (x₂, y₂)) :
  ∃ t₁ t₂, l₁ t₁ = l₂ t₂ ∧ l₂ t₂ = C := by
  sorry

theorem theorem_360685_problem
  (ComplexVectorBundle RealVectorBundle : Type*)
  (Connection : ComplexVectorBundle → Type*)
  (Curvature : Type*)
  (underlying_real : ComplexVectorBundle → RealVectorBundle)
  (curvature : ∀ {E : ComplexVectorBundle}, Connection E → Curvature)
  (tr_curvature_sq : Curvature → ℂ)
  (p1 : RealVectorBundle → ℝ)
  (E : ComplexVectorBundle)
  (A : Connection E) :
  p1 (underlying_real E) = - (tr_curvature_sq (curvature A) / (4 * Real.pi ^ 2 : ℂ)).re := by
  sorry



theorem theorem_360353_problem (n : ℕ) (J : (Fin n → ℂ) → ℂ)
  -- We define abstract operators representing the partial derivatives with respect to 
  -- the real part (x) and imaginary part (y) of the j-th coordinate.
  (partial_x : (Fin n) → ((Fin n → ℂ) → ℂ) → (Fin n → ℂ) → ℂ)
  (partial_y : (Fin n) → ((Fin n → ℂ) → ℂ) → (Fin n → ℂ) → ℂ)
  -- We define abstract operators representing the Wirtinger derivatives w.r.t z and z*.
  (partial_z : (Fin n) → ((Fin n → ℂ) → ℂ) → (Fin n → ℂ) → ℂ)
  (partial_z_conj : (Fin n) → ((Fin n → ℂ) → ℂ) → (Fin n → ℂ) → ℂ)
  -- The standard definitions of Wirtinger derivatives act as conditions/definitions for the problem.
  (h_def_z : ∀ j f z, partial_z j f z = (1 / 2 : ℂ) * (partial_x j f z - I * partial_y j f z))
  (h_def_z_conj : ∀ j f z, partial_z_conj j f z = (1 / 2 : ℂ) * (partial_x j f z + I * partial_y j f z)) :
  -- The conclusion requires proving the vector identities for ∂J/∂x and ∂J/∂y.
  (∀ z, (fun j => partial_x j J z) = (fun j => partial_z j J z + partial_z_conj j J z)) ∧
  (∀ z, (fun j => partial_y j J z) = (fun j => I * partial_z j J z - I * partial_z_conj j J z)) := by
  sorry





theorem theorem_360781_problem
  (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)
  (β : Fin 5 → ℝ)
  (h_nonneg : ∀ i, 0 ≤ β i)
  (h_sum : ∑ i : Fin 5, ((i : ℝ) + 1) * β i = 1)
  (h_bounds : β 3 ≤ 1/4 ∧ β 4 ≤ 1/5)
  (h_mono4 : ∀ x y z w v w', w < w' → f x y z w v < f x y z w' v)
  (h_mono5 : ∀ x y z w v v', v < v' → f x y z w v < f x y z w v')
  (h_beta5_pos : β 4 > 0) :
  let β' := ![β 0, β 1, β 2, β 3 + (5 * β 4) / 4, 0]
  (∀ i, 0 ≤ β' i) ∧
  (∑ i : Fin 5, ((i : ℝ) + 1) * β' i = 1) ∧
  (β' 3 ≤ 1/4 ∧ β' 4 ≤ 1/5) ∧
  f (β' 0) (β' 1) (β' 2) (β' 3) (β' 4) > f (β 0) (β 1) (β 2) (β 3) (β 4) := by
  sorry







theorem theorem_360989_problem (n : ℕ) (A P D : Matrix (Fin n) (Fin n) ℝ) (k : ℝ)
  (hP : IsUnit P)
  (hD : ∀ i j, i ≠ j → D i j = 0)
  (hA : A = P * D * P⁻¹)
  (h_inv : IsUnit (D + k • (1 : Matrix (Fin n) (Fin n) ℝ))) :
  (k • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹ = P * (D + k • 1)⁻¹ * P⁻¹ := by
  sorry























theorem theorem_362625_problem (n : ℕ) (a : ℝ) :
  let I : Matrix (Fin n) (Fin n) ℝ := 1
  let ones : Fin n → ℝ := fun _ => 1
  let A := (a - 1) • I + Matrix.vecMulVec ones ones
  A.det = (a - 1) ^ (n - 1) * (a + (n : ℝ) - 1) := by
  sorry

theorem theorem_361823_problem (n : ℕ) (A₁ A₂ : Set (Fin n → ℝ))
  (hA₁ : A₁ ⊆ {x | ∀ i, x i = 0 ∨ x i = 1})
  (hA₂ : A₂ ⊆ {x | ∀ i, x i = 0 ∨ x i = 1})
  (h_disj : Disjoint (convexHull ℝ A₁) (convexHull ℝ A₂)) :
  ∃ (g : (Fin n → ℝ) →L[ℝ] ℝ) (η : ℝ),
    (∀ x ∈ A₁, g x > η) ∧ (∀ x ∈ A₂, g x < η) := by
  sorry











theorem theorem_362228_problem (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℝ) :
  let B_n := Pi.basisFun ℝ (Fin n)
  let B_m := Pi.basisFun ℝ (Fin m)
  let f := Matrix.toLin B_n B_m M
  LinearMap.toMatrix B_m.dualBasis B_n.dualBasis (LinearMap.dualMap f) = M.transpose := by
  sorry





