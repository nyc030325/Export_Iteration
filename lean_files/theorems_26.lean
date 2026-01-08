import Mathlib
import Mathlib.Tactic



theorem theorem_136192_problem
  (E : Type*) [TopologicalSpace E] [CompactSpace E] [T2Space E]
  (A : NonUnitalSubalgebra ℝ C(E, ℝ))
  (h_sep : ∀ x y : E, x ≠ y → ∃ f ∈ A, f x ≠ f y)
  (h_nowhere_zero : ∀ x : E, ∃ f ∈ A, f x ≠ 0) :
  Dense (A : Set C(E, ℝ)) := by
  sorry

theorem theorem_136329_problem
  (F : Type*) [Field F]
  (n : ℕ)
  (A B : Matrix (Fin n) (Fin n) F)
  (h_comm : A * B = B * A) :
  ∃ (P : Matrix (Fin n) (Fin n) (AlgebraicClosure F)),
    IsUnit P ∧
    (∀ i j : Fin n, i > j → (P⁻¹ * (A.map (algebraMap F (AlgebraicClosure F))) * P) i j = 0) ∧
    (∀ i j : Fin n, i > j → (P⁻¹ * (B.map (algebraMap F (AlgebraicClosure F))) * P) i j = 0) := by
  sorry



theorem theorem_136686_problem
  {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (T : X →L[ℝ] Y)
  (h_inj : Function.Injective T)
  (h_dense : DenseRange T)
  (h_y_not_complete : ¬ CompleteSpace Y) :
  ¬ ∃ C > 0, ∀ x, ‖x‖ ≤ C * ‖T x‖ := by
  sorry







theorem theorem_136745_problem {F : Type*} [Field F] {n : ℕ}
  (A B : Matrix (Fin n) (Fin n) F) :
  Matrix.det (A * B) = Matrix.det A * Matrix.det B := by
  sorry

theorem theorem_136791_problem
  (V D : ℕ)
  (M : Matrix (Fin V) (Fin D) ℝ)
  (x : Fin V → ℝ)
  (i : Fin V)
  (h_xi : x i = 1)
  (h_xj : ∀ j, j ≠ i → x j = 0) :
  Matrix.vecMul x M = M i := by
  sorry









theorem theorem_136912_problem (T : ℝ) (hT : 0 < T) :
  Convex ℝ { p : ℝ × ℝ × ℝ × ℝ |
    let h := p.1
    let x := p.2.1
    let y := p.2.2.1
    let z := p.2.2.2
    h ≤ z ∧
    h ≤ T * x ∧
    h ≤ T * y ∧
    x ≤ 1 ∧
    y ≤ 1 ∧
    z ≤ T ∧
    h ≥ T * x + T * y + z - 2 * T ∧
    h ≥ 0 } := by
  sorry







theorem theorem_137387_problem (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
  (Matrix.det X) * (star (Matrix.det X)) = Matrix.det (X * X.conjTranspose) := by
  sorry













theorem theorem_138163_problem (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x₀ : EuclideanSpace ℝ (Fin n))
  (h₁ : Differentiable ℝ f)
  (h₂ : IsLocalMin f x₀) :
  gradient f x₀ = 0 := by
  sorry



theorem theorem_137862_problem 
  (N_P N_Z : ℕ) 
  (W : ℤ) 
  (h_arg_principle : W = (N_Z : ℤ) - (N_P : ℤ)) :
  (N_Z = 0) ↔ (W = -(N_P : ℤ)) := by
  sorry









theorem theorem_138047_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (v₁ v₂ v₃ : V) (c₁ c₂ c₃ : ℝ) :
  let u₁ := c₂ • v₃ - c₃ • v₂
  let u₂ := c₁ • v₂ - c₂ • v₁
  let u₃ := c₃ • v₁ - c₁ • v₃
  let M : Matrix (Fin 3) (Fin 3) ℝ := !![0, -c₂, c₃; -c₃, c₁, 0; c₂, 0, -c₁]
  ¬ LinearIndependent ℝ ![u₁, u₂, u₃] ↔ M.det = 0 := by
  sorry



theorem theorem_137889_problem :
  ∃ (n : ℕ) (A π π₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
    (π ∘L π = π) ∧ (π₁ ∘L π₁ = π₁) ∧ -- π and π₁ are projections
    (A ∘L π = π ∘L A) ∧ (A ∘L π₁ = π₁ ∘L A) ∧ -- π and π₁ are associated with A (commute)
    ‖π₁‖ > ‖π‖ := by
  sorry





theorem theorem_139094_problem 
  (image expectation imag1 z2 epsilon11 : ℝ)
  (beta12 lambda11 : ℝ)
  -- The structural model relates Expectation to potential causes. 
  -- We model it as a function of Image, z2, and potentially IMAG1 to test for direct influence.
  (structural_func : ℝ → ℝ → ℝ → ℝ)
  -- Condition: Expectation is defined as β12 * Image + z2. 
  -- This defines the functional form of the structural model (implicitly excluding imag1).
  (h_struct_def : ∀ (i z m : ℝ), structural_func i z m = beta12 * i + z)
  -- Condition: The value of Expectation is the result of this structural function.
  (h_expectation : expectation = structural_func image z2 imag1)
  -- Condition: The measurement model for IMAG1.
  (h_imag1 : imag1 = lambda11 * image + epsilon11) :
  -- Conclusion: IMAG1 cannot exert a direct causal influence on Expectation.
  -- Mathematically, the structural function is invariant to changes in the IMAG1 argument.
  ∀ (m : ℝ), structural_func image z2 m = expectation := by
  sorry





theorem theorem_138998_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
  (h : Matrix.rank (A * B - B * A) = 1) :
  (A * B - B * A) ^ 2 = 0 := by
  sorry













theorem theorem_139323_problem
  (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (deriv : H → H)
  (h_exist : ∃ f : H, f ≠ 0)
  (h_shift : ∀ (f : H) (K : ℝ), ∃ (g : H), ‖g‖ = ‖f‖ ∧ ‖deriv g‖ = ‖deriv f + (Complex.I * (K : ℂ)) • f‖) :
  ¬ ∃ C : ℝ, C > 0 ∧ ∀ (f : H) (K : ℝ), f ≠ 0 → K ≠ 0 → ‖deriv f + (K : ℂ) • f‖ ≤ C * ‖f‖ := by
  sorry

theorem theorem_139443_problem
  {X : Type*} [MetricSpace X]
  (K : Set X) (hK : IsCompact K)
  (f : K → ℝ → ℝ)
  (h_local : ∀ p : K, ∃ U : Set K, IsOpen U ∧ p ∈ U ∧
    ∃ L : ℝ, ∀ x ∈ U, ∀ y₁ y₂ : ℝ, |f x y₁ - f x y₂| ≤ L * |y₁ - y₂|) :
  ∃ L : ℝ, ∀ x : K, ∀ y₁ y₂ : ℝ, |f x y₁ - f x y₂| ≤ L * |y₁ - y₂| := by
  sorry





theorem theorem_139418_problem
  (x : Fin 4 → ℝ)
  (y : Fin 4 → ℝ)
  (h_distinct : Function.Injective x) :
  ∃! (coeffs : ℝ × ℝ × ℝ), ∀ (a' b' c' : ℝ),
    let ⟨a, b, c⟩ := coeffs
    (∑ i, (y i - (a * Real.exp (x i) + b * (Real.exp (x i)) ^ 2 + c * (Real.exp (x i)) ^ 3)) ^ 2) ≤
    (∑ i, (y i - (a' * Real.exp (x i) + b' * (Real.exp (x i)) ^ 2 + c' * (Real.exp (x i)) ^ 3)) ^ 2) := by
  sorry

theorem theorem_139508_problem
  (d : ℕ)
  (F : Type*) [Field F]
  (A : Matrix (Fin d) (Fin d) F)
  (hA : IsUnit A)
  (c : ℕ)
  (hc : 1 ≤ c ∧ c ≤ d) :
  ∃ (rows : Fin c → Fin d) (cols : Fin c → Fin d),
    Function.Injective rows ∧
    Function.Injective cols ∧
    (A.submatrix rows cols).rank = c := by
  sorry



theorem theorem_139785_problem (a₁ a₂ : ℝ)
  (h : ∀ x : ℝ, a₁ * (x^3 * |x|) + a₂ * x^4 = 0) :
  a₁ = 0 ∧ a₂ = 0 := by
  sorry



theorem theorem_139533_problem (a : ℝ) (h : 1 ≤ |a|) (z : ℂ)
  (hz : z = a + Complex.I * Real.sqrt (a ^ 2 - 1)) :
  Complex.abs z = Real.sqrt (2 * a ^ 2 - 1) := by
  sorry









theorem theorem_140002_problem
  (K : Type*) [Field K]
  (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (L : LieSubalgebra K (Module.End K V))
  (h : ∀ x : L, IsNilpotent (x : Module.End K V)) :
  LieAlgebra.IsNilpotent K L := by
  sorry







theorem theorem_140298_problem
  (n : ℕ) (hn : n > 0)
  (G : Type*) [Group G]
  (ρ : G →* Matrix.GeneralLinearGroup (Fin n) ℂ) :
  ∃ F : (Fin n → ℂ) → ℂ, ∀ g : G,
    Matrix.det (ρ g : Matrix (Fin n) (Fin n) ℂ) =
    F (fun k => Matrix.trace (ρ (g ^ (k.val + 1)) : Matrix (Fin n) (Fin n) ℂ)) := by
  sorry





theorem theorem_140060_problem
  (n : ℕ) (hn : 0 < n)
  (y : Fin n → ℝ) (hy : ∀ i, y i < 0)
  (h : (∏ i, -y i) ^ (1 / (n : ℝ)) < 1 / (n : ℝ)) :
  Filter.Tendsto (λ t ↦ (∑ i, (-t / y i) * y i) - (- (∏ i, -t / y i) ^ (1 / (n : ℝ)))) Filter.atTop Filter.atTop := by
  sorry



theorem theorem_140703_problem (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ)
  (h_symm : H.IsSymm)
  (h_idem : H * H = H) :
  ∀ i : Fin n, H i i = ∑ j : Fin n, (H i j) ^ 2 := by
  sorry

theorem theorem_140616_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ) (p x : E)
  (g : ℝ → E) (h : ℝ → ℝ)
  (hf : Differentiable ℝ f)
  (hg : ∀ t, g t = p + t • (x - p))
  (hh : ∀ t, h t = f (g t)) :
  ∀ t, deriv h t = inner (gradient f (g t)) (x - p) := by
  sorry



theorem theorem_140734_problem
  (n m : ℝ → EuclideanSpace ℝ (Fin 3))
  (p : ℝ)
  (hn : DifferentiableAt ℝ n p)
  (hm : DifferentiableAt ℝ m p) :
  deriv (fun x => crossProduct (n x) (m x)) p =
  crossProduct (deriv n p) (m p) + crossProduct (n p) (deriv m p) := by
  sorry







theorem theorem_141082_problem
  (r : ℝ)
  (T : ContinuousMap (Set.Icc (-r) r) ℝ →ₗ[ℝ] ContinuousMap (Set.Icc (-r) r) ℝ)
  (C : ℝ) (hC : C > 1)
  (f : ContinuousMap (Set.Icc (-r) r) ℝ) (hf : f ≠ 0)
  (hTf : ‖T f‖ = C * ‖f‖) :
  ¬ ∃ k, 0 ≤ k ∧ k < 1 ∧
    ∀ g h : ContinuousMap (Set.Icc (-r) r) ℝ, ‖T g - T h‖ ≤ k * ‖g - h‖ := by
  sorry





theorem theorem_141406_problem {K : Type*} [Field K] {n : ℕ}
  (A : Matrix (Fin n) (Fin n) K) (M : K)
  (h : (A - M • (1 : Matrix (Fin n) (Fin n) K)).rank < n) :
  Module.End.HasEigenvalue (Matrix.toLin' A) M := by
  sorry

theorem theorem_141291_problem
  {R : Type*} [CommRing R]
  (n : ℕ)
  (A : Matrix (Fin n) (Fin n) R)
  (c : R) :
  Matrix.det (c • A) = c ^ n * Matrix.det A := by
  sorry





theorem theorem_141622_problem (m n : ℕ) 
  (M : Matrix (Fin m) (Fin n) ℝ) (a b : Fin n → ℝ) :
  (Matrix.mulVec M a) * (Matrix.mulVec M b) = 
  Matrix.mulVec (fun i (p : Fin n × Fin n) => M i p.1 * M i p.2) (fun p => a p.1 * b p.2) := by
  sorry





theorem theorem_141497_problem
  {F V W U : Type*} [Field F]
  [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
  [AddCommGroup U] [Module F U]
  (n m p : ℕ)
  (bV : Basis (Fin n) F V)
  (bW : Basis (Fin m) F W)
  (bU : Basis (Fin p) F U)
  (T : V →ₗ[F] W)
  (S : W →ₗ[F] U) :
  LinearMap.toMatrix bV bU (S.comp T) = (LinearMap.toMatrix bW bU S) * (LinearMap.toMatrix bV bW T) := by
  sorry

theorem theorem_141482_problem
  (m n : ℕ)
  (hn : n > 0)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (B1 : Matrix (Fin m) (Fin n) ℝ)
  (C1 : Matrix (Fin n) (Fin n) ℝ)
  (h_decomp : A = B1 * C1) :
  ∃ (B2 : Matrix (Fin m) (Fin n) ℝ) (C2 : Matrix (Fin n) (Fin n) ℝ),
    A = B2 * C2 ∧ C2.det = -C1.det := by
  sorry





theorem theorem_141703_problem (p : ℕ) [Fact p.Prime] :
  let F := RatFunc (ZMod p)
  let x : F := RatFunc.X
  let K := Subfield.closure {x ^ p}
  ∀ a : F, Algebra.trace K F a = 0 := by
  sorry



theorem theorem_141508_problem (G : Type*) [Group G] [Fintype G] :
  ∃ Φ : MonoidAlgebra ℤ G →+* Matrix (Fin (Fintype.card G)) (Fin (Fintype.card G)) ℤ,
  Function.Injective Φ := by
  sorry



theorem theorem_142285_problem (n m : ℕ) (v : Fin n → (Fin m → ℂ)) :
  (Submodule.span ℂ {x | ∃ i j : Fin n, i < j ∧ x = v i - v j} : Set (Fin m → ℂ)) =
  {x | ∃ c : Fin n → ℂ, ∑ i, c i = 0 ∧ x = ∑ i, c i • v i} := by
  sorry



theorem theorem_142009_problem (v₁ v₂ w₁ w₂ : ℝ)
  (h_w1 : w₁ ∈ Submodule.span ℚ ({v₁, v₂} : Set ℝ))
  (h_w2 : w₂ ∈ Submodule.span ℚ ({v₁, v₂} : Set ℝ))
  (h_v_indep : LinearIndependent ℚ ![v₁, v₂])
  (h_trans : ¬ IsAlgebraic ℚ v₁ ∨ ¬ IsAlgebraic ℚ v₂) :
  LinearIndependent ℚ ![w₁, w₂] := by
  sorry





