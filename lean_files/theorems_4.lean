import Mathlib
import Mathlib.Tactic

theorem theorem_15572_problem
  (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (b c x y : Fin n → ℝ)
  (d : ℝ)
  (h_denom : Matrix.dotProduct c x + d ≠ 0)
  (hy : y = (Matrix.dotProduct c x + d)⁻¹ • (Matrix.mulVec A x + b))
  (h_inv : IsUnit (A - Matrix.vecMulVec y c)) :
  x = Matrix.mulVec (A - Matrix.vecMulVec y c)⁻¹ (d • y - b) := by
  sorry









theorem theorem_15649_problem (n : ℕ) (D : Set (Fin n → ℝ)) (a x : Fin n → ℝ)
  (hD : Convex ℝ D) (ha : a ∈ D) (hx : x ∈ D) :
  ∀ t ∈ Set.Icc (0 : ℝ) 1, a + t • (x - a) ∈ D := by
  sorry

theorem theorem_15841_problem (a b : ℝ) :
  Complex.tan (Complex.mk a b) =
  Complex.mk
    (Real.sin (2 * a) / (Real.cos (2 * a) + Real.cosh (2 * b)))
    (Real.sinh (2 * b) / (Real.cos (2 * a) + Real.cosh (2 * b))) := by
  sorry









theorem theorem_16305_problem
  (n : ℕ)
  (φ : EuclideanSpace ℝ (Fin n) × ℝ → ℝ)
  (v : ℝ → EuclideanSpace ℝ (Fin n))
  (hφ : ContDiff ℝ ⊤ φ)
  (hv : ContDiff ℝ 2 v)
  (θ : EuclideanSpace ℝ (Fin n) × ℝ → ℝ)
  (hθ : ∀ x t, θ (x, t) = φ (x, t) + inner x (deriv (deriv v) t)) :
  ∀ x t, gradient (fun y ↦ θ (y, t)) x = gradient (fun y ↦ φ (y, t)) x + deriv (deriv v) t := by
  sorry

theorem theorem_16470_problem
  {m n F : Type*}
  [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]
  [LinearOrderedField F]
  (A : Matrix m n F) :
  LinearMap.ker (Matrix.toLin' A) = LinearMap.ker (Matrix.toLin' (A.transpose * A)) := by
  sorry

theorem theorem_17092_problem 
  {k l m : Type*} [Fintype k] [Fintype l] [Fintype m]
  [DecidableEq k] [DecidableEq l] [DecidableEq m]
  {R : Type*} [CommRing R]
  (D : Matrix m k R)
  (X : Matrix m l R)
  (Y : Matrix k l R)
  (h : ∀ x : Matrix k Unit R, Y.transpose * x = X.transpose * D * x) :
  Y = D.transpose * X := by
  sorry

theorem theorem_16944_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (h_inv : A.det ≠ 0)
  (h_cond : (A⁻¹).det = (-A).det) :
  Even n := by
  sorry

theorem theorem_16713_problem
  (G : Type*) [Group G] [Infinite G]
  (K : Type*) [Field K]
  (α : Cardinal) (h : Cardinal.mk G ≤ α) :
  ∃ ρ : Representation K G (α.out →₀ K),
    ∀ W : Submodule K (α.out →₀ K),
      (∀ (g : G) (w : W), ρ g w ∈ W) →
      FiniteDimensional K W →
      W = ⊥ := by
  sorry

theorem theorem_16844_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (v : H) (hv : v ≠ 0) :
  ∃ T_v : (H →L[ℂ] H) →L[ℂ] ℂ, ∀ A : H →L[ℂ] H, T_v A = inner (A v) v := by
  sorry

theorem theorem_16499_problem {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (S L : Set V) (n m : ℕ)
  (hS_fin : S.Finite) (hL_fin : L.Finite)
  (hn : S.ncard = n) (hm : L.ncard = m)
  (h_span : Submodule.span F S = ⊤)
  (h_indep : LinearIndependent F ((↑) : L → V))
  (h_le : m ≤ n) :
  ∃ T, T ⊆ S ∧ T.ncard = m ∧ Submodule.span F ((S \ T) ∪ L) = ⊤ := by
  sorry









theorem theorem_17259_problem (n : ℕ) (hn : n > 0) :
  ¬ Continuous (fun (A : Matrix (Fin n) (Fin n) ℝ) => A.rank) := by
  sorry







theorem theorem_16884_problem
  {V : Type*}
  [AddCommGroup V] [Module ℝ V]
  (L : V →ₗ[ℝ] V)
  (conv : V → V → V)
  (H_k F p : V)
  -- Condition: F is the sum of the series, implying the fixed point property F = K + K * F where K = L H_k
  (hF : F = L H_k + conv (L H_k) F)
  -- Condition: Definition of p
  (hp : p = H_k + conv H_k F)
  -- Condition: The assumptions on estimates and differentiation under summation validate this identity
  (h_assumptions : L (conv H_k F) = conv (L H_k) F - F) :
  L p = 0 := by
  sorry





theorem theorem_16716_problem (n : ℕ) (X Y Z : Fin n → ℝ)
  (h1 : Matrix.dotProduct Z Z ≠ 0)
  (h2 : Matrix.dotProduct Z X ≠ 0) :
  ((Matrix.dotProduct Z Z)⁻¹ * Matrix.dotProduct Z Y) /
  ((Matrix.dotProduct Z Z)⁻¹ * Matrix.dotProduct Z X) =
  (Matrix.dotProduct Z X)⁻¹ * Matrix.dotProduct Z Y := by
  sorry







theorem theorem_16419_problem
  {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (J : V →L[ℝ] W)
  (A : ℕ → V →L[ℝ] W) -- Represents the approximation operators J_n ∘ P_n
  (C α : ℝ)
  (hC : 0 < C)
  (hα : 0 < α)
  (h_approx : ∀ (n : ℕ) (u : V), 0 < n → ‖J u - A n u‖ ≤ C * ‖u‖ * (n : ℝ) ^ (-α)) :
  ∀ (n : ℕ), 0 < n → ‖J - A n‖ ≤ C * (n : ℝ) ^ (-α) := by
  sorry

theorem theorem_16878_problem
  (n : ℕ)
  (y s y' s' : Fin n → ℝ)
  (B : Matrix (Fin n) (Fin n) ℝ)
  (η θ : ℝ)
  (hy : y ≠ 0)
  (hs : s ≠ 0)
  (h_dot : Matrix.dotProduct y s ≠ 0)
  (h_eta : η ≠ 0)
  (h_theta : θ ≠ 0)
  (hy' : y' = η • y)
  (hs' : s' = θ • s) :
  ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 / Matrix.dotProduct y' s') • Matrix.vecMulVec y' s') * B =
  ((1 : Matrix (Fin n) (Fin n) ℝ) - (1 / Matrix.dotProduct y s) • Matrix.vecMulVec y s) * B := by
  sorry

theorem theorem_17723_problem
  {K V W : Type*}
  [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  (m n : ℕ)
  (hm : FiniteDimensional.finrank K W = m)
  (hn : FiniteDimensional.finrank K V = n)
  (f : V →ₗ[K] W)
  (bV : Basis (Fin n) K V)
  (bW : Basis (Fin m) K W)
  (A : Matrix (Fin m) (Fin n) K)
  (hA : A = LinearMap.toMatrix bV bW f)
  (h_minor : ∃ (cols : Fin m → Fin n), Function.Injective cols ∧
    Matrix.det (Matrix.submatrix A id cols) ≠ 0) :
  FiniteDimensional.finrank K (LinearMap.range f) = m := by
  sorry

theorem theorem_17469_problem (A : Matrix (Fin 3) (Fin 3) ℝ)
  (h_orth : A.transpose * A = 1)
  (h_skew : A.transpose = -A) :
  False := by
  sorry

theorem theorem_17403_problem {I V : Type*} (v w : I → V)
  (h : ∀ i, v i = w i) :
  ∀ j, v j = w j := by
  sorry





theorem theorem_18567_problem
  (n : ℕ)
  {F : Type*} [Field F]
  (S T : Matrix (Fin n) (Fin n) F)
  (v₁ : Fin n → F)
  (h1 : ∃ c : F, S = T + c • (1 : Matrix (Fin n) (Fin n) F))
  (h2 : S * T = T * S)
  (h3 : Matrix.mulVec T v₁ = 0) :
  Matrix.mulVec (S * T) v₁ = 0 := by
  sorry

theorem theorem_17513_problem (n : ℕ) (a x : EuclideanSpace ℝ (Fin n)) (h : a ≠ 0) :
  (orthogonalProjection (Submodule.span ℝ {a}) x : EuclideanSpace ℝ (Fin n)) = 
  (inner a x / ‖a‖ ^ 2) • a := by
  sorry









theorem theorem_18467_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (h : ∀ i j : Fin n, A * Matrix.stdBasisMatrix i j 1 = Matrix.stdBasisMatrix i j 1 * A) :
  ∃ c : ℝ, A = c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  sorry

theorem theorem_18145_problem
  (R : Type*) [CommRing R]
  (m : Ideal R) [m.IsMaximal]
  (A : Type*) [AddCommGroup A] [Module R A]
  (n : ℕ)
  (gen : Fin n → A)
  (h_gen : Submodule.span R (Set.range gen) = ⊤)
  (h_min : ∀ i : Fin n, Submodule.span R (Set.range gen \ {gen i}) < ⊤) :
  let k := R ⧸ m
  let L₀ := Fin n → R
  let φ : L₀ →ₗ[R] A := (Pi.basisFun R (Fin n)).constr R gen
  let φ_k := φ.baseChange k
  Function.Bijective φ_k := by
  sorry









theorem theorem_18105_problem
  -- Dimensions
  (n1 p1 n2 p2 : ℕ)
  -- Design Matrices (Fixed constants)
  (X1 : Matrix (Fin n1) (Fin p1) ℝ)
  (X2 : Matrix (Fin n2) (Fin p2) ℝ)
  -- Coefficient Vectors (Fixed constants)
  (beta1 : Matrix (Fin p1) (Fin 1) ℝ)
  (beta2 : Matrix (Fin p2) (Fin 1) ℝ)
  -- Condition 1: Rows independent implies invertibility of Gram matrix
  (h_inv1 : Invertible (X1.transpose * X1))
  (h_inv2 : Invertible (X2.transpose * X2))
  -- Probability Space context
  (Ω : Type*)
  -- Random Error Vectors
  (u1 : Ω → Matrix (Fin n1) (Fin 1) ℝ)
  (u2 : Ω → Matrix (Fin n2) (Fin 1) ℝ)
  -- Expectation Operator abstract definition
  (E : {m n : ℕ} → (Ω → Matrix (Fin m) (Fin n) ℝ) → Matrix (Fin m) (Fin n) ℝ)
  -- Linearity of Expectation properties
  (hE_add : ∀ {m n : ℕ} (A B : Ω → Matrix (Fin m) (Fin n) ℝ), E (fun ω ↦ A ω + B ω) = E A + E B)
  (hE_mul_const : ∀ {m n k l : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (Z : Ω → Matrix (Fin k) (Fin l) ℝ) (B : Matrix (Fin l) (Fin n) ℝ),
    E (fun ω ↦ A * Z ω * B) = A * E Z * B)
  (hE_const : ∀ {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℝ), E (fun _ ↦ C) = C)
  -- Condition 2: Zero mean errors
  (hu1_mean : E u1 = 0)
  (hu2_mean : E u2 = 0)
  -- Condition 2: Pairwise independent errors (Zero cross-covariance)
  (hu_cov : E (fun ω ↦ u1 ω * (u2 ω).transpose) = 0)
  -- Model Definitions
  (Y1 : Ω → Matrix (Fin n1) (Fin 1) ℝ)
  (hY1 : Y1 = fun ω ↦ X1 * beta1 + u1 ω)
  (Y2 : Ω → Matrix (Fin n2) (Fin 1) ℝ)
  (hY2 : Y2 = fun ω ↦ X2 * beta2 + u2 ω)
  -- OLS Estimator Definitions
  (beta1_ols : Ω → Matrix (Fin p1) (Fin 1) ℝ)
  (h_beta1_ols : beta1_ols = fun ω ↦ (⅟(X1.transpose * X1)) * X1.transpose * Y1 ω)
  (beta2_ols : Ω → Matrix (Fin p2) (Fin 1) ℝ)
  (h_beta2_ols : beta2_ols = fun ω ↦ (⅟(X2.transpose * X2)) * X2.transpose * Y2 ω)
  -- Covariance Definition
  (Cov : {m n : ℕ} → (Ω → Matrix (Fin m) (Fin 1) ℝ) → (Ω → Matrix (Fin n) (Fin 1) ℝ) → Matrix (Fin m) (Fin n) ℝ)
  (hCov_def : ∀ {m n : ℕ} (Z1 : Ω → Matrix (Fin m) (Fin 1) ℝ) (Z2 : Ω → Matrix (Fin n) (Fin 1) ℝ),
    Cov Z1 Z2 = E (fun ω ↦ (Z1 ω - E Z1) * (Z2 ω - E Z2).transpose)) :
  -- Conclusion
  Cov beta1_ols beta2_ols = 0 := by
  sorry

theorem theorem_17583_problem (n q : ℕ)
  (Z : Matrix (Fin n) (Fin q) ℝ)
  (Psi : Matrix (Fin q) (Fin q) ℝ)
  (V : Matrix (Fin n) (Fin n) ℝ)
  (h_denom : (Z * Psi * Z.transpose).trace + V.trace ≠ 0) :
  let total_variance := Z * Psi * Z.transpose + V
  (Z * Psi * Z.transpose).trace / total_variance.trace =
  (Z * Psi * Z.transpose).trace / ((Z * Psi * Z.transpose).trace + V.trace) := by
  sorry



theorem theorem_17803_problem
  {K U V W : Type*} [Field K]
  [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  (f : U →ₗ[K] V) (g : V →ₗ[K] W) :
  (g.comp f).dualMap = f.dualMap.comp g.dualMap := by
  sorry







theorem theorem_19019_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (T : V →ₗ[ℝ] V)
  (U : Submodule ℝ V)
  (h_inv : ∀ x ∈ U, T x ∈ U) :
  ∀ μ : ℝ, Module.End.HasEigenvalue (T.restrict h_inv) μ → Module.End.HasEigenvalue T μ := by
  sorry

theorem theorem_19195_problem (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
  (n : ℕ) (e : Basis (Fin (n + 1)) K V) :
  ∃ Z : Basis (Fin (n + 1)) K (Module.Dual K V),
    ∀ (i j : Fin (n + 1)), Z i (e j) = if i = j then 1 else 0 := by
  sorry





theorem theorem_19496_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (n : ℕ)
  (Φ : Fin n → V)
  (α : Fin n → ℝ)
  (h : ∀ i, ‖Φ i‖ = 1) :
  ‖∑ i, α i • Φ i‖^2 ≥ (∑ i, (α i)^2) - ∑ i, ∑ j, if i ≠ j then |α i * α j * inner (Φ i) (Φ j)| else 0 := by
  sorry







theorem theorem_19841_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [Field R]
  (A : Matrix n n R)
  (h : A ^ 2 = 0) :
  (1 - A)⁻¹ = 1 + A := by
  sorry

theorem theorem_20074_problem
  (n : ℕ) (hn : n > 0)
  (constraints : (Fin n → ℝ) → Prop) :
  sSup { w : ℝ | ∃ x : Fin n → ℝ, constraints x ∧ w = sInf (Set.range x) } =
  sSup { z : ℝ | ∃ x : Fin n → ℝ, constraints x ∧ ∀ i, z ≤ x i } := by
  sorry



theorem theorem_19161_problem
  {K : Type*} [Field K] [TopologicalSpace K]
  {X : Type*} [AddCommGroup X] [Module K X] [TopologicalSpace X]
  (h_cont : Continuous (fun (p : K × X) => p.1 • p.2))
  (C : Set K) (A : Set X)
  (h_compact : IsCompact (C ×ˢ A)) :
  IsCompact ((fun (p : K × X) => p.1 • p.2) '' (C ×ˢ A)) := by
  sorry



theorem theorem_19840_problem (n m : ℕ) (α : ℕ → ℕ → ℝ)
  (hn : n ≥ 3) (hm : m ≥ 3)
  (h_dof : (n * m : ℤ) - 2 * ((n : ℤ) - 2) * ((m : ℤ) - 2) < 0)
  (h_eq1 : ∀ i j, 0 < i → i < n - 1 → 0 < j → j < m - 1 →
    α i j = (α (i + 1) j + α (i - 1) j + α i (j + 1) + α i (j - 1)) / 4)
  (h_eq2 : ∀ i j, 0 < i → i < n - 1 → 0 < j → j < m - 1 →
    α i j = (α (i + 1) (j + 1) + α (i - 1) (j + 1) + α (i + 1) (j - 1) + α (i - 1) (j - 1)) / 4)
  (h_boundary : ∃ k, ∀ i j, i < n → j < m → (i = 0 ∨ i = n - 1 ∨ j = 0 ∨ j = m - 1) → α i j = k) :
  ∃ k, ∀ i j, i < n → j < m → α i j = k := by
  sorry

theorem theorem_19359_problem
  {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
  {n : ℕ}
  (bV : Basis (Fin n) F V)
  (bW : Basis (Fin n) F W)
  (T : V →ₗ[F] W)
  (A : Matrix (Fin n) (Fin n) F)
  (hA : A = LinearMap.toMatrix bV bW T) :
  T = ∑ i : Fin n, ∑ j : Fin n, (A i j) • (LinearMap.smulRight (bV.coord j) (bW i)) := by
  sorry

theorem theorem_19869_problem :
  ∃ (U V W : Fin 7 → Matrix (Fin 2) (Fin 2) ℤ),
    ∀ (R : Type) [Ring R] (A B : Matrix (Fin 2) (Fin 2) R),
      A * B = ∑ i : Fin 7,
        (((∑ m : Fin 2, ∑ n : Fin 2, (U i m n : R) * A m n) *
          (∑ m : Fin 2, ∑ n : Fin 2, (V i m n : R) * B m n)) •
            ((W i).map (Int.castRingHom R))) := by
  sorry











theorem theorem_20577_problem (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (i : Matrix (Fin 1) (Fin N) ℝ) :
  Fintype.card (Fin N × Fin 1) = N ∧ Fintype.card (Fin N × Fin N) = N ^ 2 := by
  sorry

theorem theorem_20406_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] :
  let N : X × X → ℝ := fun x ↦ ‖x.1‖ + ‖x.2‖
  (∀ x, 0 ≤ N x) ∧
  (∀ x, N x = 0 ↔ x = 0) ∧
  (∀ (c : 𝕜) x, N (c • x) = ‖c‖ * N x) ∧
  (∀ x y, N (x + y) ≤ N x + N y) ∧
  (∀ f : ℕ → X × X, 
    (∀ ε > 0, ∃ K, ∀ m n, K ≤ m → K ≤ n → N (f m - f n) < ε) → 
    ∃ x, ∀ ε > 0, ∃ K, ∀ n, K ≤ n → N (f n - x) < ε) := by
  sorry





theorem theorem_20161_problem (d m : ℕ)
  (Φ : (Fin d → ℝ) → (Fin m → ℝ))
  (θ : Fin m → ℝ)
  (p_pos : (Fin d → ℝ) → ℝ)
  (p_neg : (Fin d → ℝ) → ℝ)
  (h_pos : ∀ x, p_pos x = 1 / (1 + Real.exp (- (Matrix.dotProduct θ (Φ x)))))
  (h_neg : ∀ x, p_neg x = 1 / (1 + Real.exp (Matrix.dotProduct θ (Φ x)))) :
  {x | p_pos x = p_neg x} = {x | Matrix.dotProduct θ (Φ x) = 0} := by
  sorry















theorem theorem_20830_problem
  (n : ℕ)
  (K : Type*) [Field K]
  (V : Type*) [AddCommGroup V] [Module K V]
  (x : Fin n → V)
  (σ τ : Equiv.Perm (Fin n))
  (act : PiTensorProduct K (fun _ : Fin n => V) → Equiv.Perm (Fin n) → PiTensorProduct K (fun _ : Fin n => V))
  (h_act : ∀ (v : Fin n → V) (π : Equiv.Perm (Fin n)),
    act (PiTensorProduct.tprod K v) π = PiTensorProduct.tprod K (v ∘ π)) :
  act (act (PiTensorProduct.tprod K x) σ) τ = PiTensorProduct.tprod K (x ∘ σ ∘ τ) := by
  sorry

theorem theorem_21040_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
  (h : Filter.Tendsto (fun k ↦ A ^ k) Filter.atTop (nhds 1)) :
  A = 1 := by
  sorry

theorem theorem_21268_problem (n : ℕ) (hn : 2 ≤ n) :
  ¬ ∃ (f : ℝ → ℝ → ℝ), ∀ (A B : Matrix (Fin n) (Fin n) ℝ),
  Matrix.det (A + B) ≤ f (Matrix.det A) (Matrix.det B) := by
  sorry





theorem theorem_21468_problem (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
  (h_symm : K.IsSymm) (h_posdef : K.PosDef) :
  ∃! X : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j : Fin n, j < i → X i j = 0) ∧
    (∀ i : Fin n, 0 < X i i) ∧
    K = X.transpose * X := by
  sorry

theorem theorem_21426_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
  (h_rank : A.rank = n) :
  ∃! QR : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ,
    let Q := QR.1
    let R := QR.2
    A = Q * R ∧
    Q.transpose * Q = 1 ∧
    (∀ i j, j < i → R i j = 0) ∧
    (∀ i, 0 < R i i) := by
  sorry



