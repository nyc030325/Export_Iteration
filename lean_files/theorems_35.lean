import Mathlib
import Mathlib.Tactic

theorem theorem_186288_problem {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (j : Fin (n + 1)) :
  (A.updateRow 0 (Pi.single j 1)).det = (-1 : ℂ) ^ (j : ℕ) * (A.submatrix Fin.succ j.succAbove).det := by
  sorry



theorem theorem_186396_problem (n k : ℕ) (v : Fin k → (Fin n → ℝ))
  (h : LinearIndependent ℤ v) :
  LinearIndependent ℚ v := by
  sorry



theorem theorem_186737_problem
  (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (bracket : V → V → V)
  (Y : V → ℝ)
  (X : V)
  (h_cond : Y X = 0 ↔ ∀ Z : V, bracket X Z = 0)
  (h_exist : ∃ Z : V, bracket X Z ≠ 0) :
  Y X ≠ 0 := by
  sorry

theorem theorem_186404_problem
  (n : ℕ)
  (K M : ℝ)
  (hK : 0 < K)
  (hM : 0 < M)
  (hKM : K < M)
  (f : ℂ → ℂ)
  (hf : ∀ z, f z = (K : ℂ) * z ^ n)
  (z : ℂ)
  (hz : z ≠ 0) :
  Complex.abs (f z) < M * (Complex.abs z) ^ n := by
  sorry







theorem theorem_186631_problem :
  ∃ (X Y : Type)
    (_ : NormedAddCommGroup X) (_ : NormedSpace ℝ X)
    (_ : NormedAddCommGroup Y) (_ : NormedSpace ℝ Y)
    (T : X →L[ℝ] Y) (invT : Y →L[ℝ] X),
    T.comp invT = ContinuousLinearMap.id ℝ Y ∧
    invT.comp T = ContinuousLinearMap.id ℝ X ∧
    ¬ (∀ x, ‖T x‖ = ‖x‖) := by
  sorry



theorem theorem_186972_problem
  (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (R : Set (Module.Dual ℝ V))
  (hR_fin : R.Finite)
  (hR_sep : ∀ v : V, v ≠ 0 → ∃ f ∈ R, f v ≠ 0)
  (hR_sym : ∀ f ∈ R, -f ∈ R)
  (K : Set V)
  (hK_cham : ∃ x ∈ {v | ∀ f ∈ R, f v ≠ 0}, K = connectedComponentIn {v | ∀ f ∈ R, f v ≠ 0} x)
  (hK_simp : ∃ (b : Basis (Fin (FiniteDimensional.finrank ℝ V)) ℝ V),
    K = {v | ∃ c : Fin (FiniteDimensional.finrank ℝ V) → ℝ, (∀ i, 0 < c i) ∧ v = ∑ i, c i • b i}) :
  ∃ (b : Basis (Fin (FiniteDimensional.finrank ℝ V)) ℝ V),
    (K = {v | ∃ c : Fin (FiniteDimensional.finrank ℝ V) → ℝ, (∀ i, 0 < c i) ∧ v = ∑ i, c i • b i}) ∧
    (∀ i, b.dualBasis i ∈ R ∨ - b.dualBasis i ∈ R) := by
  sorry









theorem theorem_187216_problem
  {𝕜 : Type*} [RCLike 𝕜]
  (a : ℕ → ℕ → 𝕜)
  (h_sum : Summable (fun (p : ℕ × ℕ) ↦ ‖a p.1 p.2‖ ^ 2))
  (T : lp (fun (_ : ℕ) ↦ 𝕜) 2 →L[𝕜] lp (fun (_ : ℕ) ↦ 𝕜) 2)
  (hT : ∀ (x : lp (fun (_ : ℕ) ↦ 𝕜) 2) (i : ℕ), T x i = ∑' j, a i j * x j) :
  IsCompactOperator T := by
  sorry

theorem theorem_187280_problem
  (n : ℕ)
  (hn : 2 ≤ n)
  (p : Fin n → EuclideanSpace ℝ (Fin n))
  (hp_distinct : Function.Injective p)
  (a b c : EuclideanSpace ℝ (Fin n))
  (h_eq : ∀ i : Fin n, ‖a - p i‖ = ‖b - p i‖ ∧ ‖b - p i‖ = ‖c - p i‖) :
  Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin n))) := by
  sorry

theorem theorem_187372_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  {W : Type*} [AddCommGroup W] [Module F W]
  (U : Submodule F V)
  (f : U →ₗ[F] W) :
  ∃ g : V →ₗ[F] W, ∀ x : U, g x = f x := by
  sorry

theorem theorem_187456_problem
  (n : ℕ)
  (A₁ A₂ : Matrix (Fin n) (Fin n) ℚ)
  (P : Matrix (Fin n) (Fin n) ℚ)
  (hP : ∃ σ : Equiv.Perm (Fin n), P = Matrix.of (fun i j ↦ if j = σ i then 1 else 0))
  (h_eq : P⁻¹ * A₂ * P = A₁) :
  let G₁ := SimpleGraph.fromRel (fun i j ↦ A₁ i j = 1)
  let G₂ := SimpleGraph.fromRel (fun i j ↦ A₂ i j = 1)
  Nonempty (G₁ ≃g G₂) := by
  sorry

theorem theorem_187452_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
  ∃ (P : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
    IsUnit P ∧
    (∀ i j : Fin n, i > j → U i j = 0) ∧
    P⁻¹ * A * P = U := by
  sorry









theorem theorem_187675_problem (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (h1 : ∀ x y a b, dist x y = dist a b → dist (f x) (f y) = dist (f a) (f b))
  (h2 : ∀ x y a b, dist x y < dist a b → dist (f x) (f y) < dist (f a) (f b))
  (h_cont : Continuous f) :
  ∃ (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)), ∀ x, f x = L x + v := by
  sorry



theorem theorem_188695_problem
  (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (h : A.PosDef) :
  A⁻¹.PosDef := by
  sorry



theorem theorem_188368_problem
  {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  (S₁ S₂ : Submodule 𝕜 V)
  -- S₁ ⊕ S₂ = V (S₁ and S₂ are orthogonal complements, and V = S₁ + S₂ with S₁ ∩ S₂ = {0})
  (h_direct : IsCompl S₁ S₂)
  (h_ortho : S₁ ⟂ S₂)
  -- {u_1, ..., u_m} is an orthonormal basis for S₁
  (m : ℕ) (u : OrthonormalBasis (Fin m) 𝕜 S₁)
  -- {v_1, ..., v_n} is an orthonormal basis for S₂
  (n : ℕ) (v : OrthonormalBasis (Fin n) 𝕜 S₂) :
  -- {u_1, ..., u_m, v_1, ..., v_n} is an orthonormal basis for V
  let union_basis := Sum.elim (fun i => (u i : V)) (fun j => (v j : V))
  Orthonormal 𝕜 union_basis ∧ Submodule.span 𝕜 (Set.range union_basis) = ⊤ := by
  sorry

theorem theorem_188513_problem (m : ℕ)
  (M : Matrix (Fin m) (Fin (m + 2)) ℝ)
  (hM : ∀ (i : Fin m) (j : Fin (m + 2)), M i j =
    if (j : ℕ) = (i : ℕ) + 1 then 1
    else if (j : ℕ) = (i : ℕ) then -((i : ℝ) + 1) / m
    else if (j : ℕ) = (i : ℕ) + 2 then -((m : ℝ) - ((i : ℝ) + 1)) / m
    else 0)
  (v : Fin m → ℝ)
  (X : Fin (m + 2) → ℝ)
  (hX : Matrix.mulVec M X = v)
  (Minv : Matrix (Fin (m + 2)) (Fin m) ℝ)
  (h_inv_left : M * Minv = 1)
  (h_inv_right : Minv * M = 1) :
  X = Matrix.mulVec Minv v := by
  sorry

theorem theorem_188702_problem
  {𝕜 X : Type*}
  [Field 𝕜] [TopologicalSpace 𝕜]
  [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
  (f : X →L[𝕜] 𝕜) :
  ∀ U ∈ nhds (0 : 𝕜), ∃ W ∈ nhds (0 : X), f '' W ⊆ U := by
  sorry





theorem theorem_188816_problem (n : ℕ)
  (P : Matrix (Fin 4) (Fin 4) ℚ)
  (hP : P = !![7/9, 1/9, 1/9, 0; 0, 8/9, 0, 1/9; 0, 0, 8/9, 1/9; 0, 0, 0, 1])
  (e_1 : Matrix (Fin 4) (Fin 1) ℚ)
  (he_1 : e_1 = !![1; 0; 0; 0])
  (e_4 : Matrix (Fin 4) (Fin 1) ℚ)
  (he_4 : e_4 = !![0; 0; 0; 1]) :
  (P ^ n) 0 3 = (e_1.transpose * (P ^ n) * e_4) 0 0 := by
  sorry





theorem theorem_188935_problem (n : ℕ) (x : Fin n → ℝ) (p : ℝ)
  (hx : ∀ i, x i ≠ 0) (hp : p > 0) :
  (∑ i, |1 / x i| ^ (-p)) ^ (1 / (-p)) = 1 / ((∑ i, |x i| ^ p) ^ (1 / p)) := by
  sorry



theorem theorem_189223_problem (f : ℝ × ℝ → ℝ × ℝ)
  (h : ∀ x y, f (x, y) = (x, y - x^2)) :
  Function.Injective f := by
  sorry









theorem theorem_189248_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (M Q Λ : Matrix n n ℝ)
  (hM_symm : M.IsSymm)
  (hQ_orth : Q ∈ Matrix.orthogonalGroup n ℝ)
  (hΛ_diag : Λ.IsDiag)
  (h_decomp : M = Q * Λ * Q.transpose)
  (hΛ_nonneg : ∀ i, Λ i i ≥ 0) :
  let sqrtΛ := Matrix.diagonal (fun i => Real.sqrt (Λ i i))
  let M_half := Q * sqrtΛ * Q.transpose
  (M_half ^ 2 = M ∧ M_half.PosSemidef) ∧
  (∀ C : Matrix n n ℝ, C ^ 2 = M → C.PosSemidef → C = M_half) := by
  sorry





theorem theorem_190016_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
  (h_unitary : A ∈ Matrix.unitaryGroup (Fin n) ℂ)
  (h_upper : ∀ i j : Fin n, j < i → A i j = 0) :
  ∀ i j : Fin n, i ≠ j → A i j = 0 := by
  sorry

theorem theorem_189703_problem
  (ω r v_r : Fin 3 → ℝ)
  (hω : ω ≠ 0)
  (h_cross : crossProduct ω ((2 : ℝ) • v_r + crossProduct ω r) = 0) :
  ∃ c : ℝ, v_r = c • ω - (1 / 2 : ℝ) • crossProduct ω r := by
  sorry

theorem theorem_189504_problem
  {𝕜 : Type*} {X : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  (T U : X →L[𝕜] X)
  (hT : IsUnit T)
  (h_ineq : ‖T - U‖ < ‖(hT.unit).inv‖⁻¹) :
  IsUnit U := by
  sorry



theorem theorem_190040_problem
  (F V : Type*)
  [Field F]
  [AddCommGroup V]
  [Module F V]
  (f : F ≃+* F) :
  let smul' : F → V → V := fun c v ↦ f c • v
  (∀ (a b : F) (v : V), smul' (a * b) v = smul' a (smul' b v)) ∧
  (∀ (v : V), smul' 1 v = v) ∧
  (∀ (a b : F) (v : V), smul' (a + b) v = smul' a v + smul' b v) ∧
  (∀ (a : F) (v w : V), smul' a (v + w) = smul' a v + smul' a w) := by
  sorry









theorem theorem_189726_problem
  {I J K L M N : Type*}
  [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype M] [Fintype N]
  [DecidableEq K] [DecidableEq L] [DecidableEq M] [DecidableEq N]
  (U : (K → L → ℝ) → (M → N → ℝ))
  (Y : (M → N → ℝ) → (I → J → ℝ))
  (x : K → L → ℝ)
  (hU : DifferentiableAt ℝ U x)
  (hY : DifferentiableAt ℝ Y (U x)) :
  ∀ (i : I) (j : J) (k : K) (l : L),
    let E_kl : K → L → ℝ := Pi.single k (Pi.single l 1)
    let E_mn (m : M) (n : N) : M → N → ℝ := Pi.single m (Pi.single n 1)
    -- LHS: The derivative of Y ∘ U with respect to X_{kl}, component ij
    (fderiv ℝ (Y ∘ U) x E_kl) i j =
    -- RHS: Sum over m, n of (dY_{ij}/dU_{mn}) * (dU_{mn}/dX_{kl})
    ∑ m : M, ∑ n : N, (fderiv ℝ Y (U x) (E_mn m n)) i j * (fderiv ℝ U x E_kl) m n := by
  sorry





theorem theorem_190363_problem
  (n : ℕ)
  (a : Fin n → ℝ)
  (c : ℝ)
  (p : (Fin n → ℝ) → ℝ)
  (u v : Fin n → ℝ)
  (hp : ∀ x, p x = (∑ i, a i * x i) + c)
  (γ : ℝ → (Fin n → ℝ))
  (hγ : ∀ t, γ t = t • u + (1 - t) • v) :
  IsLeast ((λ t => p (γ t)) '' Set.Icc 0 1) (min (p u) (p v)) := by
  sorry







theorem theorem_190313_problem
  (r tau phi t : ℝ)
  (E1 E2 E3 E4 : ℂ)
  (hr : r > 0)
  (htau : tau > 0)
  (h1 : E2 = (r : ℂ) * E1 + Complex.I * (t : ℂ) * E3)
  (h2 : E4 = (r : ℂ) * E3 + Complex.I * (t : ℂ) * E1)
  (h3 : E3 = (tau : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) * E4)
  (h4 : r^2 + t^2 = 1)
  (hE1 : E1 ≠ 0)
  (h_denom : 1 - (r : ℂ) * (tau : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) ≠ 0) :
  E2 / E1 = (1 / (r : ℂ)) * (1 + ((r : ℂ)^2 - 1) / (1 - (r : ℂ) * (tau : ℂ) * Complex.exp (Complex.I * (phi : ℂ)))) := by
  sorry

theorem theorem_190337_problem (n : ℕ) (S T A : Matrix (Fin n) (Fin n) ℝ)
  (hS : S.IsSymm)
  (hT : T.IsSymm)
  (hST : (S - T).PosSemidef)
  (hA_symm : A.IsSymm)
  (hA_pos : A.PosSemidef) :
  (A * S).trace ≥ (A * T).trace := by
  sorry





theorem theorem_190551_problem
  (n : ℕ)
  (b : Fin n → ℝ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (x : ℝ → Fin n → ℝ)
  (t : ℝ)
  (h : deriv x t = Matrix.mulVec (Matrix.diagonal (x t)) (b - Matrix.mulVec (A * Matrix.diagonal (x t)) (x t))) :
  ∀ i : Fin n, deriv x t i = x t i * (b i - ∑ j : Fin n, A i j * (x t j) ^ 2) := by
  sorry



theorem theorem_190154_problem
  {E I : Type*} [AddCommGroup E] [Module ℝ E]
  (D : Set E) (hD : Convex ℝ D)
  (f : I → E → ℝ)
  (hf : ∀ i, ConvexOn ℝ D (f i))
  (F : E → ℝ)
  (hF : ∀ x ∈ D, F x = ⨆ i, f i x)
  (h_bdd : ∀ x ∈ D, BddAbove (Set.range (fun i => f i x))) :
  ConvexOn ℝ D F := by
  sorry



theorem theorem_191094_problem
  (f : ℝ → ℝ)
  (M₀ M_n : ℝ)
  (n : ℕ)
  (hM₀ : M₀ > 0)
  (hMn : M_n > 0)
  (hn : n > 1)
  (h_bound : ∀ x : ℝ, |f x| ≤ M₀)
  (h_decay : ∀ x : ℝ, |f x| ≤ M_n / (Real.sqrt (1 + x^2)) ^ n) :
  let C_n := (2 * M_n + 3 * M₀) * ((Real.sqrt 2) ^ (1 / ((n : ℝ) - 1)) - 1) ^ (-(n : ℝ))
  ∀ x y : ℝ, x ≠ 0 → |f (x - y)| ≤ (C_n / (|x| ^ n)) * ((1 + |y|) ^ n) := by
  sorry

theorem theorem_191167_problem (a11 a22 b11 b22 : ℝ)
  (A B : Matrix (Fin 2) (Fin 2) ℝ)
  (hA : A = !![a11, 0; 0, a22])
  (hB : B = !![b11, 0; 0, b22])
  (h_trace : Matrix.trace (A * B) = Matrix.trace A * Matrix.trace B) :
  -a11 * b22 = a22 * b11 := by
  sorry









theorem theorem_191131_problem
  (d D : ℕ)
  (T : Set (EuclideanSpace ℝ (Fin D)))
  (hT : ∀ α ∈ T, ‖α‖ ≤ 1)
  (f : (EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin d)) → ℝ)
  (hf : ∀ X, f X = sSup ((fun α => ‖X α‖^2) '' T)) :
  ∀ X Y : EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin d),
    |Real.sqrt (f X) - Real.sqrt (f Y)| ≤ ‖X - Y‖ := by
  sorry

theorem theorem_190996_problem (n : ℕ) [NeZero n]
  (y : Fin n → ℝ)
  (H : Matrix (Fin n) (Fin n) ℝ)
  (h_symm : H.IsSymm)
  (h_idemp : H * H = H)
  (h_intercept : H.mulVec (fun _ => 1) = fun _ => 1) :
  let y_hat := H.mulVec y
  let e := y - y_hat
  let y_bar := (∑ i, y i) / (n : ℝ)
  ∑ i, (y_bar - y_hat i) * e i = 0 := by
  sorry

theorem theorem_190967_problem 
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (a : E) :
  let f : E → ℝ := fun x ↦ ‖x‖^2 - 2 * inner a x
  ∀ x : E, ∃ Df : E →L[ℝ] ℝ, HasFDerivAt f Df x ∧ 
    ∀ h : E, Df h = 2 * inner x h - 2 * inner a h := by
  sorry



theorem theorem_190807_problem
  (T : ℕ)
  (t : ℕ) (ht : t ∈ Finset.range T)
  (n : ℕ)
  (X_it : Fin n → ℝ) (β : Fin n → ℝ)
  (δ γ : ℕ → ℝ)
  (E : ℕ → ℝ) -- E represents the sequence of shocks
  (ε_it : ℝ)
  -- Definition of the dummy variable d_tau for the specific observation period t
  (d : ℕ → ℝ := fun τ => if τ = t then 1 else 0)
  -- The model y_it defined as a function of the shock value at time t (denoted by x)
  -- The summation is over all periods in the model range
  (y : ℝ → ℝ := fun x =>
    (Matrix.dotProduct X_it β) +
    (∑ τ in Finset.range T, δ τ * d τ) +
    (∑ τ in Finset.range T, γ τ * (d τ * (if τ = t then x else E τ))) +
    ε_it)
  (h_nonzero : γ t ≠ 0) :
  deriv y (E t) ≠ 0 := by
  sorry

theorem theorem_191766_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (F : E → ℝ) (x x_bar : E)
  (hF : ContDiff ℝ 1 F) :
  F x - F x_bar = ∫ t in (0 : ℝ)..1, inner (gradient F (x_bar + t • (x - x_bar))) (x - x_bar) := by
  sorry



theorem theorem_191729_problem
  (n : ℕ) (hn : n > 0)
  (a : Fin 2 → Fin n → ℝ)
  (b : Fin 2 → ℝ)
  (h_indep : LinearIndependent ℝ a) :
  (∀ x : Fin n → ℝ, (∑ j, a 0 j * x j = b 0) → (∑ j, a 1 j * x j = b 1) →
    (∑ j, (a 0 j + a 1 j) * x j = b 0 + b 1)) ∧
  LinearIndependent ℝ (![a 0, a 0 + a 1] : Fin 2 → Fin n → ℝ) := by
  sorry



theorem theorem_191569_problem
  (f : ℂ → ℂ) (z₀ : ℂ) (r M : ℝ)
  (hr : 0 < r)
  (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ r))
  (hM : ∀ z ∈ Metric.sphere z₀ r, Complex.abs (f z) ≤ M) :
  Complex.abs (deriv f z₀) ≤ M / r := by
  sorry







theorem theorem_191966_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {ι : Type*} (b : Basis ι F V)
  (f : V →ₗ[F] V)
  (h : ∀ i : ι, f (b i) = b i) :
  ∀ w : V, f w = w := by
  sorry

theorem theorem_192410_problem
  {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  (A : Subalgebra ℝ C(K, ℝ))
  (h_sep : ∀ x y : K, x ≠ y → ∃ f ∈ A, f x ≠ f y) :
  Dense (A : Set C(K, ℝ)) := by
  sorry

theorem theorem_192123_problem
  (n : ℕ)
  (F : (Fin n → ℝ) → ℝ)
  (U : Set (Fin n → ℝ))
  (p : Fin n → ℝ)
  (h_open : IsOpen U)
  (h_p : p ∈ U)
  (h_diff : ContDiffOn ℝ 2 F U) :
  ∀ i j : Fin n,
    iteratedFDerivWithin ℝ 2 F U p ![Pi.single i 1, Pi.single j 1] =
    iteratedFDerivWithin ℝ 2 F U p ![Pi.single j 1, Pi.single i 1] := by
  sorry





theorem theorem_192498_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (n : ℕ) (hn : 0 < n)
  (F : E →L[ℝ] E)
  (u : E) (hu : u ≠ 0)
  (v : Fin n → E)
  (a : Fin n → ℝ)
  (ha : ∀ j, a j = max 0 ((1 : ℝ) / n - ‖F u - v j‖))
  (j_star : Fin n)
  (hj_min : ∀ j, ‖F u - v j_star‖ ≤ ‖F u - v j‖)
  (hj_bound : ‖F u - v j_star‖ < (1 : ℝ) / n)
  (A : ℝ) (hA : A = ∑ j, a j)
  (F_n_u : E) (hF_n_u : F_n_u = (1 / A) • ∑ j, a j • v j) :
  ‖F u - F_n_u‖ < (1 : ℝ) / n := by
  sorry







theorem theorem_191923_problem
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (A : Set X) (hA : Dense A)
  (f : X) (ε : ℝ) (hε : 0 < ε) :
  ∃ g ∈ A, ‖f - g‖ < ε := by
  sorry

