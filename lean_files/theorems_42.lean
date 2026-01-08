import Mathlib
import Mathlib.Tactic



theorem theorem_225280_problem
  (F V : Type*) [Field F] [AddCommGroup V] [Module F V] :
  (∀ f g : V → F, IsLinearMap F f → IsLinearMap F g → IsLinearMap F (f + g)) ∧
  (∀ (c : F) (f : V → F), IsLinearMap F f → IsLinearMap F (c • f)) ∧
  (IsLinearMap F (0 : V → F)) ∧
  (∀ f : V → F, IsLinearMap F f → IsLinearMap F (-f)) := by
  sorry



















theorem theorem_226978_problem
  (n : ℕ)
  (A L U : Matrix (Fin n) (Fin n) ℝ)
  (h_symm : A.IsSymm)
  (h_L_lower : ∀ i j, i < j → L i j = 0)
  (h_L_inv : IsUnit L)
  (h_U_upper : ∀ i j, j < i → U i j = 0)
  (h_fact : A = L * U) :
  ∃ D : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j, i ≠ j → D i j = 0) ∧ U = D * L.transpose := by
  sorry



theorem theorem_226200_problem {I X : Type*}
  [AddCommGroup X] [Module ℝ X]
  (T : X →ₗ[ℝ] X)
  (x : I → X)
  (lam : I → ℝ)
  (h_nonzero : ∀ i, x i ≠ 0)
  (h_eigen : ∀ i, T (x i) = lam i • x i)
  (h_distinct : ∀ i j, i ≠ j → lam i ≠ lam j) :
  LinearIndependent ℝ x := by
  sorry

theorem theorem_226542_problem (n : ℕ) (V : Matrix (Fin n) (Fin n) ℝ) :
  MeasureTheory.volume (convexHull ℝ (insert (0 : Fin n → ℝ) (Set.range (fun j i => V i j)))) =
  ENNReal.ofReal (abs V.det / (n.factorial : ℝ)) := by
  sorry





theorem theorem_226203_problem (n : ℕ) :
  let O : Set (Matrix (Fin n) (Fin n) ℝ) := {Q | Q.transpose * Q = 1}
  let Z : Set (Matrix (Fin n) (Fin n) ℝ) := {A ∈ O | ∀ Q ∈ O, A * Q = Q * A}
  Z = {1, -1} := by
  sorry





theorem theorem_226637_problem 
  (n : ℕ) 
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (x : Fin n → E) 
  (h_indep : LinearIndependent ℝ x) :
  ∃ c > 0, ∀ a : Fin n → ℝ, a ≠ 0 → 
    ‖∑ i, a i • x i‖ / (∑ i, |a i|) ≥ c := by
  sorry

theorem theorem_226979_problem
  (r : ℝ) (hr : 0 < r)
  (P : Type*) [TopologicalSpace P]
  (f : ℂ → P → ℂ)
  (N : Set ℂ) (hN_cpt : IsCompact N) (hN_circle : Metric.sphere 0 r ⊆ N)
  (h_cont_z : ∀ z₀ : P, ContinuousOn (fun z ↦ f z z₀) N)
  (h_cont_p : ∀ z ∈ N, Continuous (fun z₀ ↦ f z z₀))
  (h_bound : ∃ M, ∀ z ∈ N, ∀ z₀ : P, ‖f z z₀‖ ≤ M) :
  Continuous (fun z₀ ↦ circleIntegral (fun z ↦ f z z₀) 0 r) := by
  sorry

theorem theorem_226272_problem
  {R : Type*} [CommRing R]
  {V : Type*} [AddCommGroup V] [Module R V]
  -- v induces a derivation δ on functions
  (δ : Derivation R R R)
  -- ∇_v is the covariant derivative on V, denoted D here
  (D : V → V)
  (hD_add : ∀ x y, D (x + y) = D x + D y)
  (hD_leibniz : ∀ (f : R) (x : V), D (f • x) = δ f • x + f • D x)
  -- T and S are tensor fields, modeled as multilinear maps to scalars
  {k l : ℕ}
  (T : MultilinearMap R (fun _ : Fin k => V) R)
  (S : MultilinearMap R (fun _ : Fin l => V) R)
  -- The tensor product T ⊗ S
  (TS : MultilinearMap R (fun _ : Fin (k + l) => V) R)
  (hTS : ∀ (x : Fin (k + l) → V), 
    TS x = T (fun i => x (Fin.castAdd l i)) * S (fun i => x (Fin.natAdd k i)))
  -- Definition of covariant derivative on tensor fields
  (covDeriv : ∀ {n}, MultilinearMap R (fun _ : Fin n => V) R → MultilinearMap R (fun _ : Fin n => V) R)
  (h_covDeriv : ∀ {n} (A : MultilinearMap R (fun _ : Fin n => V) R) (x : Fin n → V),
    covDeriv A x = δ (A x) - ∑ i : Fin n, A (Function.update x i (D (x i))))
  : 
  -- Conclusion: Product rule
  ∀ (x : Fin (k + l) → V),
    covDeriv TS x = 
      (covDeriv T (fun i => x (Fin.castAdd l i)) * S (fun i => x (Fin.natAdd k i))) + 
      (T (fun i => x (Fin.castAdd l i)) * covDeriv S (fun i => x (Fin.natAdd k i))) := by
  sorry

theorem theorem_226326_problem
  {R V W : Type*} [Field R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]
  (h_char : (2 : R) ≠ 0)
  (n : ℕ)
  (Δ : MultilinearMap R (fun _ : Fin n => V) W)
  (h_skew : ∀ (x : Fin n → V) (i j : Fin n), i ≠ j → Δ (x ∘ Equiv.swap i j) = - Δ x)
  (v : V)
  (e : Fin n → V) :
  Δ (fun i => if i.val = 0 then v else v - e i) = Δ (fun i => if i.val = 0 then v else - e i) := by
  sorry





theorem theorem_227080_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (φ : E → E)
  (C : ℝ)
  (hC : 0 < C)
  (h_lip : ∀ x y : E, ‖φ x - φ y‖ ≤ C * ‖x - y‖)
  (x y : ℕ → E)
  (h_neq : ∀ k, k ≥ 1 → x k ≠ y k)
  (h_ineq : ∀ k, k ≥ 1 → inner (φ (x k) - φ (y k)) (x k - y k) ≥ (k : ℝ) * ‖x k - y k‖ ^ 2) :
  False := by
  sorry









theorem theorem_227394_problem
  {F : Type*} [Field F]
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix m n F) (B : Matrix m Unit F) :
  (∃ X : Matrix n Unit F, A * X = B) ↔
  Matrix.rank A = Matrix.rank (Matrix.of (fun i (j : Sum n Unit) =>
    match j with
    | Sum.inl c => A i c
    | Sum.inr _ => B i ())) := by
  sorry







theorem theorem_227622_problem
  (K : Type*) [Field K]
  (A : Type*) [CommRing A] [Algebra K A]
  -- The bracket is a map from A to a linear map on A (linearity in 2nd arg)
  (bracket : A → A →ₗ[K] A)
  -- Antisymmetry condition
  (h_anti : ∀ a b, bracket a b = - bracket b a)
  -- Leibniz rule condition
  (h_leib : ∀ a b c, bracket a (b * c) = bracket a b * c + b * bracket a c) :
  -- Conclusion: For any x, {x, .} is a derivation
  ∀ x : A, ∃ D : Derivation K A A, ∀ y, D y = bracket x y := by
  sorry

theorem theorem_227595_problem (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℝ) :
  (X.transpose * X + Y.transpose * Y).det ≥ (X.transpose * Y - Y.transpose * X).det := by
  sorry





theorem theorem_227609_problem
  (n : ℕ)
  (a b p1 p2 : Fin n → ℝ)
  (s_t : ℝ)
  (Ω : Type*)
  (E : (Ω → ℝ) → ℝ)
  (h_lin : ∀ (X Y : Ω → ℝ) (r s : ℝ), E (fun ω ↦ r * X ω + s * Y ω) = r * E X + s * E Y)
  (h_const : ∀ c : ℝ, E (fun _ ↦ c) = c)
  (ε1 ε2 : Ω → ℝ)
  (h_mean1 : E ε1 = 0)
  (h_mean2 : E ε2 = 0)
  (x_t : Ω → ℝ)
  (hx : x_t = fun ω ↦ Matrix.dotProduct a p1 + ε1 ω)
  (y_t : Ω → ℝ)
  (hy : y_t = fun ω ↦ Matrix.dotProduct b p2 + ε2 ω)
  (Δ_t : Ω → ℝ)
  (hΔ : Δ_t = fun ω ↦ x_t ω - y_t ω)
  (s_next : Ω → ℝ)
  (hs : s_next = fun ω ↦ s_t + Δ_t ω) :
  E s_next = s_t + Matrix.dotProduct a p1 - Matrix.dotProduct b p2 := by
  sorry

theorem theorem_227400_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (x : ℕ → V) :
  Summable x ↔ ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → ‖∑ k in Finset.Icc m n, x k‖ < ε := by
  sorry

theorem theorem_228015_problem (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.det > 0) :
  ∃ ε > 0, ∀ A : Matrix (Fin n) (Fin n) ℝ,
  (∀ i j, |A i j - M i j| < ε) → A.det > 0 := by
  sorry

theorem theorem_227567_problem
  (n : ℕ) (A₁ A₂ : Matrix (Fin n) (Fin n) ℂ)
  (hA₁ : A₁.IsHermitian) (hA₂ : A₂.IsHermitian)
  (m : ℕ) (hm : 2 * n - 1 ≤ m) :
  ∃ H₁ H₂ : Matrix (Fin m) (Fin m) ℂ,
    H₁.IsHermitian ∧ H₂.IsHermitian ∧ Commute H₁ H₂ ∧
    let cast := Fin.castLE (show n ≤ m by omega)
    H₁.submatrix cast cast = A₁ ∧
    H₂.submatrix cast cast = A₂ := by
  sorry



theorem theorem_227756_problem (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : IsUnit A.det) :
  ∃ (V T : Matrix (Fin 2) (Fin 2) ℂ),
    IsUnit V.det ∧
    A = V * T * V⁻¹ ∧
    T 1 0 = 0 ∧
    T 0 0 ≠ 0 ∧
    T 1 1 ≠ 0 := by
  sorry

theorem theorem_228692_problem {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [Field K]
  (G S P : Matrix n n K)
  [Invertible G]
  (hP : P.transpose * G * P = G) :
  Matrix.trace (G⁻¹ * (P.transpose * S * P)) = Matrix.trace (G⁻¹ * S) := by
  sorry

theorem theorem_228765_problem
  (n : ℕ)
  (R : Matrix (Fin n) (Fin n) ℝ)
  [Invertible R] :
  (R.transpose * R)⁻¹ * R.transpose = R⁻¹ := by
  sorry



theorem theorem_228153_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (x₁ x₂ : E)
  (h₁ : x₁ ≠ 0)
  (h₂ : x₂ ≠ 0)
  (h_opp : ∃ c : ℝ, c < 0 ∧ x₂ = c • x₁) :
  ‖(‖x₁‖⁻¹ • x₁) - (‖x₂‖⁻¹ • x₂)‖ = 2 := by
  sorry



theorem theorem_229223_problem {n : ℕ} {K : Type*} [CommRing K] (A : Matrix (Fin n) (Fin n) K) :
  (Matrix.charpoly A).eval 0 = (-1 : K) ^ n * Matrix.det A := by
  sorry





theorem theorem_228956_problem {F : Type*} [Field F] {m n : ℕ}
  (A : Matrix (Fin m) (Fin n) F) :
  Matrix.rank A = Matrix.rank A.transpose := by
  sorry













theorem theorem_229244_problem
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  (inner : V → V → ℂ)
  (h_lin_first : ∀ (u v : V) (r : ℂ), inner (r • u) v = r * inner u v)
  (h_clin_second : ∀ (u v : V) (r : ℂ), inner u (r • v) = (star r) * inner u v)
  (a b c d e f : V) :
  inner ((inner a b) • c) ((inner d e) • f) =
    (inner a b) * (star (inner d e)) * (inner c f) := by
  sorry







theorem theorem_229850_problem
  {F : Type*} [Field F]
  (n k t m : ℕ)
  (C : Submodule F (Fin n → F))
  (H : Matrix (Fin (t * m)) (Fin n) F)
  (hC : C = LinearMap.ker (Matrix.toLin' H))
  (hk : k = FiniteDimensional.finrank F C) :
  k ≥ n - t * m := by
  sorry



theorem theorem_229765_problem
  {R : Type*} [CommRing R]
  {A : Type*} [AddCommGroup A] [Module R A]
  (a₁ : A)
  (C : Submodule R A)
  (h_decomp : IsCompl (Submodule.span R {a₁}) C)
  (π : A →ₗ[R] C)
  (h_π : ∀ (r : R) (c : C), π (r • a₁ + c) = c) :
  π a₁ = 0 := by
  sorry

theorem theorem_229575_problem
  (F V : Type*)
  [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (n : ℕ)
  (h_dim : FiniteDimensional.finrank F V = n)
  (S : Set V)
  (h_card : S.ncard = n + 1) :
  ¬ LinearIndependent F (fun (v : S) ↦ (v : V)) := by
  sorry

theorem theorem_229021_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (e : Basis (Fin 5) ℝ V) :
  ∀ v : V, ∃! p : V × ℝ,
    p.1 ∈ Submodule.span ℝ ({e 0, e 1, e 2, e 3} : Set V) ∧
    v = p.1 + p.2 • (e 4) := by
  sorry

theorem theorem_229813_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
  (h : spectralRadius ℂ A < 1) :
  Filter.Tendsto (fun k ↦ A ^ k) Filter.atTop (nhds 0) := by
  sorry



theorem theorem_229426_problem
  (n : ℕ)
  (x : (Fin n → ℝ) → ℝ)
  (u : ℝ → (Fin n → ℝ))
  (s : ℝ)
  (hx : ContDiff ℝ ⊤ x)
  (hu : ContDiff ℝ ⊤ u) :
  deriv (fun t => x (u t)) s =
  ∑ j : Fin n, (deriv (fun t => u t j) s) * (fderiv ℝ x (u s) (Pi.single j 1)) := by
  sorry











theorem theorem_229899_problem {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (x y : V) (c : ℝ) : ‖x + c • y‖ ≤ ‖x‖ + |c| * ‖y‖ := by
  sorry











theorem theorem_230148_problem
  (n d m : ℕ)
  (X : Fin n → Fin d → ℝ)
  (Y : Fin n → Fin m → ℝ)
  (k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
  -- We model the "relevance" as a function mapping a covariance structure to a weight vector
  (relevance_map : ((Fin d → ℝ) → (Fin d → ℝ) → ℝ) → (Fin d → ℝ))
  -- Let output_covariance j be the covariance structure associated with the j-th output
  (output_covariance : Fin m → ((Fin d → ℝ) → (Fin d → ℝ) → ℝ))
  -- The condition that outputs are generated by a shared latent GP with covariance k
  -- implies the covariance for each output is k.
  (h_shared : ∀ j : Fin m, output_covariance j = k) :
  -- Conclusion: Relevance weights are identical across all outputs
  ∀ j1 j2 : Fin m, relevance_map (output_covariance j1) = relevance_map (output_covariance j2) := by
  sorry

theorem theorem_230179_problem
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (A : E →L[ℝ] F) (v : E) :
  ‖A v‖ ≤ ‖A‖ * ‖v‖ := by
  sorry

theorem theorem_230401_problem
  (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
  (X : Type*) [AddCommGroup X] [Module K X] [TopologicalSpace X] [TopologicalAddGroup X] [ContinuousSMul K X]
  (Y : Type*) [AddCommGroup Y] [Module K Y] [TopologicalSpace Y] [TopologicalAddGroup Y] [ContinuousSMul K Y]
  (Λ : X →ₗ[K] Y)
  (h_surj : Function.Surjective Λ)
  (h_cont : Continuous Λ)
  [FiniteDimensional K Y] :
  IsOpenMap Λ := by
  sorry







theorem theorem_230845_problem : ¬ FiniteDimensional ℚ ℝ := by
  sorry

theorem theorem_230417_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  (φ ψ : V →ₗ[K] W)
  (h_rank : FiniteDimensional.finrank K (LinearMap.range φ) = FiniteDimensional.finrank K (LinearMap.range ψ)) :
  ∃ (a : V ≃ₗ[K] V) (b : LinearMap.range φ ≃ₗ[K] LinearMap.range ψ),
    ∀ v : V, (b ⟨φ v, LinearMap.mem_range_self φ v⟩ : W) = ψ (a v) := by
  sorry







theorem theorem_230999_problem
  (F : Type*) [Field F]
  (G : Type*) [Group G]
  (V : Type*) [AddCommGroup V] [Module F V]
  [DistribMulAction G V] :
  ∃ (inst : Module (MonoidAlgebra F G) V),
    ∀ (x : MonoidAlgebra F G) (v : V),
      let _ := inst
      x • v = (x : G →₀ F).sum (fun g r => r • (g • v)) := by
  sorry

theorem theorem_231477_problem (x y : ℝ)
  (z : ℂ) (hz : z = x + y * Complex.I)
  (u : ℝ) (hu : u = Real.exp (x^2 - y^2) * Real.cos (2 * x * y)) :
  u = (Complex.exp (z ^ 2)).re := by
  sorry







theorem theorem_231217_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  (S : Set (V →ₗ[F] F)) :
  ∃ W : Submodule F V, (W : Set V) = { v : V | ∀ f ∈ S, f v = 0 } := by
  sorry

