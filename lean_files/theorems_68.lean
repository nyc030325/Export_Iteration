import Mathlib
import Mathlib.Tactic



theorem theorem_368828_problem (r s t : ℕ)
  (P : Matrix (Fin r) (Fin s) ℝ)
  (Q : Matrix (Fin s) (Fin t) ℝ)
  (M : Matrix (Fin r) (Fin t) ℝ)
  (hM : M = P * Q) :
  ∀ (i : Fin r) (j : Fin t), M i j = ∑ k : Fin s, (P i k) * (Q k j) := by
  sorry

theorem theorem_368427_problem :
  operator_norm = 1 := by
  sorry

theorem theorem_368817_problem
  {K : Type*} [Field K]
  (m n : ℕ) (hn : n ≥ 1)
  (c : Fin n → ℕ)
  (A : (i : Fin n) → Matrix (Fin m) (Fin (c i)) K) :
  let M : Matrix (Fin m) ((i : Fin n) × Fin (c i)) K :=
    fun r j => A j.1 r j.2
  Matrix.rank M ≤ ∑ i, Matrix.rank (A i) := by
  sorry











theorem theorem_368639_problem (M : Matrix (Fin 3) (Fin 3) ℝ) :
  (MeasureTheory.volume (convexHull ℝ (insert 0 (Set.range M)))).toReal = (1 / 6 : ℝ) * |M.det| := by
  sorry





theorem theorem_368703_problem (n : ℕ) :
  convexHull ℝ { A : Matrix (Fin n) (Fin n) ℝ | ∃ x : Fin n → ℝ, A = Matrix.vecMulVec x x } =
  { A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef } := by
  sorry

theorem theorem_369052_problem
  {n : ℕ} {F : Type*} [Field F]
  (A : Matrix (Fin n) (Fin n) F) :
  A.det = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : F) * ∏ i : Fin n, A i (σ i) := by
  sorry

theorem theorem_369684_problem (X : Matrix (Fin 2) (Fin 2) ℝ) (hX : X ≠ 0) :
  X ^ 4 + X ^ 4 = ((2 : ℝ) ^ (1 / 4 : ℝ) • X) ^ 4 := by
  sorry

theorem theorem_369186_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (M : Submodule 𝕜 H) :
  M.orthogonal.orthogonal = M.topologicalClosure := by
  sorry



theorem theorem_369394_problem (a b : ℝ) (E : Set ℝ) (hE : MeasurableSet E) :
  let T : ℝ × ℝ → ℝ := fun p ↦ a * p.1 + b * p.2
  MeasurableSet (T ⁻¹' E) := by
  sorry





theorem theorem_368655_problem
  (f : ℕ → Set.Ioo (0 : ℝ) 1 → ℝ)
  (h_cont : ∀ n, Continuous (f n))
  (h_cauchy : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ x, |f n x - f m x| < ε) :
  ∃ g : Set.Ioo (0 : ℝ) 1 → ℝ,
    Continuous g ∧
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, |f n x - g x| < ε := by
  sorry

theorem theorem_368768_problem (B : Matrix (Fin 3) (Fin 3) ℝ)
  (h_symm : B.IsSymm)
  (BI BII BIII : ℝ)
  (h1 : BI = B.trace)
  (h2 : BII = (1 / 2) * (B.trace ^ 2 - (B ^ 2).trace))
  (h3 : BIII = B.det) :
  (B ^ 3).trace = 3 * BIII - 3 * BII * BI + BI ^ 3 := by
  sorry

theorem theorem_369595_problem (n : ℕ) 
  (norm_a norm_b : (Fin n → ℝ) → ℝ)
  (h_na_def : ∀ x, norm_a x = 0 ↔ x = 0)
  (h_na_hom : ∀ (c : ℝ) x, norm_a (c • x) = |c| * norm_a x)
  (h_na_tri : ∀ x y, norm_a (x + y) ≤ norm_a x + norm_a y)
  (h_nb_def : ∀ x, norm_b x = 0 ↔ x = 0)
  (h_nb_hom : ∀ (c : ℝ) x, norm_b (c • x) = |c| * norm_b x)
  (h_nb_tri : ∀ x y, norm_b (x + y) ≤ norm_b x + norm_b y) :
  ∃ m M : ℝ, m > 0 ∧ M > 0 ∧ ∀ x : Fin n → ℝ, 
    m * norm_b x ≤ norm_a x ∧ norm_a x ≤ M * norm_b x := by
  sorry

theorem theorem_369276_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  (B : Set G)
  (h : ∀ f : G →L[𝕜] 𝕜, Bornology.IsBounded (f '' B)) :
  Bornology.IsBounded B := by
  sorry



theorem theorem_369586_problem (p : ℕ) (x : Fin p → ℝ)
  (A B : Matrix (Fin p) (Fin p) ℝ)
  (hx : ∀ i, 0 < x i)
  (hsum : ∑ i, x i = p)
  (hA : A = 1)
  (hB : B = Matrix.diagonal x) :
  Matrix.trace (A⁻¹ * B) = p := by
  sorry

theorem theorem_369322_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (h : n > 0) :
  sSup {r : ℝ | ∃ x : Fin n → ℝ, ∑ i, |x i| = 1 ∧ r = ∑ i, |(Matrix.mulVec A x) i|} =
  ⨆ j, ∑ i, |A i j| := by
  sorry



theorem theorem_369606_problem
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  (h_dim : ¬ FiniteDimensional ℝ X) :
  ∃ f : X →ₗ[ℝ] ℝ, ¬ Continuous f := by
  sorry



theorem theorem_369898_problem
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (c : Fin n → ℤ)
  (d : ℝ)
  (x : Fin n → ℤ)
  (α : Fin m → ℝ)
  (h_nonneg : ∀ i, 0 ≤ α i)
  (h_c : ∀ j, (c j : ℝ) = ∑ i, α i * A i j)
  (h_d : d = ∑ i, α i * b i)
  (h_Ax : ∀ i, ∑ j, A i j * (x j : ℝ) ≤ b i) :
  ∑ j, c j * x j ≤ Int.floor d := by
  sorry

theorem theorem_370251_problem (n : ℕ) :
  Continuous (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) ∧
  Continuous (Matrix.det : Matrix (Fin n) (Fin n) ℂ → ℂ) := by
  sorry











theorem theorem_369994_problem
  (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : Invertible A)
  (X : ℕ → Matrix (Fin n) (Fin n) ℝ)
  (h_iter : ∀ k, X (k + 1) = X k * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - A * X k * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - A * X k))) :
  ∀ k, (1 : Matrix (Fin n) (Fin n) ℝ) - A * X (k + 1) = ((1 : Matrix (Fin n) (Fin n) ℝ) - A * X k) ^ 3 := by
  sorry









theorem theorem_370534_problem
  (n : ℕ)
  (D : Set (Fin n → ℝ))
  (hD_conv : Convex ℝ D)
  (hD_nonempty : D.Nonempty)
  (f : (Fin n → ℝ) → ℝ)
  (hf_diff : ContDiffOn ℝ 2 f D)
  (h_hess : ∀ x ∈ D, ∀ v : Fin n → ℝ, 0 ≤ iteratedFDerivWithin ℝ 2 f D x (fun _ : Fin 2 => v)) :
  ConvexOn ℝ D f := by
  sorry

theorem theorem_370434_problem
  (K : Type*) [Field K]
  (G : Type*) [Group G]
  (V : Type*) [AddCommGroup V] [Module K V]
  (φ : G →* (V ≃ₗ[K] V)) :
  ∃! Φ : MonoidAlgebra K G →ₐ[K] Module.End K V,
    ∀ g : G, Φ (MonoidAlgebra.of K G g) = (φ g : Module.End K V) := by
  sorry



theorem theorem_370415_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [CommRing R]
  (A C : Matrix n n R)
  (hA : A.IsSymm) :
  Matrix.diag (A * (A.hadamard C) * A) =
  ((A * (A.hadamard C)).hadamard A).mulVec (fun _ => 1) := by
  sorry

theorem theorem_370643_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (D : Module.End ℝ V)
  (P_L P_M : Polynomial ℝ)
  (L M : Module.End ℝ V)
  (hL : L = Polynomial.aeval D P_L)
  (hM : M = Polynomial.aeval D P_M)
  (y f : V)
  (h1 : L y = f)
  (h2 : M f = 0) :
  (M * L) y = 0 := by
  sorry



theorem theorem_370822_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  {W : Type*} [AddCommGroup W] [Module F W]
  {ι : Type*} (b : Basis ι F V)
  (L : V →ₗ[F] W) (v : V) :
  L v = (b.repr v).sum (fun i a => a • L (b i)) := by
  sorry





theorem theorem_370547_problem (f g : ℝ → ℝ) (x₀ : ℝ)
  (hf : DifferentiableAt ℝ f x₀)
  (hg : DifferentiableAt ℝ g x₀)
  (h_not_vanish : f x₀ ≠ 0 ∨ g x₀ ≠ 0) :
  ((g x₀ ≠ 0 → deriv (fun x ↦ f x / g x) x₀ = 0) ∧
   (f x₀ ≠ 0 → deriv (fun x ↦ g x / f x) x₀ = 0)) ↔
  f x₀ * deriv g x₀ - deriv f x₀ * g x₀ = 0 := by
  sorry



theorem theorem_370871_problem
  (n : ℕ)
  (a : Fin n → ℝ)
  (b : ℝ)
  (ha : a ≠ 0)
  (H : Set (Fin n → ℝ))
  (hH : H = {y | Matrix.dotProduct a y = b})
  (x₀ : Fin n → ℝ)
  (hx₀ : Matrix.dotProduct a x₀ = b)
  (y : Fin n → ℝ)
  (hy : y ∈ H) :
  ∃! x : Fin n → ℝ, Matrix.dotProduct a x = 0 ∧ y = x₀ + x := by
  sorry

theorem theorem_370956_problem (n : ℕ) (U : Matrix (Fin n) (Fin n) ℂ) :
  (∀ x : Fin n → ℂ, Matrix.dotProduct (star (Matrix.mulVec U x)) (Matrix.mulVec U x) = Matrix.dotProduct (star x) x) ↔
  U.conjTranspose * U = 1 := by
  sorry

















theorem theorem_371416_problem
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (hV : FiniteDimensional.finrank ℝ V = 3)
  (P₁ : Submodule ℝ V)
  (hP₁ : FiniteDimensional.finrank ℝ P₁ = 2) :
  FiniteDimensional.finrank ℝ P₁.orthogonal = 1 := by
  sorry





theorem theorem_371527_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  (T : V →ₗ[K] W) :
  ∃ S : Submodule K W, (S : Set W) = {w | ∃ v, T v = w} := by
  sorry





theorem theorem_371089_problem (n : ℕ) (A B : Basis (Fin n) ℝ (Fin n → ℝ)) :
  let F := fun (f : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ↦ LinearMap.toMatrix A A f
  let G := fun (f : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ↦ LinearMap.toMatrix B B f
  let η := A.toMatrix B
  (∀ f, η * F f = G f * η) ∧ IsUnit η := by
  sorry

theorem theorem_370996_problem (f : ℂ → ℂ) (n : ℝ) (hn : 1 < n)
  (hf_holo : DifferentiableOn ℂ f (Metric.ball 0 1))
  (hf_bound : ∀ z ∈ Metric.ball 0 1, Complex.abs (f z) ≤ 1 / (1 - Complex.abs z) ^ n) :
  ∀ z ∈ Metric.ball 0 1,
    Complex.abs (deriv f z) < n / ((1 - Complex.abs z) ^ (n + 1) * (1 - 1 / n) ^ n) := by
  sorry

theorem theorem_371741_problem
  (k : Type*) [Field k]
  (A : Type*) [CommRing A] [IsDomain A] [Algebra k A]
  (hA : Algebra.FiniteType k A)
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra A L] [IsScalarTower A K L] :
  Module.Finite A (integralClosure A L) := by
  sorry



theorem theorem_371750_problem (n k : ℕ)
  (a : Fin k → (Fin n → ℝ))
  (c : Fin k → ℝ)
  (h_distinct : Function.Injective a)
  (h_zero : ∀ z : Fin n → ℝ, ∑ i : Fin k, c i * Real.exp (Matrix.dotProduct (a i) z) = 0) :
  ∀ i : Fin k, c i = 0 := by
  sorry









theorem theorem_371962_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  (h : ∀ (a : F) (v : V), a ≠ 0 → v ≠ 0 → a • v = 0) :
  ∀ v : V, v = 0 := by
  sorry

theorem theorem_372540_problem
  (V : Type*) [AddCommGroup V] [Module ℝ V]
  (norm_i norm_j : V → ℝ)
  (α : ℝ)
  (hα : 0 < α)
  (h : ∀ x : V, norm_j x ≤ α * norm_i x) :
  {x : V | norm_i x < 1} ⊆ {x : V | norm_j x < α} := by
  sorry

theorem theorem_372195_problem (s j N : ℝ) (f : ℤ → ℂ)
  (hs : 0 ≤ s) (hjs : j ≤ s) (hN : 0 < N)
  (hf : Summable (fun n : ℤ ↦ (1 + |(n : ℝ)|) ^ (2 * s) * ‖f n‖ ^ 2)) :
  Real.sqrt (∑' n : ℤ, if |(n : ℝ)| > N then (1 + |(n : ℝ)|) ^ (2 * j) * ‖f n‖ ^ 2 else 0) ≤
  N ^ (j - s) * Real.sqrt (∑' n : ℤ, (1 + |(n : ℝ)|) ^ (2 * s) * ‖f n‖ ^ 2) := by
  sorry

theorem theorem_372240_problem
  (n : ℕ) (hn : 0 < n)
  (X : Fin n → ℝ)
  (X_bar : ℝ) (hX_bar : X_bar = (∑ i, X i) / n)
  (S_XX : ℝ) (hS_XX : S_XX = ∑ i, (X i - X_bar)^2)
  (h_denom : S_XX ≠ 0)
  (c : Fin n → ℝ) (hc : ∀ i, c i = (X i - X_bar) / S_XX)
  -- Abstract probability space setup
  (RV : Type*) [AddCommGroup RV] [Module ℝ RV]
  (Cov : RV → RV → ℝ)
  -- Properties of Covariance (Bilinearity)
  (cov_add_left : ∀ x y z, Cov (x + y) z = Cov x z + Cov y z)
  (cov_add_right : ∀ x y z, Cov x (y + z) = Cov x y + Cov x z)
  (cov_smul_left : ∀ (r : ℝ) x y, Cov (r • x) y = r * Cov x y)
  (cov_smul_right : ∀ (r : ℝ) x y, Cov x (r • y) = r * Cov x y)
  -- Constants in probability space
  (const : ℝ → RV)
  (cov_const_left : ∀ (r : ℝ) x, Cov (const r) x = 0)
  (cov_const_right : ∀ (r : ℝ) x, Cov x (const r) = 0)
  -- Errors and parameters
  (σ_sq : ℝ)
  (ε : Fin n → RV)
  (h_indep : ∀ i j, Cov (ε i) (ε j) = if i = j then σ_sq else 0)
  (β₀ β₁ : ℝ)
  -- Regression Model
  (Y : Fin n → RV) (hY : ∀ i, Y i = const (β₀ + β₁ * X i) + ε i)
  (beta_hat_1 : RV) (h_beta : beta_hat_1 = ∑ i, c i • Y i)
  (eps_bar : RV) (h_eps : eps_bar = (1 / (n : ℝ)) • ∑ i, ε i) :
  Cov eps_bar beta_hat_1 = 0 := by
  sorry

theorem theorem_372235_problem
  {m p : ℕ} {K : Type*} [Field K]
  (C : Matrix (Fin m) (Fin p) K)
  (h_mp : m < p)
  (h_rank : Matrix.rank C = m) :
  let D := C.transpose * (C * C.transpose)⁻¹
  C * D = 1 := by
  sorry



theorem theorem_372737_problem (n : ℕ)
  (L : Set (Fin (n + 1) → ℂ))
  (hL : L = {z | z (Fin.last n) = 0})
  (C : Set (Fin (n + 1) → ℂ))
  (hC : C = {z | ∀ i, Complex.abs (z i) = 1}) :
  L ∩ C = ∅ := by
  sorry









theorem theorem_372714_problem (m n p : ℕ)
  (X : Matrix (Fin m) (Fin n) ℝ)
  (Θ : Matrix (Fin n) (Fin p) ℝ)
  (Y : Matrix (Fin m) (Fin p) ℝ) :
  Matrix.trace ((X * Θ - Y).transpose * (X * Θ - Y)) = 
  ∑ i : Fin m, ∑ j : Fin p, ((X * Θ - Y) i j) ^ 2 := by
  sorry



theorem theorem_373640_problem
  {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (L : V →L[ℝ] W) (x : V) :
  fderiv ℝ L x = L := by
  sorry

theorem theorem_372645_problem
  {E : Type*} [AddCommGroup E]
  (I : E → ℂ)
  (C : Set E)
  (h_lin : ∀ x y z : E, x ∈ C → y ∈ C → z ∈ C → x = y + z → I x = I y + I z)
  (h_reg : ∀ (f g h : E) (ε : ℝ), 0 < ε →
    ∃ tf tg th : E, tf ∈ C ∧ tg ∈ C ∧ th ∈ C ∧
      tf = tg + th ∧
      Complex.abs (I f - I tf) < ε ∧
      Complex.abs (I g - I tg) < ε ∧
      Complex.abs (I h - I th) < ε) :
  ∀ f g : E, I (f + g) = I f + I g := by
  sorry

theorem theorem_373001_problem (n : ℕ) (L : Set (EuclideanSpace ℝ (Fin n))) (r : ℝ) (hr : r > 0) :
  (∀ x : EuclideanSpace ℝ (Fin n), ∃ l ∈ L, ‖x - l‖ ≤ r) ↔
  (⋃ l ∈ L, Metric.closedBall l r) = Set.univ := by
  sorry

theorem theorem_373070_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (A : E →L[𝕜] E)
  (x : E)
  (hx : x ≠ 0) :
  ‖A‖ ≥ ‖A x‖ / ‖x‖ := by
  sorry

theorem theorem_372752_problem (a b c d : Fin 3 → ℝ) :
  Matrix.det !![a 0, a 1, a 2, 1;
                b 0, b 1, b 2, 1;
                c 0, c 1, c 2, 1;
                d 0, d 1, d 2, 1] =
  - Matrix.det !![b 0 - a 0, b 1 - a 1, b 2 - a 2;
                  c 0 - a 0, c 1 - a 1, c 2 - a 2;
                  d 0 - a 0, d 1 - a 1, d 2 - a 2] := by
  sorry

theorem theorem_373369_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ) (x_tilde : E) (x : E)
  (hf : ContDiff ℝ 2 f)
  (q : E → ℝ)
  (hq : ∀ y, q y = f x_tilde + inner (gradient f x_tilde) (y - x_tilde) +
    (1 / 2 : ℝ) * inner ((fderiv ℝ (gradient f) x_tilde) (y - x_tilde)) (y - x_tilde)) :
  gradient q x = gradient f x_tilde + (fderiv ℝ (gradient f) x_tilde) (x - x_tilde) := by
  sorry







