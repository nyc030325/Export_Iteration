import Mathlib
import Mathlib.Tactic







theorem theorem_294808_problem (k : ℕ) (c : Fin k → ℝ)
  (S : Set (ℕ → ℝ))
  (hS : S = { a | ∀ n ≥ k, a n = ∑ i : Fin k, c i * a (n - (i + 1)) })
  (F : Set (ℕ → ℝ))
  (hF_subset : F ⊆ S)
  (hF_finite : F.Finite)
  (h_card : F.ncard > k) :
  ¬ LinearIndependent ℝ (fun (x : F) ↦ (x : ℕ → ℝ)) := by
  sorry



theorem theorem_294522_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (p : V →ₗ[F] V →ₗ[F] F)
  (h_skew : ∀ x y, p x y = -p y x)
  (h_nondeg : ∀ x, (∀ y, p x y = 0) → x = 0)
  (f : V ≃ₗ[F] V)
  {ι : Type*} (b : Basis ι F V)
  (h_basis : ∀ i j, p (f (b i)) (f (b j)) = p (b i) (b j)) :
  ∀ x y, p (f x) (f y) = p x y := by
  sorry



theorem theorem_295211_problem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (A A' : V →ₗ[K] V) :
  LinearMap.ker (LinearMap.prod A A') = LinearMap.ker A ⊓ LinearMap.ker A' := by
  sorry







theorem theorem_294833_problem {V : Type*} [AddCommGroup V] [Module ℝ V]
  (B : V → V → ℝ)
  (h_sym : ∀ v w : V, B v w = B w v)
  (h_lin_left : ∀ (u v w : V) (a b : ℝ), B (a • u + b • v) w = a * B u w + b * B v w)
  (h_lin_right : ∀ (u v w : V) (a b : ℝ), B u (a • v + b • w) = a * B u v + b * B u w)
  (h_pos : ∀ v : V, 0 ≤ B v v)
  (h_nondeg : ∀ v : V, B v v = 0 → v = 0) :
  ∃ (I : InnerProductSpace.Core ℝ V), I.inner = B := by
  sorry

theorem theorem_295160_problem (f : (ℝ × ℝ) → ℝ)
  (h_zero : f 0 = 0)
  (h_bound : ∀ x : ℝ × ℝ, x ≠ 0 → |f x| ≤ ‖x‖ ^ 2) :
  HasFDerivAt f (0 : (ℝ × ℝ) →L[ℝ] ℝ) 0 := by
  sorry

theorem theorem_295472_problem
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (W : Submodule ℝ V)
  (L : V →ₗ[ℝ] Module.Dual ℝ V)
  (hL : ∀ v v', L v v' = inner v v')
  (i : W →ₗ[ℝ] V)
  (hi : i = W.subtype) :
  W.orthogonal = LinearMap.ker ((LinearMap.dualMap i) ∘ₗ L) := by
  sorry







theorem theorem_294847_problem
  (A : ℝ × ℝ → ℝ × ℝ × ℝ × ℝ)
  (W : Set (ℝ × ℝ × ℝ × ℝ))
  (hA : A = fun (u, v) ↦ (u + v, u - v, 2 * v, 3 * u + v))
  (hW : W = {p : ℝ × ℝ × ℝ × ℝ | let (x, y, z, t) := p; x = 1 + z + t ∧ y = -2 - 2 * z - t}) :
  A ⁻¹' W = {p : ℝ × ℝ | let (u, v) := p; 2 * u + 2 * v + 1 = 0} := by
  sorry

theorem theorem_295892_problem 
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (x_seq : ℕ → X) (x : X)
  (Y : Submodule ℝ X) (hY : Y = Submodule.span ℝ (Set.range x_seq))
  (h_weak : ∀ f : X →L[ℝ] ℝ, Filter.Tendsto (fun n ↦ f (x_seq n)) Filter.atTop (nhds (f x))) :
  x ∈ closure (Y : Set X) := by
  sorry



theorem theorem_295600_problem
  (F : Type*) [Field F]
  (n : ℕ) (hn : 0 < n)
  (beta_1 beta_2 : Fin n → F)
  (h_eq : beta_1 = beta_2)
  (h_val : beta_1 = fun i => if i = ⟨0, hn⟩ then 1 else 0) :
  ∃ Φ : (Fin n → F) → (Fin n → F),
    (∀ v, (Φ v) ⟨0, hn⟩ = v ⟨0, hn⟩) ∧
    Φ beta_1 = Φ beta_2 := by
  sorry

theorem theorem_295420_problem (N : ℕ) (hN : 0 < N)
  (P : (ℤ → ℂ) → (ℤ → ℂ))
  (hP : ∀ (f : ℤ → ℂ) (a : ℤ), P f a = if 0 ≤ a ∧ a < N then ∑' (b : ℤ), f (a + b * N) else 0) :
  P ∘ P = P := by
  sorry









theorem theorem_296314_problem
  {K U W : Type*} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
  (f : U →ₗ[K] W)
  (V : Submodule K W)
  (n k : ℕ)
  (x : Fin n → U)
  (u : Fin k → U)
  (hx_indep : LinearIndependent K x)
  (hx_span : Submodule.span K (Set.range x) = LinearMap.ker f)
  (hu_indep : LinearIndependent K (f ∘ u))
  (hu_span : Submodule.span K (Set.range (f ∘ u)) = V ⊓ LinearMap.range f) :
  LinearIndependent K (Sum.elim x u) ∧
  Submodule.span K (Set.range (Sum.elim x u)) = Submodule.comap f V := by
  sorry



theorem theorem_296076_problem (v : Fin 2 → ℝ) (z : ℂ) :
  z • (fun i => (v i : ℂ)) ≠ ![1, Complex.I] := by
  sorry





theorem theorem_296461_problem
  (n d : ℕ)
  (X : Matrix (Fin n) (Fin d) ℝ)
  (y : Fin n → ℝ)
  (w : Fin d → ℝ)
  (hX_mean : ∀ j, ∑ i, X i j = 0)
  (hX_var : ∀ j, ∑ i, (X i j) ^ 2 = (n : ℝ))
  (hy_mean : ∑ i, y i = 0) :
  ∀ i, w i = 0 → ∀ k, w i * X k i = 0 := by
  sorry



theorem theorem_296069_problem 
  (n : ℕ) 
  (A B : Matrix (Fin n) (Fin n) ℂ) 
  (h : ℂ) 
  (f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) 
  (hf : f = fun M ↦ M * M.conjTranspose) : 
  f (A + h • B) - f A = 
    h • (B * A.conjTranspose) + (star h) • (A * B.conjTranspose) + (Complex.normSq h : ℂ) • (B * B.conjTranspose) := by
  sorry

theorem theorem_295383_problem :
  ∃ (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℝ),
    X.PosSemidef ∧ Y.PosSemidef ∧ (Y - X).PosSemidef ∧ ¬ (Y ^ 2 - X ^ 2).PosSemidef := by
  sorry

theorem theorem_297084_problem
  (S : Set ℂ)
  (h_open : IsOpen S)
  (h_conn : IsConnected S)
  (f : ℂ → ℂ)
  (h_analytic : DifferentiableOn ℂ f S)
  (h_re_zero : ∀ z ∈ S, (f z).re = 0) :
  ∃ c : ℝ, ∀ z ∈ S, f z = ↑c * Complex.I := by
  sorry



theorem theorem_296962_problem
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (R : ℝ) (hR : 0 ≤ R)
  (K : {x : E // x ∈ Metric.closedBall (0 : E) R} → {x : E // x ∈ Metric.closedBall (0 : E) R})
  (hK : Continuous K) :
  ∃ x : {x : E // x ∈ Metric.closedBall (0 : E) R}, K x = x := by
  sorry

theorem theorem_296350_problem
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (neighbors : ι → Finset ι)
  (a l h : ι → ι → ℝ)
  (B : Matrix ι ι ℝ)
  (u : ι → ℝ)
  (h1 : ∀ i j, i ≠ j → B i j = if j ∈ neighbors i then (a i j * l i j) / h i j else 0)
  (h2 : ∀ i, B i i = - ∑ j in neighbors i, (a i j * l i j) / h i j) :
  ∀ i, Matrix.mulVec B u i =
    (∑ j in (neighbors i).erase i, ((a i j * l i j) / h i j) * u j) -
    u i * (∑ j in neighbors i, (a i j * l i j) / h i j) := by
  sorry

theorem theorem_296597_problem
  (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x d : EuclideanSpace ℝ (Fin n))
  (h : DifferentiableAt ℝ f x) :
  deriv (fun t : ℝ ↦ f (x + t • d)) 0 = inner (gradient f x) d := by
  sorry





theorem theorem_296198_problem (n : ℕ) (a b : Fin n → ℝ) :
  ∑ i : Fin n, ∑ j : Fin n, (if i < j then (a i * b j - a j * b i)^2 else 0) =
  (∑ i : Fin n, (a i)^2) * (∑ i : Fin n, (b i)^2) - (∑ i : Fin n, a i * b i)^2 := by
  sorry



theorem theorem_296795_problem
  {F : Type*} [Field F] [DecidableEq F]
  {n : ℕ}
  (X : Matrix (Fin n) (Fin n) F)
  (hX : IsUnit X)
  (h : ∀ (B A : Matrix (Fin n) (Fin n) F), IsUnit B → IsUnit A → B * A = X → B * A * B = B * X) :
  ∃ c : F, c ≠ 0 ∧ X = c • (1 : Matrix (Fin n) (Fin n) F) := by
  sorry

theorem theorem_297000_problem (n : ℕ) (u v : Fin n → ℝ) (p q : ℝ)
  (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
  (hu : ∑ i, |u i| ^ p ≠ 0)
  (hv : ∑ i, |v i| ^ q ≠ 0) :
  (∑ i, |u i| * |v i|) /
    ((∑ i, |u i| ^ p) ^ (1 / p) * (∑ i, |v i| ^ q) ^ (1 / q)) ≤ 1 := by
  sorry

theorem theorem_297074_problem
  (n : ℕ)
  (hn : 2 ≤ n)
  (e : Fin n → Fin n → ℝ)
  (he : e = fun i => Pi.single i 1)
  (B : Set (Fin n → ℝ))
  (hB : B = {b | ∃ i j : Fin n, ∃ s₁ s₂ : ℝ, i < j ∧ s₁ ∈ ({-1, 1} : Set ℝ) ∧ s₂ ∈ ({-1, 1} : Set ℝ) ∧ b = s₁ • e i + s₂ • e j})
  (f : (Fin n → ℝ) → ℝ)
  (hf : ∀ x, f x = sSup {y | ∃ b ∈ B, y = Matrix.dotProduct b x}) :
  {p : (Fin n → ℝ) × ℝ | f p.1 ≤ p.2} =
  {p : (Fin n → ℝ) × ℝ | ∀ b ∈ B, Matrix.dotProduct b p.1 - p.2 ≤ 0} := by
  sorry

theorem theorem_296867_problem (n : ℕ) (x y : Fin n → ℝ) :
  ∑ i, (x i * y i)^2 ≤ (∑ i, (x i)^2) * (∑ i, (y i)^2) := by
  sorry



theorem theorem_297183_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (x_n : ℕ → V) (x y : V)
  (h1 : Filter.Tendsto x_n Filter.atTop (nhds x))
  (h2 : Filter.Tendsto x_n Filter.atTop (nhds y)) :
  x = y := by
  sorry









theorem theorem_297638_problem
  (K : Type*) [Field K]
  (V : Type*) [AddCommGroup V] [Module K V]
  [Module.Finite K V]
  (U : Submodule K V)
  (h : U.dualAnnihilator = ⊤) :
  U = ⊥ := by
  sorry



theorem theorem_297114_problem (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
  (h_nonneg : ∀ i j, 0 ≤ P i j)
  (h_sum : ∀ i, ∑ j, P i j = 1)
  (h_irred : ∀ i j, ∃ k, (P ^ k) i j > 0)
  (h_fix : Matrix.mulVec P v = v) :
  ∀ i j, v i = v j := by
  sorry





theorem theorem_296672_problem (n : ℕ)
  (F : (Fin n → ℝ) → (Fin n → ℝ))
  (A : Set (Fin n → ℝ))
  (hF : ∀ y i, F y i = ∑ j in Finset.filter (· ≤ i) Finset.univ, y j)
  (hA : A = { x | Monotone x ∧ (∀ i, 0 ≤ x i) ∧ (∀ i, x i ≤ 1) }) :
  F ⁻¹' A = { y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1 } := by
  sorry





theorem theorem_297644_problem
  {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E] [CharP F 2]
  (b : E →ₗ[F] E →ₗ[F] F)
  (h_symm : LinearMap.IsSymm b)
  (h_nondeg : LinearMap.Nondegenerate b)
  (h_nonalt : ∃ x, b x x ≠ 0) :
  ∃ (ι : Type) (_ : Fintype ι) (e : Basis ι F E), ∀ i j, i ≠ j → b (e i) (e j) = 0 := by
  sorry



theorem theorem_297926_problem
  (a b : ℝ) (hab : a ≤ b)
  (f : ℂ → ℂ) (β : ℝ → ℂ)
  (hf : ContinuousOn f (β '' Set.Icc a b))
  (hβ : ContDiffOn ℝ ⊤ β (Set.Icc a b)) :
  Complex.abs (∫ t in a..b, f (β t) * deriv β t) ≤
  ∫ t in a..b, Complex.abs (f (β t)) * Complex.abs (deriv β t) := by
  sorry







theorem theorem_297804_problem
  {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  (M : Matrix n n ℝ)
  (E : Matrix (n ⊕ m) (n ⊕ m) ℝ)
  (hM_symm : M.IsSymm)
  (hM_neg : (-M).PosDef)
  (hE_symm : E.IsSymm) :
  ∃ δ > 0, ∀ c : ℝ, |c| < δ →
    let H := Matrix.fromBlocks M 0 0 ((-4 : ℝ) • (1 : Matrix m m ℝ)) + c • E
    (-H).PosDef := by
  sorry

theorem theorem_297908_problem
  (k : ℕ)
  (f : Set.Icc (0 : ℝ) 1 → (Fin k → ℝ))
  (h_cont : Continuous f)
  (h_cond : ∀ a : Set.Icc (0 : ℝ) 1, ∀ δ > 0, ∃ ε > 0,
    (Set.range f) ∩ (Metric.ball (f a) ε) ⊆ f '' (Metric.ball a δ)) :
  Function.Injective f := by
  sorry

theorem theorem_298057_problem
  {k G V V' : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V']
  (ρ : Representation k G V)
  (ρ' : Representation k G V')
  (T : V ≃ₗ[k] V')
  (hT : ∀ (g : G) (v : V), T (ρ g v) = ρ' g (T v))
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (B : Basis ι k V)
  (B' : Basis ι k V')
  (hB' : B' = B.map T)
  (g : G) :
  LinearMap.toMatrix B B (ρ g) = LinearMap.toMatrix B' B' (ρ' g) := by
  sorry





theorem theorem_298410_problem
  {K V : Type*}
  [NormedField K]
  [NormedAddCommGroup V]
  [NormedSpace K V]
  [FiniteDimensional K V]
  (A : V ≃ₗ[K] V) :
  (∀ (v : V), ‖A v‖ = 0 ↔ v = 0) ∧
  (∀ (c : K) (v : V), ‖A (c • v)‖ = ‖c‖ * ‖A v‖) ∧
  (∀ (u v : V), ‖A (u + v)‖ ≤ ‖A u‖ + ‖A v‖) := by
  sorry





theorem theorem_298764_problem (a b p q : ℝ) :
  let u : ℝ × ℝ := (a, b)
  let v : ℝ × ℝ := (p, q)
  let norm_sq (w : ℝ × ℝ) := w.1^2 + w.2^2
  let dot (w z : ℝ × ℝ) := w.1 * z.1 + w.2 * z.2
  let cross_mag (w z : ℝ × ℝ) := |w.1 * z.2 - w.2 * z.1|
  norm_sq u * norm_sq v = (dot u v)^2 + (cross_mag u v)^2 := by
  sorry

















theorem theorem_298314_problem (a b : Fin 3 → ℝ) :
  Matrix.dotProduct (crossProduct a b) (crossProduct a b) + (Matrix.dotProduct a b) ^ 2 =
  (Matrix.dotProduct a a) * (Matrix.dotProduct b b) := by
  sorry

theorem theorem_298461_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (e₁ e₂ : V)
  (h_ortho : inner e₁ e₂ = (0 : ℝ))
  (h_norm_e1 : inner e₁ e₁ = (1 : ℝ))
  (h_norm_e2 : inner e₂ e₂ = (1 : ℝ)) :
  inner (e₁ + e₂) ((-2 : ℝ) • e₁ + e₂) = (-1 : ℝ) := by
  sorry

theorem theorem_298348_problem (m n : ℕ) (hm : m ≤ n) (hn : n ≤ 10) (hm_pos : 0 < m) :
  let N : ℝ := ((m : ℝ) - 1) * ((n : ℝ) - 1)
  let target : ℝ := (Int.ceil ((N - 1) / 2) : ℝ)
  let f (A : Matrix (Fin m) (Fin n) ℕ) (i : Fin m) (j : Fin n) : ℝ :=
    ∑ k in Finset.univ.erase i, ∑ l in Finset.univ.erase j, (A k l : ℝ)
  (∃ A : Matrix (Fin m) (Fin n) ℕ,
    (∀ i j, A i j ∈ ({0, 1} : Set ℕ)) ∧
    (1 ≤ ∑ i, ∑ j, A i j) ∧
    (∑ i, ∑ j, A i j ≤ m * n - 1) ∧
    (∃ z : ℝ, z = target ∧
      (∀ i j, f A i j - z ≤ N * (A i j : ℝ)) ∧
      (∀ i j, (∑ k in Finset.univ.erase i, ∑ l in Finset.univ.erase j, (1 - (A k l : ℝ))) - z ≤ N * (1 - (A i j : ℝ))))) ∧
  (∀ (A : Matrix (Fin m) (Fin n) ℕ) (z : ℝ),
    (∀ i j, A i j ∈ ({0, 1} : Set ℕ)) →
    (1 ≤ ∑ i, ∑ j, A i j) →
    (∑ i, ∑ j, A i j ≤ m * n - 1) →
    (∀ i j, f A i j - z ≤ N * (A i j : ℝ)) →
    (∀ i j, (∑ k in Finset.univ.erase i, ∑ l in Finset.univ.erase j, (1 - (A k l : ℝ))) - z ≤ N * (1 - (A i j : ℝ))) →
    z ≥ target) := by
  sorry

theorem theorem_299094_problem
  {S : Type*} [AddCommGroup S] [Module ℝ S] [FiniteDimensional ℝ S]
  (K : S →ₗ[ℝ] S →ₗ[ℝ] ℝ)
  (h_neg_def : ∀ v : S, v ≠ 0 → K v v < 0)
  (v : S)
  (h_degenerate : ∀ w : S, K v w = 0) :
  v = 0 := by
  sorry

theorem theorem_299242_problem 
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (U : X →L[ℝ] X) 
  (hU : ∀ f : X, ‖U f‖ = ‖f‖) 
  (g : X) : 
  Filter.Tendsto (fun n : ℕ => ‖g - (U ^ n) g‖ / (n : ℝ)) Filter.atTop (nhds 0) := by
  sorry





theorem theorem_299119_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (h_inv : A.det ≠ 0)
  (hA : ∃ k : ℤ, A.det = k)
  (hAinv : ∃ k : ℤ, (A⁻¹).det = k) :
  A.det = 1 ∨ A.det = -1 := by
  sorry

theorem theorem_299052_problem (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n ≥ 1) :
  let U_n : Set (Matrix (Fin 2) (Fin 2) ℚ_[p]) :=
    { A | ∀ i j, ‖(A - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p])) i j‖ ≤ (p : ℝ) ^ (-n : ℤ) }
  let SL2_Zp : Set (Matrix (Fin 2) (Fin 2) ℚ_[p]) :=
    { A | (∀ i j, ‖A i j‖ ≤ 1) ∧ A.det = 1 }
  ¬ (U_n ⊆ SL2_Zp) := by
  sorry



theorem theorem_298973_problem {p q : ℕ} {R : Type*} [CommRing R]
  (A : Matrix (Fin p) (Fin q) R) (B : Matrix (Fin q) (Fin p) R) :
  Matrix.trace (A * B) = Matrix.trace (B * A) := by
  sorry







theorem theorem_299984_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [Field K]
  (S_x S_y S_star Sigma : Matrix n n K)
  (h1 : S_star = S_x + S_y)
  (h2 : IsUnit Sigma.det) :
  Matrix.trace (S_x * Sigma⁻¹) + Matrix.trace (S_y * Sigma⁻¹) = Matrix.trace (S_star * Sigma⁻¹) := by
  sorry

