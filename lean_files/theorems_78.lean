import Mathlib
import Mathlib.Tactic



theorem theorem_420985_problem
  (x y : Fin 6 → ℝ)
  (h_distinct : Function.Injective (fun i => (x i, y i))) :
  (∃ a b c d e f : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0 ∨ f ≠ 0) ∧
    ∀ i, a * (x i)^2 + b * (x i) * (y i) + c * (y i)^2 + d * (x i) + e * (y i) + f = 0) ↔
  Matrix.det (Matrix.of (fun i j : Fin 6 =>
    if i = 0 then 1
    else if i = 1 then x j
    else if i = 2 then y j
    else if i = 3 then (x j)^2
    else if i = 4 then (x j) * (y j)
    else (y j)^2)) = 0 := by
  sorry









theorem theorem_421434_problem
  {𝕜 E : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]
  (M : E →L[𝕜] E)
  (β : 𝕜)
  (h_eig : Module.End.HasEigenvalue (M : E →ₗ[𝕜] E) β)
  (h_val : 1 < ‖β‖) :
  ¬ Bornology.IsBounded (Set.range (fun n : ℕ => M ^ n)) := by
  sorry



theorem theorem_421334_problem
  {E : Type*} [AddCommGroup E] [Module ℝ E]
  (X : Submodule ℝ E)
  (u : E) (hu : u ∈ X)
  (W : Set E) (hW : W = {w | ∃ x ∈ X, w = x - u}) :
  ∃ S : Submodule ℝ E, (S : Set E) = W := by
  sorry

theorem theorem_421620_problem (n : ℕ) :
  IsClosed { A : Matrix (Fin n) (Fin n) ℝ | ∃ p : ℕ, p > 0 ∧ A ^ p = 0 } := by
  sorry

theorem theorem_421507_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2) =
  Real.sqrt (∑ k : Fin (m * n), (A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) ^ 2) := by
  sorry

theorem theorem_421332_problem :
  ∃ x y z x' y' z' : ℕ → ℝ,
    (Summable (fun i => x i ^ 2)) ∧ (Summable (fun i => y i ^ 2)) ∧ (Summable (fun i => z i ^ 2)) ∧
    (Summable (fun i => x' i ^ 2)) ∧ (Summable (fun i => y' i ^ 2)) ∧ (Summable (fun i => z' i ^ 2)) ∧
    (Summable (fun i => x i * y i)) ∧ (Summable (fun i => x i * z i)) ∧ (Summable (fun i => y i * z i)) ∧
    (Summable (fun i => x' i * y' i)) ∧ (Summable (fun i => x' i * z' i)) ∧ (Summable (fun i => y' i * z' i)) ∧
    (Summable (fun i => x i * y i * z i)) ∧ (Summable (fun i => x' i * y' i * z' i)) ∧
    (∑' i, x i ^ 2 = ∑' i, x' i ^ 2) ∧
    (∑' i, y i ^ 2 = ∑' i, y' i ^ 2) ∧
    (∑' i, z i ^ 2 = ∑' i, z' i ^ 2) ∧
    (∑' i, x i * y i = ∑' i, x' i * y' i) ∧
    (∑' i, x i * z i = ∑' i, x' i * z' i) ∧
    (∑' i, y i * z i = ∑' i, y' i * z' i) ∧
    (∑' i, x i * y i * z i ≠ ∑' i, x' i * y' i * z' i) := by
  sorry

theorem theorem_421627_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (er et ep : E)
  (h_norm_er : ‖er‖ = 1)
  (h_norm_et : ‖et‖ = 1)
  (h_norm_ep : ‖ep‖ = 1)
  (h_orth_rt : inner er et = (0 : ℝ))
  (h_orth_rp : inner er ep = (0 : ℝ))
  (h_orth_tp : inner et ep = (0 : ℝ))
  (pr pt pp : ℝ)
  (p : E)
  (h_p_def : p = pr • er + pt • et + pp • ep)
  (h_p_nonzero : p ≠ 0) :
  Real.cos (InnerProductGeometry.angle p er) = pr / Real.sqrt (pr^2 + pt^2 + pp^2) := by
  sorry

theorem theorem_421550_problem
  {R : Type*} [CommRing R]
  {M N1 N2 N3 : Type*}
  [AddCommGroup M] [Module R M]
  [AddCommGroup N1] [Module R N1]
  [AddCommGroup N2] [Module R N2]
  [AddCommGroup N3] [Module R N3]
  (f1 : N1 →ₗ[R] N2) (f2 : N2 →ₗ[R] N3)
  (h_exact : Function.Exact f1 f2)
  (x : N2) (hx : f2 x = 0) :
  let Q := N2 ⧸ LinearMap.range f1
  let α : R →ₗ[R] Q := LinearMap.toSpanSingleton R Q ((LinearMap.range f1).mkQ x)
  ∀ (r : R) (m : M), (TensorProduct.map α (LinearMap.id : M →ₗ[R] M)) (r ⊗ₜ[R] m) = 0 := by
  sorry

theorem theorem_421580_problem
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (T : E →L[ℝ] F)
  {n : ℕ} (e : Basis (Fin n) ℝ E)
  (he : ∀ i, ‖e i‖ = 1) :
  ‖T‖ ≥ ⨆ i, ‖T (e i)‖ := by
  sorry











theorem theorem_422026_problem
  {K : Type*} [Field K]
  {n : ℕ}
  (f g : Fin n → K)
  (A : Matrix (Fin n) (Fin n) K)
  (hA : A = Matrix.vecMulVec f g)
  (k : ℕ)
  (hk : k > 0) :
  Matrix.trace (A ^ k) = (Matrix.dotProduct g f) ^ k := by
  sorry







theorem theorem_422493_problem (n : ℕ)
  (norm : Matrix (Fin n) (Fin n) ℂ → ℝ)
  (h_unitary_inv : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (U V : Matrix (Fin n) (Fin n) ℂ),
    U ∈ Matrix.unitaryGroup (Fin n) ℂ → V ∈ Matrix.unitaryGroup (Fin n) ℂ →
    norm (U * A * V) = norm A)
  (M : Matrix (Fin n) (Fin n) ℂ) :
  norm M = norm M.conjTranspose := by
  sorry





theorem theorem_422748_problem (a b c d : ℝ)
  (A : Matrix (Fin 2) (Fin 2) ℝ)
  (hA : A = !![a, b; c, d])
  (h_det : a * d - b * c ≠ 0) :
  A⁻¹ = (1 / (a * d - b * c)) • !![d, -b; -c, a] := by
  sorry











theorem theorem_423389_problem
  {d : Type*} [AddCommGroup d] [Module ℝ d]
  (n : ℕ) (hn : 0 < n)
  (v : Fin n → d)
  (v_bar : d)
  (h_v_bar : v_bar = (n : ℝ)⁻¹ • ∑ i, v i) :
  convexHull ℝ (Set.range v) ⊆
  {x | ∃ u ∈ Submodule.span ℝ {w | ∃ i : Fin n, (i : ℕ) < n - 1 ∧ w = v i - v_bar}, x = v_bar + u} := by
  sorry

theorem theorem_422904_problem
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix m m ℂ) (B : Matrix n n ℂ) (C : Matrix m n ℂ) :
  (∃! X : Matrix m n ℂ, A * X - X * B = C) ↔ (spectrum ℂ A ∩ spectrum ℂ B = ∅) := by
  sorry







theorem theorem_423290_problem (a b c : ℚ) 
  (h : (a : ℝ) * Real.pi ^ 2 + (b : ℝ) * Real.pi + (c : ℝ) = 0) : 
  a = 0 ∧ b = 0 ∧ c = 0 := by
  sorry

theorem theorem_423518_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) :
  let valid_rows := Finset.filter (fun p : Fin m × Fin m => p.1 ≤ p.2) Finset.univ
  let valid_cols := Finset.filter (fun p : Fin n × Fin n => p.1 ≤ p.2) Finset.univ
  let submatrix_sums := (valid_rows.product valid_cols).image 
    (fun x => ∑ r in Finset.Icc x.1.1 x.1.2, ∑ c in Finset.Icc x.2.1 x.2.2, A r c)
  let algo_sums := valid_rows.biUnion 
    (fun rp => 
      let B := fun k => ∑ r in Finset.Icc rp.1 rp.2, A r k
      valid_cols.image (fun cp => ∑ k in Finset.Icc cp.1 cp.2, B k))
  submatrix_sums.max = algo_sums.max := by
  sorry



theorem theorem_423929_problem (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) (i j r : Fin n) :
  deriv (fun x => (Matrix.adjugate (Function.update X i (Function.update (X i) r x))) j i) (X i r) = 0 := by
  sorry









theorem theorem_423846_problem (n d k : ℕ)
  (X : Matrix (Fin n) (Fin d) ℝ)
  (W : Matrix (Fin d) (Fin k) ℝ)
  (T : Matrix (Fin n) (Fin k) ℝ)
  (E : Matrix (Fin n) (Fin k) ℝ)
  (hE : E = X * W - T) :
  (1 / 2 : ℝ) * Matrix.trace (E.transpose * E) = (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin k, (E i j) ^ 2 := by
  sorry

theorem theorem_424521_problem
  (n : ℕ)
  (S : Matrix (Fin n) (Fin n) ℝ)
  (x : Fin n → ℝ)
  (hS : Invertible S)
  (hS_add : Invertible (S + Matrix.vecMulVec x x)) :
  Matrix.dotProduct x (Matrix.mulVec (S + Matrix.vecMulVec x x)⁻¹ x) =
  1 - S.det / (S + Matrix.vecMulVec x x).det := by
  sorry











theorem theorem_424160_problem
  (n : ℕ)
  (p : Fin n → ℝ × ℝ)
  (w : Fin n → ℝ)
  (hw : ∀ i, 0 < w i)
  (a b c1 c2 : ℝ)
  (hab : a^2 + b^2 = 1) :
  let distance (i : Fin n) (c : ℝ) := |a * (p i).1 + b * (p i).2 + c|
  let cost (S : Finset (Fin n)) :=
    (∑ i in S, w i * distance i c1) + (∑ i in (Finset.univ \ S), w i * distance i c2)
  let min_dist_sum := ∑ i : Fin n, w i * min (distance i c1) (distance i c2)
  (∀ S : Finset (Fin n), min_dist_sum ≤ cost S) ∧
  (∃ S : Finset (Fin n), cost S = min_dist_sum) := by
  sorry









theorem theorem_424467_problem
  {ι : Type*}
  {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)]
  (F : Set (PiLp 2 E))
  (h : ∀ (x : PiLp 2 E), Set.Finite {i | x i ≠ 0} → x ∈ F) :
  ∀ x : PiLp 2 E, x ∈ closure F := by
  sorry

theorem theorem_424856_problem
  (m n p : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (B : Matrix (Fin n) (Fin p) ℝ)
  (T : Fin m → Fin n → Fin n → Fin p → ℝ)
  (hT : ∀ (i : Fin m) (j : Fin n) (k : Fin n) (l : Fin p), T i j k l = A i j * B k l) :
  ∀ (i : Fin m) (l : Fin p), (A * B) i l = ∑ j : Fin n, T i j j l := by
  sorry







theorem theorem_424698_problem
  (X : Type*) [MetricSpace X] [CompactSpace X]
  (F : ℕ → X → ℝ)
  (h_equicont : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ n : ℕ, ∀ x y : X, dist x y < δ → |F n x - F n y| < ε)
  (h_bounded : ∀ x : X, ∃ M : ℝ, ∀ n : ℕ, |F n x| ≤ M) :
  ∃ (φ : ℕ → ℕ) (f : X → ℝ), StrictMono φ ∧ Continuous f ∧
  TendstoUniformly (fun k => F (φ k)) f Filter.atTop := by
  sorry



theorem theorem_425167_problem
  (F : Type*) [Field F] (V : Type*) [AddCommGroup V] [Module F V]
  (h_char : ringChar F ≠ 2)
  (g : V →ₗ[F] V →ₗ[F] F)
  (h_symm : ∀ x y, g x y = g y x)
  (Q : V → F)
  (h_Q_def : ∀ x, Q x = g x x)
  (L : V →ₗ[F] V)
  (h_L_Q : ∀ x, Q (L x) = Q x) :
  ∀ x y, g (L x) (L y) = g x y := by
  sorry



theorem theorem_424805_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (n : ℕ) [NeZero n]
  (Y : E)
  (X : Fin n → E)
  (hX : ∀ i, X i = Y) :
  sSup {v | ∃ (u : EuclideanSpace ℝ (Fin n)), ‖u‖ = 1 ∧ v = ‖∑ i, u i • X i‖} ≥
  Real.sqrt n * sSup (Set.range (fun i => ‖X i‖)) := by
  sorry

theorem theorem_425098_problem {K : Type*} [Field K] (i j : ℕ) :
  (Polynomial.derivative ((Polynomial.X : Polynomial K) ^ j)).coeff i =
  if i = j - 1 then (j : K) else 0 := by
  sorry



theorem theorem_424973_problem (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (B : Matrix (Fin n) (Fin n) ℝ)
  (J : Matrix (Fin m) (Fin n) ℝ)
  (hB : Invertible B)
  (hJ : J * B = A) :
  ∀ (i : Fin m) (j : Fin n), Matrix.dotProduct (J i) (fun k => B k j) = A i j := by
  sorry





theorem theorem_425439_problem
  (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
  (n : ℕ)
  (v w : Basis (Fin n) K V)
  (T : V →ₗ[K] V)
  (Tv Tw P : Matrix (Fin n) (Fin n) K)
  (hTv : Tv = LinearMap.toMatrix v v T)
  (hTw : Tw = LinearMap.toMatrix w w T)
  (hP : P = v.toMatrix w) :
  Tw = P⁻¹ * Tv * P := by
  sorry













theorem theorem_426288_problem (n m : ℕ)
  (f : Fin m → (Fin n → ℝ) → ℝ)
  (hf : ∀ i, ContDiff ℝ 2 (f i))
  (H : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
  (hH : ∀ x, H x = ∑ i : Fin m, (f i x) • Matrix.of (fun j k => iteratedFDeriv ℝ 2 (f i) x ![Pi.single j 1, Pi.single k 1])) :
  ∀ x, (H x).IsSymm := by
  sorry





theorem theorem_426291_problem
  {α : Type*} [TopologicalSpace α]
  (f : α → ℝ)
  (L : Set α)
  (h_nonempty : L.Nonempty)
  (h_compact : IsCompact L)
  (h_cont : ContinuousOn f L) :
  ∃ x ∈ L, ∀ y ∈ L, f x ≤ f y := by
  sorry





theorem theorem_426447_problem
  (V : Type*) [AddCommGroup V] [Module ℂ V]
  (inner : V → V → ℂ)
  (h_add : ∀ (f g₁ g₂ : V), inner f (g₁ + g₂) = inner f g₁ + inner f g₂)
  (h_hom : ∀ (f g : V) (s : ℂ), inner f (s • g) = star s * inner f g)
  (s : ℂ) (hs : s ≠ 0)
  (f g₁ g₂ : V) (hf : f ≠ 0) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) :
  inner f (s • g₁ + g₂) = (star s) * inner f g₁ + inner f g₂ := by
  sorry











theorem theorem_427209_problem (T : (ℕ → ℂ) → (ℕ → ℂ))
  (hT : ∀ a : ℕ → ℂ, T a = fun n => if n = 0 then 0 else a (n - 1)) :
  ¬ ∃ (c : ℂ) (v : ℕ → ℂ), v ≠ 0 ∧ T v = c • v := by
  sorry

theorem theorem_426648_problem (k : Float) (as cs : List Float)
  (h_k : k > 15.0)
  (h_len : as.length = cs.length)
  (h_mag : ∀ (a c : Float), (a, c) ∈ List.zip as cs → c.abs * ((10.0 : Float) ^ k) ≤ a.abs) :
  (List.zipWith (fun x y => x + y) as cs).foldl (fun acc x => acc + x) 0.0 =
  as.foldl (fun acc x => acc + x) 0.0 := by
  sorry



theorem theorem_427364_problem (F : Type*) [Field F] (V : Type*) [AddCommGroup V] [Module F V] :
  FaithfulSMul (Module.End F V) V := by
  sorry





theorem theorem_427337_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [Field R]
  (C D : Matrix n n R)
  (hC : IsUnit C.det) :
  ∑ k, ∑ l, (∑ i, (C⁻¹) l i * C i k) * D k l = ∑ k, ∑ l, D k l * (if l = k then 1 else 0) := by
  sorry



