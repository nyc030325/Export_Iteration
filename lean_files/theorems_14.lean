import Mathlib
import Mathlib.Tactic



theorem theorem_68939_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  (A B : V →L[𝕜] V) :
  ‖A.comp B‖ ≤ ‖A‖ * ‖B‖ := by
  sorry



theorem theorem_69044_problem
  (σ_Y2 σ_error2 σ_hat_Y2 R2 : ℝ)
  (h_val : σ_Y2 = 1)
  (h_decomp : σ_Y2 = σ_hat_Y2 + σ_error2)
  (h_R2 : R2 = σ_hat_Y2 / σ_Y2) :
  σ_error2 = σ_Y2 * (1 - R2) := by
  sorry

theorem theorem_69002_problem (f : ℕ → ℝ → ℝ)
  (h : ∀ n x, f n x = x ^ n * (1 - x)) :
  TendstoUniformlyOn f 0 atTop (Set.Icc 0 1) := by
  sorry



theorem theorem_69477_problem
  (n : ℕ)
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA_symm : A.IsSymm)
  (hA_pos : A.PosDef)
  (hB_symm : B.IsSymm)
  (hB_pos : B.PosDef) :
  (A + B).det = A.det * B.det * (A⁻¹ + B⁻¹).det := by
  sorry

theorem theorem_69039_problem (f : ℕ → ℝ → ℝ)
  (h : ∀ x, 0 < x → x ≤ 1 → ∃ m, ∀ n ≥ m, f n x = 0) :
  ∀ x, 0 < x → x ≤ 1 → Filter.Tendsto (fun n ↦ f n x) Filter.atTop (nhds 0) := by
  sorry









theorem theorem_69171_problem
  {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (F : V →ₗ[ℝ] W)
  (h : ∃ C : ℝ, C > 0 ∧ ∀ f : V, ‖F f‖ ≤ C * ‖f‖) :
  Continuous F := by
  sorry

theorem theorem_69503_problem
  (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x x_ast : EuclideanSpace ℝ (Fin n))
  (h_diff : Differentiable ℝ f) :
  f x = f x_ast + ∫ t in (0 : ℝ)..1, inner (gradient f (x_ast + t • (x - x_ast))) (x - x_ast) := by
  sorry















theorem theorem_69694_problem
  (m : ℕ)
  (hm : m > 0)
  (p : Fin m → (Fin 2 → ℝ))
  (L2 : Set (Fin 2 → ℝ))
  (S : Fin m → Set (Matrix (Fin 2) (Fin 2) ℝ))
  (hS : ∀ n, S n = { M | M.mulVec (p n) ∈ L2 }) :
  (∃ M : Matrix (Fin 2) (Fin 2) ℝ, Set.image (fun v ↦ M.mulVec v) (Set.range p) = L2) ↔
  (⋂ n, S n).Nonempty := by
  sorry

theorem theorem_70146_problem
  (G : Type*) [Group G] [Fintype G] [DecidableEq G]
  (N : ℕ) (hN : Fintype.card G = N)
  (g_seq : Fin N ≃ G)
  (R : G → Matrix (Fin N) (Fin N) ℂ)
  (hR : ∀ (g : G) (i j : Fin N), R g i j = if g_seq i * (g_seq j)⁻¹ = g then 1 else 0) :
  ∀ (g_m g_n : G), R g_m * R g_n = R (g_m * g_n) := by
  sorry





theorem theorem_70703_problem
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (β : ℝ)
  (hβ : 0 < β) :
  Matrix.PosDef (A.transpose * A + β • (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
  IsUnit (A.transpose * A + β • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  sorry

theorem theorem_70503_problem (R D : Matrix (Fin 2) (Fin 2) (ZMod 4))
  (hR : IsUnit R.det)
  (hD : ∀ i j, i ≠ j → D i j = 0) :
  !![0, 1; 1, 0] ≠ R * D * R⁻¹ := by
  sorry







theorem theorem_70480_problem
  (a₁ a₂ : ℝ → ℝ → ℝ → ℝ → ℝ)
  (x₁ x₂ v₁ v₂ : ℝ → ℝ)
  (h₁ : deriv (deriv x₁) = fun t ↦ a₁ (x₁ t) (x₂ t) (deriv x₁ t) (deriv x₂ t))
  (h₂ : deriv (deriv x₂) = fun t ↦ a₂ (x₁ t) (x₂ t) (deriv x₁ t) (deriv x₂ t))
  (hv₁ : v₁ = deriv x₁)
  (hv₂ : v₂ = deriv x₂) :
  deriv (fun t ↦ ![x₁ t, x₂ t, v₁ t, v₂ t]) =
  fun t ↦ ![v₁ t, v₂ t, a₁ (x₁ t) (x₂ t) (v₁ t) (v₂ t), a₂ (x₁ t) (x₂ t) (v₁ t) (v₂ t)] := by
  sorry









theorem theorem_71420_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
  (h : ∀ k : ℕ, Odd k → (A.charpoly.roots.map (fun x => x ^ k)).sum = 0) :
  A.charpoly.roots = A.charpoly.roots.map Neg.neg := by
  sorry





theorem theorem_70899_problem {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) :
  A.det = ∑ i : Fin n.succ, (-1 : R) ^ (i : ℕ) * A 0 i * (A.submatrix (Fin.succAbove 0) (Fin.succAbove i)).det := by
  sorry









theorem theorem_71624_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (h : ∃ v : Fin n → (Fin n → ℝ),
    (∀ i j, Matrix.dotProduct (v i) (v j) = if i = j then 1 else 0) ∧
    (∀ i, ∃ c : ℝ, Matrix.mulVec A (v i) = c • (v i))) :
  A = A.transpose := by
  sorry





theorem theorem_72059_problem
  (a b c d e f : ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hd : d > 0) (he : e > 0) (hf : f > 0)
  (h_pyth1 : a^2 + b^2 = c^2)
  (h_pyth2 : d^2 + e^2 = f^2) :
  let A : ℂ := -a
  let B : ℂ := a
  let C : ℂ := b * Complex.I
  let z : ℂ := d + e * Complex.I
  let A' := A * z
  let B' := B * z
  let C' := C * z
  let is_horizontal (p q : ℂ) := p.im = q.im
  let is_vertical (p q : ℂ) := p.re = q.re
  let has_hv_side :=
    (is_horizontal A' B' ∨ is_vertical A' B') ∨
    (is_horizontal B' C' ∨ is_vertical B' C') ∨
    (is_horizontal C' A' ∨ is_vertical C' A')
  has_hv_side ↔ (a / b = d / e ∨ a / b = e / d) := by
  sorry









theorem theorem_71834_problem
  (N : ℕ)
  (u_norm_s : Fin N → ℝ)
  (err_norm_q : Fin N → ℝ)
  (Ci : Fin N → ℝ)
  (s q k h : ℝ)
  (h_pos : 0 < h)
  (hs : 1 ≤ s)
  (hq : 1 ≤ q)
  (hu_nonneg : ∀ i, 0 ≤ u_norm_s i)
  (herr_nonneg : ∀ i, 0 ≤ err_norm_q i)
  (h_local_err : ∀ i, err_norm_q i ≤ Ci i * h ^ (min (k + 1) s - q) * u_norm_s i)
  (C : ℝ)
  (hC : C = Real.sqrt (sSup (Set.range (λ i => (Ci i)^2))))
  (vec_u_norm : ℝ)
  (h_vec_u : vec_u_norm = Real.sqrt (∑ i, (u_norm_s i)^2))
  (vec_err_norm : ℝ)
  (h_vec_err : vec_err_norm = Real.sqrt (∑ i, (err_norm_q i)^2)) :
  vec_err_norm ≤ C * h ^ (min (k + 1) s - q) * vec_u_norm := by
  sorry







theorem theorem_72156_problem (n : ℕ) (β : Fin n → ℝ) :
  spectralRadius ℝ (Matrix.diagonal β) = Finset.sup Finset.univ (fun i ↦ ENNReal.ofReal (|β i|)) := by
  sorry





theorem theorem_72568_problem 
  {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (g : V →ₗ[K] W)
  (F S D E : Submodule K V)
  (h1 : LinearMap.ker g ≤ F ⊓ S)
  (h2 : F ⊓ S ≤ D ⊓ S)
  (h3 : D ⊓ S ≤ E)
  (h4 : E ⊓ F = ⊥) :
  F ⊓ S = ⊥ := by
  sorry

theorem theorem_72088_problem
  (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : A.IsSymm)
  (π : Equiv.Perm (Fin n))
  (h_unique : ∀ σ : Equiv.Perm (Fin n), σ ≠ π → ∑ i : Fin n, A i (π i) < ∑ i : Fin n, A i (σ i)) :
  π = π⁻¹ := by
  sorry







theorem theorem_72355_problem {R : Type*} [CommRing R]
  (A₁ A₂ A₃ A₄ : Matrix (Fin 3) (Fin 3) R) :
  let T : Matrix (Fin 3) (Fin 3) R → Matrix (Fin 3) (Fin 3) R := fun A ↦ (3 : R) • A
  let M := Matrix.fromBlocks A₁ A₂ A₃ A₄
  let M' := Matrix.fromBlocks (T A₁) (T A₂) (T A₃) (T A₄)
  M' = (3 : R) • M := by
  sorry

theorem theorem_72596_problem
  {n : Type*} [DecidableEq n] [Fintype n]
  {R : Type*} [CommRing R]
  (H S : Matrix n n R)
  (hH : IsUnit H) :
  H * S = H ↔ S = 1 := by
  sorry





theorem theorem_72987_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {n m : ℕ}
  (v : Basis (Fin n) K V)
  (w : Basis (Fin m) K W)
  (T : V →ₗ[K] W) :
  let f := v.dualBasis
  let g := w.dualBasis
  let M := LinearMap.toMatrix g f (LinearMap.dualMap T)
  ∀ (i : Fin n) (j : Fin m), M i j = g j (T (v i)) := by
  sorry



theorem theorem_73237_problem {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
  (P : Matrix n n R) (h : P.transpose = P.transpose * P) :
  P = P.transpose := by
  sorry







theorem theorem_73318_problem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (T : V →ₗ[K] V) (h : T ^ 2 = 1) :
  LinearMap.det T = 1 ∨ LinearMap.det T = -1 := by
  sorry

theorem theorem_73090_problem
  {V : Type*} [AddCommGroup V] [Module ℚ V]
  (S : Set V)
  (rowsA : Set V)
  (h_rows : rowsA ⊆ S)
  (h_no_zero : (0 : V) ∉ rowsA)
  (h_gen : ∀ e ∈ S, e ∈ Submodule.span ℚ rowsA) :
  S = Submodule.span ℚ rowsA := by
  sorry









theorem theorem_74699_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  (φ : (H →L[ℂ] H) →ₗ[ℂ] F)
  (c : ℝ)
  (h : ∀ (A : H →L[ℂ] H), IsSelfAdjoint A → ‖φ A‖ ≤ c * ‖A‖) :
  ∀ (A : H →L[ℂ] H), ‖φ A‖ ≤ 2 * c * ‖A‖ := by
  sorry















theorem theorem_73781_problem (n : ℕ) (K : Type*) [Field K] :
  Subgroup.center (Matrix.GeneralLinearGroup (Fin n) K) =
  MonoidHom.range (Units.map (algebraMap K (Matrix (Fin n) (Fin n) K)).toMonoidHom) := by
  sorry





theorem theorem_74248_problem
  (n m : ℕ)
  (P : Matrix (Fin n) (Fin n) ℝ)
  (R : Matrix (Fin m) (Fin m) ℝ)
  (H : Matrix (Fin m) (Fin n) ℝ)
  (hP : P.PosSemidef)
  (hR : R.PosDef)
  (S : Matrix (Fin m) (Fin m) ℝ)
  (hS : S = H * P * H.transpose + R) :
  S.PosDef := by
  sorry

theorem theorem_74379_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  {n : Type*} [Fintype n] [DecidableEq n]
  (B B' : Basis n K V)
  (T : V →ₗ[K] V)
  (TB TB' P : Matrix n n K)
  (hTB : TB = LinearMap.toMatrix B B T)
  (hTB' : TB' = LinearMap.toMatrix B' B' T)
  (hP : ∀ v : V, B'.repr v = P.mulVec (B.repr v)) :
  TB' = P * TB * P⁻¹ := by
  sorry





theorem theorem_74365_problem (g : ℂ → ℂ)
  (h_holo : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1))
  (h_bound : ∀ z ∈ Metric.ball (0 : ℂ) 1, Complex.abs (g z) ≤ 1)
  (h_exists : ∃ z₀ ∈ Metric.ball (0 : ℂ) 1, Complex.abs (g z₀) = 1) :
  ∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1, g x = g y := by
  sorry



theorem theorem_74500_problem
  (f : ℝ → ℝ)
  (hf_diff : Differentiable ℝ f)
  (hf_symm : ∀ x, f x = f (-x))
  (A : ℝ → ℝ → ℂ)
  (hA : ∀ m n, A m n = ↑(deriv (fun t => f (m - t)) n)) :
  ∀ m n, star (A n m) = - A m n := by
  sorry

theorem theorem_74853_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  (V : Set X)
  (hV : Dense V) :
  closure (Submodule.span 𝕜 V : Set X) = Set.univ := by
  sorry



theorem theorem_74461_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (I S : Set V)
  (h_ind : LinearIndependent F ((↑) : I → V))
  (h_span : Submodule.span F S = ⊤)
  (h_sub : I ⊆ S) :
  ∃ M : Set V, I ⊆ M ∧ M ⊆ S ∧ LinearIndependent F ((↑) : M → V) ∧ Submodule.span F M = ⊤ := by
  sorry

