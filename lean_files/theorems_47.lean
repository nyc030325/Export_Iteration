import Mathlib
import Mathlib.Tactic





theorem theorem_252097_problem (q r₁ : ℚ) :
  let S := {p : ℚ × ℚ | ∃ q₁ : ℚ, p.1 = q - q₁ ∧ p.2 = r₁ - q₁}
  S = Set.range (fun q₁ ↦ (q - q₁, r₁ - q₁)) ∧ Set.Infinite S := by
  sorry





theorem theorem_252199_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (n : ℕ) (x : Fin n → E) :
  let x_bar := (n : ℝ)⁻¹ • ∑ i, x i
  ∑ i, ∑ j, (if i ≠ j then ‖x i - x j‖^2 else 0) =
  2 * (n : ℝ) * ∑ i, ‖x i - x_bar‖^2 := by
  sorry





theorem theorem_253066_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (x : ℕ → X)
  (h_conv : ∃ L, Filter.Tendsto x Filter.atTop (nhds L)) :
  ∃ M > 0, ∀ n, ‖x n‖ ≤ M := by
  sorry

theorem theorem_252653_problem
  (a b c d : ℝ → ℂ)
  (z : ℂ)
  (ha : DifferentiableAt ℝ a 0)
  (hb : DifferentiableAt ℝ b 0)
  (hc : DifferentiableAt ℝ c 0)
  (hd : DifferentiableAt ℝ d 0)
  (h_sl2 : ∀ t, a t * d t - b t * c t = 1)
  (ha0 : a 0 = 1)
  (hb0 : b 0 = 0)
  (hc0 : c 0 = 0)
  (hd0 : d 0 = 1) :
  deriv (fun t ↦ (a t * z + b t) / (c t * z + d t)) 0 =
  - (deriv c 0) * z ^ 2 + (deriv a 0 - deriv d 0) * z + deriv b 0 := by
  sorry













theorem theorem_252409_problem (n : ℕ) (a b : ℕ → ℂ) :
  Complex.abs (∑ i in Finset.range n, a i * b i) ^ 2 =
  (∑ i in Finset.range n, Complex.abs (a i) ^ 2) * (∑ i in Finset.range n, Complex.abs (b i) ^ 2) -
  ∑ i in Finset.range n, ∑ j in Finset.range n,
    if i < j then Complex.abs (a i * star (b j) - a j * star (b i)) ^ 2 else 0 := by
  sorry







theorem theorem_253326_problem (F1 F2 V : Type*)
  [Field F1] [Field F2] [AddCommGroup V]
  [Algebra F2 F1]
  [Module F1 V]
  [Module F2 V] [IsScalarTower F2 F1 V]
  (h : FiniteDimensional F1 V) :
  FiniteDimensional.finrank F2 V = FiniteDimensional.finrank F2 F1 * FiniteDimensional.finrank F1 V := by
  sorry

theorem theorem_253336_problem
  (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (f : ℝ → (Fin n → ℝ))
  (a b : ℝ)
  (hf : IntervalIntegrable f volume a b) :
  Matrix.mulVec A (∫ x in a..b, f x) = ∫ x in a..b, Matrix.mulVec A (f x) := by
  sorry



theorem theorem_253752_problem (n : ℕ) (A H : Matrix (Fin n) (Fin n) ℝ)
  (hA : IsUnit A.det) :
  deriv (fun t : ℝ => (A + t • H).det) 0 = A.det * (A⁻¹ * H).trace := by
  sorry





theorem theorem_253646_problem {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
  (A : Matrix n n K) (h : A ^ 2 = A) :
  LinearMap.range (Matrix.toLin' (A - 1)) = LinearMap.ker (Matrix.toLin' A) := by
  sorry







theorem theorem_254158_problem (m n : ℕ) (hm : 0 < m) (hmn : m < n) :
  ∃ φ : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ),
    (∀ (x : Fin m → ℝ) (i : Fin n), φ x i = if h : (i : ℕ) < m then x ⟨i, h⟩ else 0) ∧
    Function.Injective φ ∧
    ∀ y : Fin n → ℝ, y ∈ LinearMap.range φ ↔ ∀ i : Fin n, m ≤ (i : ℕ) → y i = 0 := by
  sorry









theorem theorem_254067_problem
  (r : ℝ → EuclideanSpace ℝ (Fin 3))
  (f : EuclideanSpace ℝ (Fin 3) → ℝ)
  (s : ℝ)
  (hr : DifferentiableAt ℝ r s)
  (hf : DifferentiableAt ℝ f (r s)) :
  deriv (f ∘ r) s = inner (gradient f (r s)) (deriv r s) := by
  sorry

theorem theorem_254500_problem
  (m n k : ℕ)
  (hm : m > 0) (hn : n > 0) (hk : k > 0)
  (A : Matrix (Fin m) (Fin n) ℝ) :
  let L : Matrix (Fin m) (Fin k) ℝ × Matrix (Fin k) (Fin n) ℝ → ℝ :=
    fun ⟨X, Y⟩ => ∑ i, ∑ j, (A i j - (X * Y) i j) ^ 2
  ¬ ConvexOn ℝ Set.univ L := by
  sorry



theorem theorem_254747_problem
  (R : Type*) [CommRing R] [IsDomain R]
  (m n : ℕ) (h_nm : m < n)
  (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (e : Basis (Fin m) R M)
  (f : Basis (Fin n) R N)
  (φ : M →ₗ[R] N →ₗ[R] R) :
  ∃ x : N, x ≠ 0 ∧ ∀ (i : Fin m), φ (e i) x = 0 := by
  sorry













theorem theorem_254683_problem
  {X : Type*} [MetricSpace X]
  (f : ℕ → X → ℝ)
  (h : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x y : X, |f n x - f n y| < ε) :
  ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ x y : X, dist x y < δ → |f n x - f n y| < ε := by
  sorry







theorem theorem_255105_problem (f : ℂ → ℂ) (z₀ : ℂ)
  (h : ∃ s, IsOpen s ∧ z₀ ∈ s ∧ DifferentiableOn ℂ f s) :
  AnalyticAt ℂ f z₀ := by
  sorry



theorem theorem_255076_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (n : ℕ)
  (h_dim : FiniteDimensional.finrank F V = n)
  (S : Fin n → V)
  (h_lc : ∃ k : Fin n, S k ∈ Submodule.span F (S '' {i : Fin n | i ≠ k})) :
  FiniteDimensional.finrank F (Submodule.span F (Set.range S)) < n := by
  sorry



theorem theorem_255229_problem (z : ℂ) (c d : ℝ)
  (hc : c ≠ 0) (hz : 1 ≤ Complex.abs z) :
  Complex.abs ((c : ℂ) * z + (d : ℂ)) ^ 2 ≥ c ^ 2 + 2 * c * d * z.re + d ^ 2 := by
  sorry





theorem theorem_255690_problem (n : ℕ) (A : ℕ → Type*)
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℝ (A i)]
  [∀ i, FiniteDimensional ℝ (A i)]
  (h_base : A 0 ≃ₗ[ℝ] ℝ)
  (h_step : ∀ i, A (i + 1) ≃ₗ[ℝ] A i × A i) :
  FiniteDimensional.finrank ℝ (A n) = 2 ^ n := by
  sorry







theorem theorem_255889_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (X : Matrix n n ℝ)
  (A : Matrix n n ℝ)
  (hA : A = 1 + X)
  (h_pd : ((1 : Matrix n n ℝ) - X.transpose * X).PosDef) :
  IsUnit A := by
  sorry



theorem theorem_255515_problem :
  Nonempty (AddAut (ZMod 3 × ZMod 3) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) := by
  sorry

theorem theorem_255796_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (n : ℕ)
  (v : Fin n → E)
  (c : ℝ)
  (h : ∀ (i : Fin n) (a : ℝ), c * |a| ≤ ‖a • v i‖) :
  ∀ i : Fin n, c ≤ ‖v i‖ := by
  sorry



theorem theorem_255960_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
  (h : ∃ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P ∧ B = P⁻¹ * A * P) :
  A.charpoly = B.charpoly := by
  sorry





theorem theorem_256130_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA_symm : A.IsSymm) (hB_symm : B.IsSymm)
  (hA_pos : A.PosDef) (hB_pos : B.PosDef) :
  (A + B).PosDef := by
  sorry



theorem theorem_256273_problem
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (h_dim : ¬ Module.Finite ℝ X)
  (r : ℝ) (hr : r > 0)
  (S : Set X) (hS : S = {x : X | ‖x‖ = r}) :
  ¬ IsCompact S := by
  sorry





theorem theorem_255703_problem
  (x y : Fin 3 → ℝ)
  (v : ℝ)
  (ρ : ℝ → ℝ → ℝ) :
  ∃ z : Fin 3 → ℝ, ∀ i : Fin 3,
    z i ∈ ({x i, y i} : Set ℝ) ∧
    ρ (z i) v = max (ρ (x i) v) (ρ (y i) v) := by
  sorry





theorem theorem_256349_problem
  (N : ℕ)
  (R : Type*) [Field R]
  (K : R)
  (ones : Fin N → R)
  (I_N : Matrix (Fin N) (Fin N) R)
  (Y : Matrix (Fin N) (Fin N) R)
  (g : Fin N → R)
  (h_ones : ones = fun _ ↦ 1)
  (h_I : I_N = 1)
  (h_Y : Y = I_N - K • Matrix.vecMulVec ones ones)
  (h_g : Matrix.dotProduct ones g = 0) :
  Matrix.mulVec Y g = g := by
  sorry



theorem theorem_256077_problem
  {K V n : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype n] [DecidableEq n]
  (bV : Basis n K V)
  (bW : Basis n K V)
  (T : V →ₗ[K] V)
  (C B A : Matrix n n K)
  (hC : C = LinearMap.toMatrix bW bV LinearMap.id)
  (hB : B = LinearMap.toMatrix bW bW T)
  (hA : A = LinearMap.toMatrix bV bV T) :
  A = C * B * C⁻¹ := by
  sorry

theorem theorem_256064_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (V : Matrix n n ℝ) (s : n → ℝ) (l i j : n) :
  HasDerivAt (fun x => ∑ m, (Matrix.updateRow V i (Function.update (V i) j x)) l m * s m)
    (∑ m, (if i = l then (1 : ℝ) else 0) * (if j = m then (1 : ℝ) else 0) * s m) (V i j) := by
  sorry



theorem theorem_256103_problem
  (n : ℕ)
  (v v' : Matrix (Fin n) (Fin n) ℝ)
  (k : Fin n)
  (h_base : ∀ i, i ≠ k → v' i = v i)
  (h_shear : ∃ c : Fin n → ℝ, v' k = v k + ∑ i in Finset.univ.erase k, c i • v i) :
  |v'.det| = |v.det| := by
  sorry

theorem theorem_256572_problem
  (n p : ℕ)
  (X : Matrix (Fin n) (Fin (p + 1)) ℝ)
  (x : Matrix (Fin 1) (Fin (p + 1)) ℝ)
  (σ : ℝ)
  (h_inv : Invertible (X.transpose * X))
  (X_new : Matrix (Fin (n + 1)) (Fin (p + 1)) ℝ)
  (h_def : X_new = Matrix.of (Fin.snoc X (x 0))) :
  ∀ i, (X_new.transpose * X_new)⁻¹ i i ≤ (X.transpose * X)⁻¹ i i := by
  sorry

theorem theorem_256562_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (P : Matrix n n ℝ)
  (h_nonneg : ∀ i j, 0 ≤ P i j)
  (h_stochastic : ∀ i, ∑ j, P i j = 1)
  (h_irreducible : ∀ i j, ∃ k : ℕ, 0 < (P ^ k) i j)
  (h_eigenvalue : ∀ (z : ℂ), (P.map (algebraMap ℝ ℂ)).charpoly.eval z = 0 → Complex.abs z = 1 → z = 1) :
  ∃ k : ℕ, 0 < k ∧ ∀ i j, 0 < (P ^ k) i j := by
  sorry





theorem theorem_256313_problem
  {F V : Type*} [NormedField F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (N₁ N₂ : V → ℝ)
  (hN₁_nonneg : ∀ x, 0 ≤ N₁ x)
  (hN₁_eq_zero_iff : ∀ x, N₁ x = 0 ↔ x = 0)
  (hN₁_add : ∀ x y, N₁ (x + y) ≤ N₁ x + N₁ y)
  (hN₁_hom : ∀ (c : F) x, N₁ (c • x) = ‖c‖ * N₁ x)
  (hN₂_nonneg : ∀ x, 0 ≤ N₂ x)
  (hN₂_eq_zero_iff : ∀ x, N₂ x = 0 ↔ x = 0)
  (hN₂_add : ∀ x y, N₂ (x + y) ≤ N₂ x + N₂ y)
  (hN₂_hom : ∀ (c : F) x, N₂ (c • x) = ‖c‖ * N₂ x) :
  ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ x : V, m * N₁ x ≤ N₂ x ∧ N₂ x ≤ M * N₁ x := by
  sorry



theorem theorem_256506_problem
  {n : Type*} [DecidableEq n] [Fintype n]
  {F : Type*} [Field F]
  (A B : Matrix n n F)
  (h : Matrix.charpoly A = Matrix.charpoly B) :
  (Matrix.charpoly A).roots = (Matrix.charpoly B).roots := by
  sorry

theorem theorem_255508_problem (N : ℕ) (v w v_bar w_bar : Fin N → ℝ) (B C : ℝ)
  (h1 : v = -w_bar)
  (h2 : w = -v_bar)
  (h3 : B = -C) :
  ∀ s : Fin N → ℝ, (∀ i, s i = 0 ∨ s i = 1) →
    (Matrix.dotProduct s w ≤ B ↔ Matrix.dotProduct (-s) v_bar ≤ -C) ∧
    (Matrix.dotProduct s v = Matrix.dotProduct (-s) w_bar) := by
  sorry









theorem theorem_256098_problem
  {E : Type*} [AddCommGroup E] [Module ℝ E]
  (x y V_r V_theta : ℝ)
  (e_x e_y : E)
  (e_r e_theta V : E)
  (h_nonorigin : x^2 + y^2 ≠ 0)
  (h_er : e_r = (Real.sqrt (x^2 + y^2))⁻¹ • (x • e_x + y • e_y))
  (h_etheta : e_theta = (Real.sqrt (x^2 + y^2))⁻¹ • (-y • e_x + x • e_y))
  (h_V : V = V_r • e_r + V_theta • e_theta) :
  V = (Real.sqrt (x^2 + y^2))⁻¹ • ((x * V_r - y * V_theta) • e_x + (y * V_r + x * V_theta) • e_y) := by
  sorry

theorem theorem_257149_problem
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (T : E →ₗ[ℝ] F)
  (c a : ℝ)
  (hc : c > 0)
  (h : ∀ (x : E) (r : ℝ), 0 < r → r * ‖T x‖ ≤ c * r ^ a * ‖x‖ ^ a) :
  T = 0 ∨ a = 1 := by
  sorry

theorem theorem_256289_problem (n : ℕ) (a b : ℝ)
  (ha : a ≠ 0)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : ∀ i j, A i j = if i = j then a
                      else if |(i : ℤ) - (j : ℤ)| = 1 then b
                      else 0)
  (X : Matrix (Fin n) (Fin n) ℝ)
  (hX : X = (1 / a) • A)
  (h_inv : IsUnit A) :
  A⁻¹ = (1 / a) • X⁻¹ := by
  sorry







