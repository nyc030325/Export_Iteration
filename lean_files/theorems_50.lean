import Mathlib
import Mathlib.Tactic











theorem theorem_268559_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (X₀ : Submodule K V)
  (x x₀ : V)
  (h : K)
  (hx : x ∈ X₀)
  (hx₀ : x₀ ∈ X₀)
  (hh : h ≠ 0) :
  h⁻¹ • x + x₀ ∈ X₀ := by
  sorry



theorem theorem_267966_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (n : ℕ)
  (v : Fin n → V →L[ℝ] ℝ)
  (a b : V)
  (hv : ∀ i, v i ≠ 0)
  (ha : ∀ i, v i a ≠ 0)
  (hb : ∀ i, v i b ≠ 0) :
  (∃ γ : Path a b, ∀ (i : Fin n) (t : unitInterval), v i (γ t) ≠ 0) ↔
  (∀ i, Real.sign (v i a) = Real.sign (v i b)) := by
  sorry

theorem theorem_268759_problem
  (X : Type*) [Nonempty X]
  (f_seq : ℕ → X → ℝ) (f : X → ℝ) :
  (∀ ε > 0, ∃ N, ∀ n ≥ N, BddAbove (Set.range (fun x => |f_seq n x - f x|)) ∧
    sSup (Set.range (fun x => |f_seq n x - f x|)) < ε) ↔
  (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, |f_seq n x - f x| < ε) := by
  sorry



theorem theorem_268217_problem
  {F : Type*} [Field F]
  (n : ℕ)
  (p : Polynomial F)
  (hp_monic : p.Monic)
  (hp_degree : p.natDegree = n)
  (C : Matrix (Fin n) (Fin n) F)
  (hC : ∀ i j, C i j =
    if i.val = n - 1 then -p.coeff j
    else if j.val = i.val + 1 then 1
    else 0) :
  ∀ (x : F), (∃ v : Fin n → F, v ≠ 0 ∧ Matrix.mulVec C v = x • v) ↔ p.eval x = 0 := by
  sorry

theorem theorem_268719_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (m n : ℕ)
  (v : Fin m → V)
  (u : Fin n → V)
  (h_nm : n > m)
  (h_span : ∀ i, u i ∈ Submodule.span F (Set.range v)) :
  ¬ LinearIndependent F u := by
  sorry

theorem theorem_268911_problem (n p : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (C : Matrix (Fin p) (Fin n) ℝ)
  (hA : A.PosDef)
  (hC : C.rank = p) :
  (C * A * C.transpose).PosDef := by
  sorry



theorem theorem_268598_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (T R : V →ₗ[F] V)
  (h_comm : T ∘ₗ R = R ∘ₗ T)
  (μ : F)
  (E : Set V)
  (hE : E = {v : V | T v = μ • v}) :
  ∀ v ∈ E, R v ∈ E := by
  sorry









theorem theorem_268433_problem (n k : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (U : Matrix (Fin n) (Fin k) ℝ)
  (V : Matrix (Fin k) (Fin n) ℝ)
  (C : Matrix (Fin k) (Fin k) ℝ)
  (hA : IsUnit A)
  (hC : IsUnit C)
  (h_inner : IsUnit (C⁻¹ + V * A⁻¹ * U)) :
  (A + U * C * V)⁻¹ = A⁻¹ - A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ := by
  sorry





theorem theorem_268463_problem (n : ℕ) :
  let P : ℕ → ℕ := fun r ↦ ((Finset.Icc 1 n).powerset.filter 
    (fun s ↦ s.card = r ∧ s.sum id = (r * (n + 1) + 1) / 2)).card
  let b : ℕ → ℕ := fun r ↦ P r + P (r - 1)
  ∀ i ≥ 2, b (i - 1) * b (i + 1) ≤ (b i)^2 := by
  sorry

theorem theorem_269009_problem
  (n k1 k2 : ℕ)
  (Y : Matrix (Fin n) (Fin 1) ℝ)
  (X1 : Matrix (Fin n) (Fin k1) ℝ)
  (X2 : Matrix (Fin n) (Fin k2) ℝ)
  (beta1 : Matrix (Fin k1) (Fin 1) ℝ)
  (beta2 : Matrix (Fin k2) (Fin 1) ℝ)
  (M_X1 : Matrix (Fin n) (Fin n) ℝ)
  (h_inv1 : Invertible (X1.transpose * X1))
  (hM : M_X1 = (1 : Matrix (Fin n) (Fin n) ℝ) - X1 * (X1.transpose * X1)⁻¹ * X1.transpose)
  (h_inv2 : Invertible (X2.transpose * M_X1 * X2))
  (h_ols1 : X1.transpose * (Y - X1 * beta1 - X2 * beta2) = 0)
  (h_ols2 : X2.transpose * (Y - X1 * beta1 - X2 * beta2) = 0) :
  beta2 = (X2.transpose * M_X1 * X2)⁻¹ * X2.transpose * M_X1 * Y := by
  sorry

theorem theorem_269596_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (T : V →ₗ[F] V) :
  ∃ N : ℕ, ∀ n ≥ N, LinearMap.range (T ^ n) = LinearMap.range (T ^ N) := by
  sorry



theorem theorem_269432_problem
  {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  (F : V → W) (hF : Differentiable ℝ F) (A X : V) :
  deriv (fun t : ℝ => F (A + t • X)) 0 = fderiv ℝ F A X := by
  sorry

theorem theorem_268570_problem (m n : ℕ) (c : ℕ → ℝ) (b : ℕ → ℂ)
  (hmn : m ≤ n)
  (hc_nonneg : 0 ≤ c m)
  (hc_mono : MonotoneOn c (Set.Icc m n))
  (hc_n : c n = 1) :
  Complex.abs (∑ k in Finset.Icc m n, (c k : ℂ) * b k) ≤
    (Finset.Icc m n).sup' (Finset.nonempty_Icc.mpr hmn)
      (fun k => Complex.abs (∑ j in Finset.Icc m k, b j)) := by
  sorry















theorem theorem_270371_problem (n : ℕ) (R : Type*) [CommRing R] (A : Matrix (Fin n) (Fin n) R)
  (h : A ^ 4 = (-4 : R) • (1 : Matrix (Fin n) (Fin n) R)) :
  ∀ k : ℕ, A ^ (4 * k) = ((-4 : R) ^ k) • (1 : Matrix (Fin n) (Fin n) R) := by
  sorry



theorem theorem_269989_problem (n p : ℕ) (k : Fin p → ℕ)
  (hn : 0 < n)
  (hk : ∀ i, k i < n) :
  ¬ ∃ (φ : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] (Π i, Matrix (Fin (k i)) (Fin (k i)) ℂ)), Function.Injective φ := by
  sorry

theorem theorem_269857_problem
  (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  (N : Type*) [NormedAddCommGroup N] [NormedSpace 𝕜 N] :
  Nonempty ((NormedSpace.Dual 𝕜 N) ≃ₗᵢ[𝕜] (NormedSpace.Dual 𝕜 (UniformSpace.Completion N))) := by
  sorry

theorem theorem_270330_problem (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
  ∫ x : ℝ, (Real.log (a ^ 2 + x ^ 2) : ℂ) / ((x : ℂ) - I * b) ^ 2 = (2 * π / (a + b) : ℂ) := by
  sorry





theorem theorem_270875_problem (n : ℕ) (h : 2 ≤ n) :
  ∃ u v w : EuclideanSpace ℝ (Fin n), u ≠ 0 ∧ inner u v = (0 : ℝ) ∧ inner u w = (0 : ℝ) ∧ v ≠ w := by
  sorry



theorem theorem_270692_problem 
  (M N : ℕ) (a K : ℝ) 
  (hM : M ≥ N) (hN : N > 0) (ha : a ≠ 0)
  -- E_tr represents the term E[tr((aXX^H + I)⁻¹)]
  (E_tr : ℝ)
  -- F represents the function F(a) = E[tr((aXX^H + I)⁻¹YY^H)]
  (F : ℝ)
  -- Condition 1: Independence of X, Y and E[YY^H] = KI implies F decomposes
  (h_indep : F = K * E_tr)
  -- Condition 2: The Marcenko-Pastur spectral density implies the specific value for the trace of the resolvent
  (h_spectral : E_tr = (1 / (2 * a)) * (Real.sqrt ((a * ((M : ℝ) - N))^2 + 2 * a * ((M : ℝ) + N) + 1) + a * ((N : ℝ) - M) - 1)) :
  F = (K / (2 * a)) * (Real.sqrt ((a * ((M : ℝ) - N))^2 + 2 * a * ((M : ℝ) + N) + 1) + a * ((N : ℝ) - M) - 1) := by
  sorry





theorem theorem_270970_problem (x_A y_A x_B y_B x_C y_C : ℝ) :
  let A : ℝ × ℝ := (x_A, y_A)
  let B : ℝ × ℝ := (x_B, y_B)
  let C : ℝ × ℝ := (x_C, y_C)
  let m : Matrix (Fin 2) (Fin 2) ℝ := !![x_B - x_A, x_C - x_A; y_B - y_A, y_C - y_A]
  (MeasureTheory.volume (convexHull ℝ {A, B, C})).toReal = (1 / 2 : ℝ) * |m.det| := by
  sorry





theorem theorem_270835_problem
  {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]
  [DecidableEq n] [DecidableEq m] [DecidableEq k]
  (Q : Matrix n n ℝ)
  (S1 : Matrix n m ℝ)
  (S2 : Matrix n k ℝ)
  (Sigma : Matrix m m ℝ)
  (hQ : Q.IsSymm)
  (hSigma : Sigma.PosSemidef)
  (hS2 : S2 ≠ 0)
  (M : Matrix (n ⊕ m ⊕ k) (n ⊕ m ⊕ k) ℝ)
  (hM : M = Matrix.fromBlocks Q
            (fun i j => match j with | Sum.inl a => S1 i a | Sum.inr b => S2 i b)
            (Matrix.transpose (fun i j => match j with | Sum.inl a => S1 i a | Sum.inr b => S2 i b))
            (Matrix.fromBlocks Sigma 0 0 0)) :
  ¬ M.PosSemidef ∧ ¬ (-M).PosSemidef := by
  sorry

theorem theorem_271582_problem
  (n : ℕ)
  (F : Matrix (Fin n) (Fin n) ℝ)
  (lam : ℝ)
  (hlam : lam > 0) :
  IsUnit (F * F.transpose + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  sorry



theorem theorem_271331_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (Y : Submodule ℝ X)
  (θ : Y →L[ℝ] ℝ) :
  ∃ Φ : X →L[ℝ] ℝ, (∀ (y : Y), Φ y = θ y) ∧ ‖Φ‖ = ‖θ‖ := by
  sorry







theorem theorem_271242_problem
  (n : ℕ)
  (T : Fin n → Fin n → ℝ)
  (v_grad : Fin n → Fin n → ℝ) -- v_grad i j represents ∂v_j/∂x_i
  : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
      T i j * v_grad k l * (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)) =
    ∑ i : Fin n, ∑ j : Fin n, T i j * v_grad i j := by
  sorry









theorem theorem_271301_problem (n : ℕ)
  (p : Matrix (Fin n) (Fin n) ℤ)
  (q : Matrix (Fin n) (Fin n) ℕ)
  (A : Matrix (Fin n) (Fin n) ℚ)
  (hq : ∀ i j, q i j > 0)
  (hA : ∀ i j, A i j = (p i j : ℚ) / (q i j : ℚ)) :
  |A.det| ≤ ∏ i, ∏ j, ((|p i j| : ℚ) + 1) := by
  sorry

theorem theorem_272034_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (s : Set E)
  (f : E → ℝ)
  (h_open : IsOpen s)
  (h_conv : Convex ℝ s)
  (h_diff : ContDiffOn ℝ 2 f s)
  (h_hess : ∀ x ∈ s, ∀ u : E, 0 ≤ iteratedFDerivWithin ℝ 2 f s x (fun _ ↦ u)) :
  ConvexOn ℝ s f := by
  sorry





theorem theorem_272055_problem
  {E : Type*} [AddCommGroup E] [Module ℝ E]
  (S : Set E) (hS_fin : S.Finite) (hS_nonempty : S.Nonempty)
  (f : E →ₗ[ℝ] ℝ) :
  ∃ v ∈ S, ∀ x ∈ convexHull ℝ S, f x ≤ f v := by
  sorry



theorem theorem_271961_problem
  (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (C : ℕ → Set V)
  (h_decr : ∀ k, C (k + 1) ⊆ C k)
  (h_closed : ∀ k, IsClosed (C k))
  (h_nonempty : ∀ k, (C k).Nonempty)
  (n : ℕ)
  (h_int : (interior (C n)).Nonempty) :
  ¬ Nonempty (V ≃L[ℝ] (Fin (n + 1) → ℝ)) := by
  sorry





theorem theorem_271550_problem
  (n : ℕ)
  (x₁ x₂ y : Fin n → ℝ)
  (h_norm₁ : Matrix.dotProduct x₁ x₁ = 1)
  (h_norm₂ : Matrix.dotProduct x₂ x₂ = 1)
  (h_uncorr : Matrix.dotProduct x₁ x₂ = 0)
  (w₁ w₂ w₃ : ℝ)
  (hw₁ : w₁ = Matrix.dotProduct x₁ y / Matrix.dotProduct x₁ x₁)
  (hw₂ : w₂ = Matrix.dotProduct x₂ y / Matrix.dotProduct x₂ x₂)
  (hw₃ : w₃ = Matrix.dotProduct (x₁ + x₂) y / (Matrix.dotProduct x₁ x₁ + Matrix.dotProduct x₂ x₂)) :
  w₃ = (w₁ + w₂) / 2 := by
  sorry

















theorem theorem_272351_problem
  (X : Type*) [TopologicalSpace X] [CompactSpace X]
  (f_n : ℕ → X → ℝ) (f : X → ℝ)
  (h_cont_n : ∀ n, Continuous (f_n n))
  (h_mono : ∀ x, Monotone (fun n ↦ f_n n x))
  (h_cont_f : Continuous f)
  (h_pointwise : ∀ x, Filter.Tendsto (fun n ↦ f_n n x) Filter.atTop (nhds (f x))) :
  TendstoUniformly f_n f Filter.atTop := by
  sorry

theorem theorem_272532_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {V : Type*} [CommRing V] [Algebra ℝ V]
  (E : V →ₗ[ℝ] ℝ)
  (c : ℝ)
  (Sigma Omega : Matrix n n ℝ)
  (ft fs : n → V)
  (h_symm : Sigma.IsSymm)
  (h_moments : ∀ i j, E (ft i * fs j) = c * Omega i j) :
  E (∑ i, ∑ j, Sigma i j • (ft i * fs j)) = c * (Sigma * Omega).trace := by
  sorry









theorem theorem_272469_problem
  (n : ℕ)
  (norm_alpha norm_beta : (Fin n → ℝ) → ℝ)
  (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  (c : ℝ)
  (hc : c > 0)
  (h_beta_tri : ∀ x y, norm_beta (x + y) ≤ norm_beta x + norm_beta y)
  (h_beta_hom : ∀ (r : ℝ) x, norm_beta (r • x) = |r| * norm_beta x)
  (h_equiv : ∀ (x : Fin n → ℝ) (i : Fin n), |x i| ≤ c * norm_alpha x)
  (x : Fin n → ℝ)
  (hx : norm_alpha x = 1) :
  norm_beta (A x) ≤ c * (Finset.sum Finset.univ (fun i => norm_beta (A (Pi.basisFun ℝ (Fin n) i)))) := by
  sorry



theorem theorem_272257_problem (N M : ℕ) (hNM : N ≤ M)
  (X Y : ℤ → ℤ → ℝ)
  (hX_supp : ∀ i j : ℤ, ¬(1 ≤ i ∧ i ≤ N ∧ 1 ≤ j ∧ j ≤ N) → X i j = 0)
  (hY_def : ∀ i j : ℤ, Y i j = ∑ i' in Finset.range M, ∑ j' in Finset.range M, X (i - (i' : ℤ)) (j - (j' : ℤ))) :
  ∀ i j : ℤ, X i j = Y i j - ∑ p in (Finset.product (Finset.range M) (Finset.range M)).erase (0, 0), X (i - (p.1 : ℤ)) (j - (p.2 : ℤ)) := by
  sorry





theorem theorem_272887_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (y : ℝ → V) (t : ℝ)
  (hy : DifferentiableAt ℝ y t) :
  deriv (fun s => ‖y s‖ ^ 2) t = 2 * inner (y t) (deriv y t) := by
  sorry

theorem theorem_273006_problem (n : ℕ) (hn : 0 < n) :
  ∫ x in (0 : ℝ)..1, x * ((n : ℝ) * x ^ (n - 1)) = (n : ℝ) / (n + 1) := by
  sorry

theorem theorem_272844_problem
  {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (A : E →L[𝕜] F) (v : E) (h : v ≠ 0) :
  ‖A v‖ / ‖v‖ ≤ ‖A‖ := by
  sorry





theorem theorem_273434_problem (n p : ℕ)
  (X : Matrix (Fin n) (Fin p) ℝ)
  (Y : Matrix (Fin n) (Fin 1) ℝ)
  (β : Matrix (Fin p) (Fin 1) ℝ)
  (h : X.transpose * X * β = X.transpose * Y) :
  β.transpose * X.transpose * X * β = β.transpose * X.transpose * Y := by
  sorry



theorem theorem_273426_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (phi : V →ₗ[K] V) :
  Polynomial.aeval phi (LinearMap.charpoly phi) = 0 := by
  sorry



