import Mathlib
import Mathlib.Tactic



theorem theorem_208104_problem (m n : ℕ)
  (U : Matrix (Fin m) (Fin n) ℝ)
  [Invertible (U * U.transpose)] :
  let W : Matrix (Fin n) (Fin n) ℝ := 1 - (2 : ℝ) • U.transpose * (U * U.transpose)⁻¹ * U
  W.transpose * W = 1 := by
  sorry







theorem theorem_208773_problem (n : ℕ) (R Q : Matrix (Fin n) (Fin n) ℝ)
  (hR_orth : R.transpose * R = 1)
  (hR_det : Matrix.det R = 1)
  (hQ : Q.IsSymm) :
  (R * Q * R.transpose).IsSymm := by
  sorry

theorem theorem_208442_problem
  {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (f : X → ℝ) (μ L : ℝ)
  (h_diff : ContDiff ℝ 2 f)
  (h_bounds : 0 < μ ∧ μ ≤ L)
  (h_hess : ∀ x : X, ∀ u : X,
    μ * ‖u‖^2 ≤ inner ((fderiv ℝ (gradient f) x) u) u ∧
    inner ((fderiv ℝ (gradient f) x) u) u ≤ L * ‖u‖^2) :
  ∀ x : X, spectrum ℝ (fderiv ℝ (gradient f) x) ⊆ Set.Icc μ L := by
  sorry



theorem theorem_209387_problem
  (n : ℕ)
  (μ : Fin n → ℝ)
  (δ : ℝ) (hδ : δ > 0)
  (M : ℝ) (hM : M > 0)
  (hM_large : ∀ i j : Fin n, |μ i - μ j| + δ ≤ M) :
  (∀ i j : Fin n, i < j → |μ i - μ j| ≥ δ) ↔
  (∃ z : Fin n → Fin n → ℝ,
    (∀ i j : Fin n, i < j → z i j = 0 ∨ z i j = 1) ∧
    (∀ i j : Fin n, i < j → μ j - μ i + δ ≤ M * z i j) ∧
    (∀ i j : Fin n, i < j → μ i - μ j + δ ≤ M * (1 - z i j))) := by
  sorry

theorem theorem_208869_problem
  (n p : Type*) [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
  (X A : Matrix n p ℝ)
  (hX : X.transpose * X = 1)
  (sym : Matrix p p ℝ → Matrix p p ℝ)
  (hsym : ∀ B, sym B = (1 / 2 : ℝ) • (B + B.transpose)) :
  X.transpose * A + A.transpose * X = 0 ↔ sym (X.transpose * A) = 0 := by
  sorry

theorem theorem_209300_problem 
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (Λ : V → ℂ) (h z : V) :
  inner z ((Λ h) • z - h) = (Λ h) * inner z z - inner z h := by
  sorry



theorem theorem_209295_problem
  {n : ℕ} {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  (v : Basis (Fin n) F V)
  (inner_prod : V → V → F)
  (h_def : ∀ (x y : V), inner_prod x y = ∑ i, (v.repr x i) * (v.repr y i)) :
  ∀ (i j : Fin n), inner_prod (v i) (v j) = if i = j then (1 : F) else 0 := by
  sorry

theorem theorem_209459_problem (x y : ℕ → ℝ)
  (hx : CauchySeq x) (hy : CauchySeq y) :
  CauchySeq (fun n ↦ x n * y n) := by
  sorry





theorem theorem_209376_problem
  {F : Type*} [Field F]
  {n : Type*} [Fintype n] [DecidableEq n]
  (T R J : Matrix n n F)
  (hR : Invertible R)
  (h : R⁻¹ * (T - (3 : F) • (1 : Matrix n n F)) * R = J) :
  R⁻¹ * T * R = J + (3 : F) • (1 : Matrix n n F) := by
  sorry







theorem theorem_209561_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  (T : X →ₗ[𝕜] Y)
  (h : IsClosed (T.graph : Set (X × Y))) :
  Continuous T := by
  sorry





theorem theorem_209425_problem
  (n : ℕ)
  (X : Set (Matrix (Fin n) (Fin n) ℝ))
  (hX_binary : ∀ x ∈ X, ∀ i j, x i j = 0 ∨ x i j = 1)
  (u : Matrix (Fin n) (Fin n) ℝ)
  (x_star : Matrix (Fin n) (Fin n) ℝ)
  (hx_star : x_star ∈ X)
  (h_opt : ∀ x ∈ X, ∑ i, ∑ j, u i j * x_star i j ≥ ∑ i, ∑ j, u i j * x i j)
  (i₀ j₀ : Fin n)
  (h_entry : x_star i₀ j₀ = 1)
  (δ : ℝ)
  (h_delta : δ > 0)
  (u' : Matrix (Fin n) (Fin n) ℝ)
  (h_u' : ∀ i j, u' i j = if i = i₀ ∧ j = j₀ then u i j + δ else u i j) :
  ∀ x ∈ X, ∑ i, ∑ j, u' i j * x_star i j ≥ ∑ i, ∑ j, u' i j * x i j := by
  sorry

theorem theorem_209665_problem
  (u : ℝ → ℝ)
  (hu_neg : ∀ x, x < 0 → u x = 0)
  (hu_pos : ∀ x, 0 < x → u x = 1)
  (hu_mono : Monotone u)
  (r : ℕ → ℚ)
  (hr : Function.Surjective r)
  (f : ℝ → ℝ)
  (hf : ∀ x, f x = ∑' n, (1 / 2 : ℝ) ^ (n + 1) * u (x - r n)) :
  Monotone f ∧ (∀ x, ContinuousAt f x ↔ Irrational x) := by
  sorry









theorem theorem_210358_problem (n : ℕ) (W : Matrix (Fin n) (Fin n) ℝ)
  (hW : W.transpose * W = 4 • (1 : Matrix (Fin n) (Fin n) ℝ)) :
  let A := Matrix.fromBlocks W W W (-W)
  let B := (1 / (2 * Real.sqrt 2)) • A
  B.transpose * B = 1 := by
  sorry





theorem theorem_210707_problem
  (m r : ℕ)
  (W : Type*) [AddCommGroup W] [Module ℝ W]
  (S : Submodule ℝ W)
  (x : Fin m → W)
  (h_i1 : ∀ i, x i ∉ S)
  (β : Fin r → Fin m → ℝ)
  (h_indep : LinearIndependent ℝ β)
  (h_coint : ∀ j, (∑ i : Fin m, β j i • x i) ∈ S) :
  r ≤ m - 1 := by
  sorry









theorem theorem_210627_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : V →ₗ[ℝ] V)
  (a : ℝ) (ha : a > 0)
  (h_cond : ∀ y : V, ‖y‖ = a → ‖T y‖ < 1)
  (x : V) (hx : ‖x‖ ≤ a) :
  ‖T x‖ < 1 := by
  sorry





theorem theorem_210809_problem (n : ℕ) :
  (Fintype.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : ℝ) /
  (Fintype.card (Matrix (Fin n) (Fin n) (ZMod 2)) : ℝ) =
  ∏ k in Finset.range n, (1 - (1 : ℝ) / 2 ^ (k + 1)) := by
  sorry





theorem theorem_211185_problem
  {K : Type*} [Field K]
  (n : ℕ) (A : Matrix (Fin n) (Fin n) K)
  (h_char : (2 : K) ≠ 0)
  (h_odd : Odd n)
  (h_skew : A.transpose = -A) :
  A.det = 0 := by
  sorry

theorem theorem_211121_problem
  {R : Type*} [CommRing R]
  (m n : ℕ) (h : n ≤ m)
  (A : Matrix (Fin m) (Fin n) R)
  (B : Matrix (Fin n) (Fin m) R)
  (x : R) :
  Matrix.det (x • (1 : Matrix (Fin m) (Fin m) R) - A * B) =
  x ^ (m - n) * Matrix.det (x • (1 : Matrix (Fin n) (Fin n) R) - B * A) := by
  sorry



theorem theorem_211615_problem (a b c d r s : ℝ) 
  (h1 : c + d ≠ 0) 
  (h2 : a - b ≠ 0) : 
  (∃ x : ℝ, a^2 - b^2 - (c + d) * x = r ∧ c^2 - d^2 - (a - b) * x = s) ↔ 
  (a^2 - b^2 - r) * (a - b) = (c^2 - d^2 - s) * (c + d) := by
  sorry















theorem theorem_211742_problem
  (a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : ℝ)
  -- Conditions: Lines are pairwise not parallel (determinant of coefficients non-zero)
  (h12 : a₁ * b₂ - a₂ * b₁ ≠ 0)
  (h23 : a₂ * b₃ - a₃ * b₂ ≠ 0)
  (h31 : a₃ * b₁ - a₁ * b₃ ≠ 0)
  -- Definition of Vertices A, B, C as intersections of the lines
  (A B C : ℝ × ℝ)
  (hA2 : a₂ * A.1 + b₂ * A.2 + c₂ = 0)
  (hA3 : a₃ * A.1 + b₃ * A.2 + c₃ = 0)
  (hB1 : a₁ * B.1 + b₁ * B.2 + c₁ = 0)
  (hB3 : a₃ * B.1 + b₃ * B.2 + c₃ = 0)
  (hC1 : a₁ * C.1 + b₁ * C.2 + c₁ = 0)
  (hC2 : a₂ * C.1 + b₂ * C.2 + c₂ = 0)
  -- Condition: Lines are not concurrent (Triangle is non-degenerate)
  -- Since A is on L2 and L3, checking A is not on L1 suffices given h12, h23, h31.
  (h_non_concur : a₁ * A.1 + b₁ * A.2 + c₁ ≠ 0) :
  -- Conclusion: Unique orthocenter H exists satisfying the altitude equations
  ∃! H : ℝ × ℝ,
    (b₁ * (H.1 - A.1) - a₁ * (H.2 - A.2) = 0) ∧
    (b₂ * (H.1 - B.1) - a₂ * (H.2 - B.2) = 0) ∧
    (b₃ * (H.1 - C.1) - a₃ * (H.2 - C.2) = 0) := by
  sorry







theorem theorem_211753_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) (hlam : lam ≠ 0) :
  Matrix.det (A + lam • B) = lam ^ n * Matrix.det (lam⁻¹ • A + B) := by
  sorry







theorem theorem_212234_problem
  {n : ℕ}
  {H : Type*}
  [AddCommGroup H] [Module ℤ H]
  (f : H ≃+ (Fin n → ℤ))
  (ω η : Basis (Fin n) ℤ H)
  (C : Matrix (Fin n) (Fin n) ℤ)
  (h : ∀ i, f (ω i) = ∑ j, C i j • f (η j)) :
  C.det = 1 ∨ C.det = -1 := by
  sorry

theorem theorem_212306_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (n : ℕ) (M : ℝ)
  (f : Fin n → V)
  (h₁ : ∀ i, ‖f i‖ ≤ M)
  (h₂ : ∀ i j, i ≠ j → inner (f i) (f j) = (-1 : ℝ)) :
  (n : ℝ) ≤ M^2 + 1 := by
  sorry



theorem theorem_211830_problem
  {n k k' : ℕ}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (x : Fin n → E)
  (c : Fin k → E)
  (hk : k' < k)
  (S : Fin k → Finset (Fin n))
  (h_partition : ∀ i : Fin n, ∃! j, i ∈ S j)
  (h_assign : ∀ (j : Fin k) (i : Fin n), i ∈ S j → ∀ l : Fin k, ‖x i - c j‖ ≤ ‖x i - c l‖)
  (c' : Fin k → E)
  (h_fixed : ∀ j : Fin k, j.val < k' → c' j = c j)
  (h_update : ∀ j : Fin k, k' ≤ j.val → c' j = ((S j).card : ℝ)⁻¹ • ∑ i in S j, x i) :
  ∑ j : Fin k, ∑ i in S j, ‖x i - c' j‖^2 ≤ ∑ j : Fin k, ∑ i in S j, ‖x i - c j‖^2 := by
  sorry

theorem theorem_211762_problem
  (f : ℝ → ℝ → ℝ → ℝ → ℝ)
  (g : ℝ → ℝ → ℝ → ℝ)
  (h : ℝ → ℝ → ℝ)
  (φ ψ : ℝ → ℝ)
  (hf : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2.1 p.2.2.2))
  (hg : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2))
  (hh : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => h p.1 p.2))
  (hφ : ContDiff ℝ ⊤ φ)
  (hψ : ContDiff ℝ ⊤ ψ)
  (h_impl_g : ∀ y, g y (φ y) (ψ y) = 0)
  (h_impl_h : ∀ y, h (φ y) (ψ y) = 0)
  (x : ℝ) :
  ∀ y, deriv (fun y' => f x y' (φ y') (ψ y')) y =
       deriv (fun y' => f x y' (φ y) (ψ y)) y +
       deriv (fun z => f x y z (ψ y)) (φ y) * deriv φ y +
       deriv (fun t => f x y (φ y) t) (ψ y) * deriv ψ y := by
  sorry

theorem theorem_211786_problem
  (rot : ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
  (rot_inv : Matrix (Fin 3) (Fin 3) ℝ → ℝ × ℝ × ℝ)
  (α β γ u v r a b c : ℝ)
  (R_air R_cam R_combined : Matrix (Fin 3) (Fin 3) ℝ)
  (h_inv : ∀ x y z, rot_inv (rot x y z) = (x, y, z))
  (h_air : R_air = rot α β γ)
  (h_cam : R_cam = rot u v r)
  (h_combined_def : R_combined = R_air * R_cam)
  (h_abc_eq : rot a b c = R_combined) :
  (a, b, c) = rot_inv R_combined := by
  sorry

theorem theorem_212238_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
  let B := fun (i : ℕ) => Cardinal.toNat (Matrix.rank (A ^ (i - 1))) - Cardinal.toNat (Matrix.rank (A ^ i))
  let C := fun (i : ℕ) => B i - B (i + 1)
  let D := fun (i : ℕ) => ((Finset.Ico i n).filter (fun j => Odd (C j))).card
  (∃ R : Matrix (Fin n) (Fin n) ℂ, R ^ 2 = A) ↔ ∀ j ∈ Finset.Ico 1 n, C j = 0 → Even (D j) := by
  sorry





theorem theorem_213033_problem (a : EuclideanSpace ℝ (Fin 3))
  (f : EuclideanSpace ℝ (Fin 3) → ℝ)
  (hf : ∀ x, f x = inner a x) :
  ∀ x, gradient f x = a := by
  sorry



theorem theorem_212830_problem
  (H W Cin Cout : ℕ)
  (X : Fin H → Fin W → Fin Cin → ℝ)
  (W_1x1 : Matrix (Fin Cout) (Fin Cin) ℝ) :
  ∀ (i : Fin H) (j : Fin W),
    (fun (k : Fin Cout) => ∑ c : Fin Cin, W_1x1 k c * X i j c) = Matrix.mulVec W_1x1 (X i j) := by
  sorry

theorem theorem_212075_problem (φ B : ℝ) (x u w : ℕ → ℝ) (x_tilde : ℕ → ℝ)
  (h_flip : ∀ t, x_tilde t = 1 - x t)
  (h_dyn : ∀ t, x (t + 1) = φ * x t + B * u (t + 1) + w (t + 1)) :
  ∀ t, x_tilde (t + 1) = (1 - φ) + φ * x_tilde t - B * u (t + 1) - w (t + 1) := by
  sorry

theorem theorem_212602_problem (n : ℕ) (M P J : Matrix (Fin n) (Fin n) ℂ)
  (hP : Invertible P)
  (hM : M = P * J * P⁻¹)
  (k : ℕ) (hk : 0 < k) :
  M ^ k = P * (J ^ k) * P⁻¹ := by
  sorry



theorem theorem_212868_problem
  {K : Type*} [Field K]
  (a b c d : Fin 4 → K)
  (hl : LinearIndependent K ![a, b])
  (hm : LinearIndependent K ![c, d]) :
  (Submodule.span K ({a, b} : Set (Fin 4 → K)) ⊓ Submodule.span K {c, d} ≠ ⊥) ↔
  Matrix.det (fun i j => ![a, b, c, d] j i) = 0 := by
  sorry







theorem theorem_212659_problem
  (n : ℕ) (hn : 1 < n)
  (X : Matrix (Fin n) (Fin n) ℝ)
  (hX : X.rank = n) :
  ¬ ∃ (A : Matrix (Fin n) (Fin (n^2)) ℝ)
      (B : Matrix (Fin 1) (Fin n) ℝ)
      (x : Matrix (Fin (n^2)) (Fin 1) ℝ),
    A * x * B = X := by
  sorry











theorem theorem_213353_problem
  (K : Set ℝ) (hK : IsCompact K)
  (A : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
  (R₁ R₂ : C(K, ℝ) →L[ℝ] A)
  (h_faithful1 : Function.Injective R₁)
  (h_faithful2 : Function.Injective R₂)
  (N : A)
  (h_id1 : R₁ 1 = N)
  (h_id2 : R₂ 1 = N)
  (h_poly : ∀ p : Polynomial ℝ,
    let x_map : C(K, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
    R₁ (Polynomial.aeval x_map p) = R₂ (Polynomial.aeval x_map p)) :
  R₁ = R₂ := by
  sorry



theorem theorem_213476_problem 
  {Ω V : Type*} 
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (E : (Ω → ℝ) →ₗ[ℝ] ℝ) -- Expectation operator as a linear map
  (hE_pos : ∀ f : Ω → ℝ, (∀ x, 0 ≤ f x) → 0 ≤ E f) -- Expectation preserves non-negativity
  (X : Ω → V) -- Covariate vector X_i
  (Q : Ω → ℝ) -- Conditional quantile Q_tau(Y_i | X_i)
  (w : Ω → ℝ) -- Weight function w(X_i, tau)
  (hw_nonneg : ∀ ω, 0 ≤ w ω) -- Weights are non-negative
  (β_τ : V) -- The parameter vector estimated by quantile regression
  -- The regularity condition derived in Angrist et al. (2006) implies the first-order condition:
  -- E[ w * (X'β_τ - Q) * X ] = 0
  (h_foc : ∀ v : V, E (fun ω ↦ w ω * (inner (X ω) β_τ - Q ω) * inner (X ω) v) = 0) :
  -- Conclusion: β_τ minimizes the weighted expectation of the squared specification error
  ∀ β : V, E (fun ω ↦ w ω * (inner (X ω) β_τ - Q ω)^2) ≤ E (fun ω ↦ w ω * (inner (X ω) β - Q ω)^2) := by
  sorry

theorem theorem_213739_problem (n : ℕ)
  (f : AlternatingMap ℝ (Fin n → ℝ) ℝ (Fin n))
  (g : Matrix (Fin n) (Fin n) ℝ → ℝ)
  (hg : ∀ A, g A = Matrix.det A * f (1 : Matrix (Fin n) (Fin n) ℝ))
  (hf : f (1 : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
  ∀ A, f A = g A := by
  sorry









theorem theorem_213690_problem
  (e : Fin 3 → (Fin 3 → ℝ))
  (partial_r : Fin 3 → (Fin 3 → ℝ))
  (h_ortho : ∀ i j, Matrix.dotProduct (e i) (e j) = if i = j then 1 else 0) :
  ∀ i, (∑ j : Fin 3, (Matrix.dotProduct (e i) (e j)) • (partial_r j)) = partial_r i := by
  sorry



theorem theorem_213445_problem (x_0 y_0 x y a_1 b_1 a_2 b_2 K : ℝ)
  (h1 : a_1 * (x - x_0) + b_1 * (y - y_0) = 0)
  (h2 : a_2 * (x - x_0) + b_2 * (y - y_0) = 0) :
  (a_1 + K * a_2) * (x - x_0) + (b_1 + K * b_2) * (y - y_0) = 0 := by
  sorry





