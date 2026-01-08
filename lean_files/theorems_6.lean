import Mathlib
import Mathlib.Tactic











theorem theorem_27177_problem (k : ℕ) (x : Fin k → EuclideanSpace ℝ (Fin k))
  (h_indep : LinearIndependent ℝ x)
  (G : Matrix (Fin k) (Fin k) ℝ)
  (hG : G = Matrix.of (fun i j => inner (x i) (x j)))
  (S : Set (EuclideanSpace ℝ (Fin k)))
  (hS : S = convexHull ℝ (insert 0 (Set.range x))) :
  MeasureTheory.volume S = ENNReal.ofReal ((1 / (Nat.factorial k : ℝ)) * Real.sqrt G.det) := by
  sorry









theorem theorem_28216_problem (n : ℕ)
  (f : (Fin n → ℝ) × lp (fun _ : ℕ ↦ ℝ) 2 → lp (fun _ : ℕ ↦ ℝ) 2)
  (h_def : ∀ (x : Fin n → ℝ) (y : lp (fun _ : ℕ ↦ ℝ) 2) (i : ℕ),
    f (x, y) i = if h : i < n then x ⟨i, h⟩ else y (i - n)) :
  Function.Injective f := by
  sorry



theorem theorem_27291_problem (n : ℕ) (v : Fin n → ℝ) :
  Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.vecMulVec v v) = 1 + Matrix.dotProduct v v := by
  sorry



theorem theorem_28410_problem (n k l : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (h_symm : A.IsSymm)
  (hk : k ≤ n)
  (hl : l ≤ n)
  (h_leading : (A.submatrix (Fin.castLE hk) (Fin.castLE hk)).det > 0)
  (h_trailing : (A.submatrix (fun i : Fin l => Fin.cast (Nat.sub_add_cancel hl) (Fin.natAdd (n - l) i))
                             (fun i : Fin l => Fin.cast (Nat.sub_add_cancel hl) (Fin.natAdd (n - l) i))).det < 0) :
  ¬ A.PosSemidef := by
  sorry



theorem theorem_28278_problem (r s : ℝ)
  (Q : ℝ → ℝ → ℝ → ℝ)
  (hQ : ∀ a b c, Q a b c = r * (a^2 + b^2 + c^2) + s * (a * b + b * c + c * a))
  (h1 : Q 1 1 1 = 240)
  (h2 : Q 1 1 (-1) = 240) :
  r = 80 ∧ s = 0 := by
  sorry

theorem theorem_28486_problem (a b : ℝ)
  (M : Matrix (Fin 3) (Fin 3) ℝ)
  (hM : M = !![3, 1 + a + b, 1 + a^2 + b^2;
               1 + a + b, 1 + a^2 + b^2, 1 + a^3 + b^3;
               1 + a^2 + b^2, 1 + a^3 + b^3, 1 + a^4 + b^4]) :
  M.det = ((a - 1) * (b - 1) * (a - b))^2 := by
  sorry

theorem theorem_28079_problem
  (S T : ℕ) (hS : 0 < S) (hT : 0 < T)
  (x y : Fin S → Fin T → ℝ)
  (x_bar_s : Fin S → ℝ) (x_bar_t : Fin T → ℝ) (x_bar : ℝ)
  (y_bar_s : Fin S → ℝ) (y_bar_t : Fin T → ℝ) (y_bar : ℝ)
  (hx_bar_s : ∀ s, x_bar_s s = (∑ t, x s t) / (T : ℝ))
  (hx_bar_t : ∀ t, x_bar_t t = (∑ s, x s t) / (S : ℝ))
  (hx_bar : x_bar = (∑ s, ∑ t, x s t) / ((S : ℝ) * (T : ℝ)))
  (hy_bar_s : ∀ s, y_bar_s s = (∑ t, y s t) / (T : ℝ))
  (hy_bar_t : ∀ t, y_bar_t t = (∑ s, y s t) / (S : ℝ))
  (hy_bar : y_bar = (∑ s, ∑ t, y s t) / ((S : ℝ) * (T : ℝ)))
  (x_tilde : Fin S → Fin T → ℝ)
  (y_tilde : Fin S → Fin T → ℝ)
  (hx_tilde : ∀ s t, x_tilde s t = x s t - x_bar_s s - x_bar_t t + x_bar)
  (hy_tilde : ∀ s t, y_tilde s t = y s t - y_bar_s s - y_bar_t t + y_bar)
  (h_denom : ∑ s, ∑ t, (x_tilde s t)^2 ≠ 0) :
  (∑ s, ∑ t, y_tilde s t * x_tilde s t) / (∑ s, ∑ t, (x_tilde s t)^2) =
  (∑ s, ∑ t, (y s t - y_bar_s s - y_bar_t t + y_bar) * (x s t - x_bar_s s - x_bar_t t + x_bar)) /
  (∑ s, ∑ t, (x s t - x_bar_s s - x_bar_t t + x_bar)^2) := by
  sorry



theorem theorem_28106_problem {n k : ℕ}
  (A : Matrix (Fin n) (Fin n) ℝ)
  (B : Matrix (Fin n) (Fin k) ℝ)
  (h1 : A ^ 2 = A)
  (h2 : A = B * B.transpose)
  (h3 : B.transpose * B = 1) :
  ¬ IsUnit A ∨ A = 1 := by
  sorry



theorem theorem_28657_problem
  {V H : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (ι : V →L[ℝ] H)
  (h_dense : DenseRange ι)
  (h_inj : Function.Injective ι) :
  ∃ (J : H →L[ℝ] NormedSpace.Dual ℝ V), ∀ (f : H) (v : V), J f v = inner f (ι v) := by
  sorry

theorem theorem_28530_problem (n : ℕ) (x : ℕ → ℂ) (θ : ℝ) :
  Complex.abs (∑ k in Finset.range n, x k * Complex.exp (-Complex.I * ↑k * ↑θ)) ≤
  ∑ k in Finset.range n, Complex.abs (x k) := by
  sorry













theorem theorem_28893_problem
  (k l : ℕ)
  (h_le : k ≤ l)
  (U : Set (Fin k → ℝ))
  (hU : IsOpen U)
  (h0 : 0 ∈ U)
  (g : (Fin k → ℝ) → (Fin l → ℝ))
  (hg_diff : DifferentiableAt ℝ g 0)
  (h_dg : ∀ v : Fin k → ℝ, fderiv ℝ g 0 v = fun i : Fin l => if h : (i : ℕ) < k then v ⟨i, h⟩ else 0) :
  let g_tilde : (Fin k → ℝ) × (Fin (l - k) → ℝ) → (Fin l → ℝ) :=
    fun p => fun i : Fin l => if (i : ℕ) < k then g p.1 i else 0
  let h_map : (Fin k → ℝ) × (Fin (l - k) → ℝ) → (Fin l → ℝ) :=
    fun p => fun i : Fin l => if h : (i : ℕ) < k then 0 else p.2 ⟨i - k, by omega⟩
  let G : (Fin k → ℝ) × (Fin (l - k) → ℝ) → (Fin l → ℝ) :=
    fun p => g_tilde p + h_map p
  ∀ (u : Fin k → ℝ) (w : Fin (l - k) → ℝ),
    fderiv ℝ G (0, 0) (u, w) = fun i : Fin l => if h : (i : ℕ) < k then u ⟨i, h⟩ else w ⟨i - k, by omega⟩ := by
  sorry





theorem theorem_28696_problem
  (n : ℕ)
  -- Variables as functions of time (ℝ) and space (Fin n → ℝ)
  (ρ : ℝ → (Fin n → ℝ) → ℝ)
  (u : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
  (p : ℝ → (Fin n → ℝ) → ℝ)
  (τ : ℝ → (Fin n → ℝ) → Fin n → Fin n → ℝ)
  (g : Fin n → ℝ)
  -- Abstract partial derivative operators
  (partial_t : (ℝ → (Fin n → ℝ) → ℝ) → (ℝ → (Fin n → ℝ) → ℝ))
  (partial_i : Fin n → (ℝ → (Fin n → ℝ) → ℝ) → (ℝ → (Fin n → ℝ) → ℝ))
  -- Abstract Vector Operators acting on fields, returning vector fields
  (vec_dt_mom : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
  (vec_div_flux : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
  (vec_grad_p : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
  (vec_div_tau : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
  -- Definitions of Vector Operators in terms of indices (Hypotheses)
  (h_def_dt : ∀ t x j, vec_dt_mom t x j = partial_t (fun t' x' => ρ t' x' * u t' x' j) t x)
  (h_def_flux : ∀ t x j, vec_div_flux t x j = ∑ i, partial_i i (fun t' x' => ρ t' x' * u t' x' i * u t' x' j) t x)
  (h_def_grad : ∀ t x j, vec_grad_p t x j = partial_i j p t x)
  (h_def_tau : ∀ t x j, vec_div_tau t x j = ∑ i, partial_i i (fun t' x' => τ t' x' i j) t x)
  -- The Vector Form of Conservation of Momentum (Hypothesis)
  (h_vector_conservation : ∀ t x, vec_dt_mom t x + vec_div_flux t x = - vec_grad_p t x + vec_div_tau t x + (ρ t x • g)) :
  -- Goal: The Index Form
  ∀ t x j,
    partial_t (fun t' x' => ρ t' x' * u t' x' j) t x +
    (∑ i, partial_i i (fun t' x' => ρ t' x' * u t' x' i * u t' x' j) t x) =
    - partial_i j p t x +
    (∑ i, partial_i i (fun t' x' => τ t' x' i j) t x) +
    ρ t x * g j := by
  sorry



theorem theorem_29205_problem {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
  (v₀ : V) (w₀ : W)
  (hv : v₀ ≠ 0) (hw : w₀ ≠ 0) :
  v₀ ⊗ₜ[F] w₀ ≠ 0 := by
  sorry

theorem theorem_29106_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] :
  ∃ T : H ≃ₗ[ℝ] (H →L[ℝ] ℝ), ∀ (v w : H), T v w = inner v w := by
  sorry







theorem theorem_29006_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (M : V →ₗ[K] V)
  (v₁ v₂ w₁ w₂ : V)
  (b : Basis (Fin 4) K V)
  (hv1 : b 0 = v₁)
  (hw1 : b 1 = w₁)
  (hv2 : b 2 = v₂)
  (hw2 : b 3 = w₂)
  (hMv1 : M v₁ = 0)
  (hMw1 : M w₁ = v₁)
  (hMv2 : M v₂ = 0)
  (hMw2 : M w₂ = v₂) :
  LinearMap.toMatrix b b M = !![0, 1, 0, 0;
                                0, 0, 0, 0;
                                0, 0, 0, 1;
                                0, 0, 0, 0] := by
  sorry

theorem theorem_28812_problem (p : ℂ → ℂ) (x : ℂ)
  (h : p x = (x^2 + x + 1) * (x^2 - x + 1)) :
  p x = (x + 1/2 - (Complex.I * (Real.sqrt 3 : ℂ)) / 2) *
        (x + 1/2 + (Complex.I * (Real.sqrt 3 : ℂ)) / 2) *
        (x - 1/2 - (Complex.I * (Real.sqrt 3 : ℂ)) / 2) *
        (x - 1/2 + (Complex.I * (Real.sqrt 3 : ℂ)) / 2) := by
  sorry

theorem theorem_29029_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
  (vec : Matrix (Fin n) (Fin n) ℝ → Fin (n * n) → ℝ)
  (h_vec : ∀ M, vec M = Function.uncurry M ∘ finProdFinEquiv.symm) :
  Matrix.dotProduct (vec A) (vec B) = Matrix.trace (A.transpose * B) := by
  sorry







theorem theorem_30014_problem
  (n m : ℕ)
  (R_PP : Matrix (Fin n) (Fin n) ℝ)
  (R_FP : Matrix (Fin m) (Fin n) ℝ)
  (b_F : Matrix (Fin m) (Fin 1) ℝ)
  (b_P : Matrix (Fin n) (Fin 1) ℝ)
  (h_symm : R_PP.transpose = R_PP)
  (h_inv : Invertible R_PP)
  (h_grad : (2 : ℝ) • (b_F.transpose * R_FP) + (2 : ℝ) • (b_P.transpose * R_PP) = 0) :
  b_P = - (R_PP⁻¹ * R_FP.transpose * b_F) := by
  sorry





theorem theorem_29961_problem
  {W : Type*} [AddCommGroup W] [Module ℂ W]
  (V : Submodule ℂ (W →ₗ[ℂ] ℂ))
  (h_sep : ∀ w : W, w ≠ 0 → ∃ φ ∈ V, φ w ≠ 0)
  (weak_topo : TopologicalSpace W)
  (h_topo : weak_topo = ⨅ (φ : V), TopologicalSpace.induced (φ : W →ₗ[ℂ] ℂ) inferInstance)
  (Ψ : W →ₗ[ℂ] ℂ)
  (h_cont : @Continuous W ℂ weak_topo inferInstance Ψ) :
  Ψ ∈ V := by
  sorry















theorem theorem_30123_problem
  {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (T S : H →L[𝕜] H)
  (β : 𝕜) (hβ : β ≠ 0)
  (C : H →L[𝕜] H) (hC : C = T * S - β • (S * T))
  (h_rank : FiniteDimensional.finrank 𝕜 (LinearMap.range C) = 1) :
  LinearMap.range C ≤ LinearMap.range S := by
  sorry

theorem theorem_30531_problem
  (F : Type*) [Field F]
  (V : Type*) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (w : LinearMap.BilinForm F V)
  (h_nondeg : w.Nondegenerate)
  (Y : Submodule F V) :
  let ortho := fun (S : Set V) ↦ { v : V | ∀ u ∈ S, w v u = 0 }
  ortho (ortho Y) = (Y : Set V) := by
  sorry









theorem theorem_29811_problem
  {R : Type*} [CommRing R] (X Y : R)
  (hX : ∀ r : R, r * X = 0 → r = 0)
  (hY : ∀ r : R, r * Y ∈ Ideal.span {X} → r ∈ Ideal.span {X}) :
  (Function.Injective (fun (p : R) ↦ (-p * Y, p * X))) ∧
  (∀ a b : R, a * X + b * Y = 0 ↔ ∃ p : R, a = -p * Y ∧ b = p * X) ∧
  (∀ z : R, z ∈ Ideal.span {X, Y} ↔ ∃ a b : R, a * X + b * Y = z) := by
  sorry









theorem theorem_30677_problem
  {n m p : Type*}
  [AddCommGroup n] [Module ℝ n]
  [AddCommGroup m] [Module ℝ m]
  [AddCommGroup p] [Module ℝ p]
  (A B : n →ₗ[ℝ] m) (C : m →ₗ[ℝ] p) :
  (∀ x y : n, C (A x) = C (B y) → A x = B y) ↔
  (LinearMap.range A + LinearMap.range B) ⊓ LinearMap.ker C = ⊥ := by
  sorry

theorem theorem_30866_problem
  (n p : ℕ)
  (X : Matrix (Fin n) (Fin p) ℝ)
  (β : Matrix (Fin p) (Fin 1) ℝ)
  (σ : ℝ)
  (h_rank : IsUnit (Matrix.det (X.transpose * X))) -- Ensures X has full column rank so (XᵀX)⁻¹ exists
  (P_X : Matrix (Fin n) (Fin n) ℝ)
  (hP_X : P_X = X * (X.transpose * X)⁻¹ * X.transpose)
  (E : (Matrix (Fin n) (Fin 1) ℝ → ℝ) → ℝ)
  (hE : ∀ A : Matrix (Fin n) (Fin n) ℝ, E (fun ε => (ε.transpose * A * ε) 0 0) = σ^2 * Matrix.trace A) :
  E (fun ε =>
    let y := X * β + ε
    let residual := y - P_X * y
    (residual.transpose * residual) 0 0) = ((n : ℝ) - (p : ℝ)) * σ^2 := by
  sorry







theorem theorem_30658_problem (n : ℕ) (f : (Fin n → ℝ) → (Fin n → ℝ)) (c : Fin n → ℝ)
  (x : Fin n → ℝ) (hf : DifferentiableAt ℝ f x) :
  LinearMap.det ((fderiv ℝ (fun y ↦ f y + c) x).toLinearMap) =
  LinearMap.det ((fderiv ℝ f x).toLinearMap) := by
  sorry

theorem theorem_30888_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  {n : ℕ}
  (v : Basis (Fin n) F V)
  (f : Fin n → Module.Dual F V)
  (h_dual : ∀ i j, f i (v j) = if i = j then (1 : F) else 0)
  (phi : V →ₗ[F] Module.Dual F V)
  (h_phi : ∀ (a : Fin n → F), phi (∑ i, a i • v i) = ∑ i, a i • f i) :
  Function.Bijective phi := by
  sorry

theorem theorem_30778_problem
  {n m l : Type*} [Fintype n] [Fintype m] [Fintype l]
  [DecidableEq n] [DecidableEq m] [DecidableEq l]
  {R : Type*} [CommRing R]
  (A : Matrix m m R)
  (B : Matrix n n R)
  (P : Matrix n n R)
  (P_tilde : Matrix n n R)
  (N_P : Matrix n l R)
  (N_P_tilde : Matrix n l R)
  (hA : IsUnit A)
  (hB : IsUnit B)
  (hP : P ^ 2 = P)
  (hN_P : P * N_P = 0)
  (hP_tilde_def : P_tilde = P * B)
  (hP_tilde_proj : P_tilde ^ 2 = P_tilde)
  (hN_P_tilde : P_tilde * N_P_tilde = 0) :
  (P * B) * N_P_tilde = 0 := by
  sorry

theorem theorem_30377_problem
  {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Nontrivial W]
  (A : V →L[ℝ] W) (B : W →L[ℝ] V)
  (S_A : Set V) (hSA : S_A = {v | ‖A v‖ = ‖A‖ * ‖v‖})
  (S_B : Set W) (hSB : S_B = {w | ‖B w‖ = ‖B‖ * ‖w‖}) :
  ‖A.comp B‖ = ‖A‖ * ‖B‖ ↔ ∃ w ∈ S_B, w ≠ 0 ∧ B w ∈ S_A := by
  sorry









theorem theorem_31459_problem (n : ℕ) (S : Set (Fin n → ℝ)) (hS : Convex ℝ S) :
  Convex ℝ { p : (Fin n → ℝ) × ℝ | 0 < p.2 ∧ p.2⁻¹ • p.1 ∈ S } := by
  sorry

theorem theorem_31008_problem
  (n p : ℕ)
  (X : Matrix (Fin n) (Fin p) ℝ)
  (beta : Matrix (Fin p) (Fin 1) ℝ)
  (sigma : ℝ)
  (Ω : Type*)
  (epsilon : Ω → Matrix (Fin n) (Fin 1) ℝ)
  (Y : Ω → Matrix (Fin n) (Fin 1) ℝ)
  (beta_hat : Ω → Matrix (Fin p) (Fin 1) ℝ)
  (Var : {m : ℕ} → (Ω → Matrix (Fin m) (Fin 1) ℝ) → Matrix (Fin m) (Fin m) ℝ)
  (h_inv : Invertible (X.transpose * X))
  (h_Y : Y = fun ω ↦ X * beta + epsilon ω)
  (h_beta_hat : beta_hat = fun ω ↦ (⅟(X.transpose * X)) * X.transpose * Y ω)
  (h_var_epsilon : Var epsilon = (sigma ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ))
  (h_var_affine : ∀ {m k : ℕ} (A : Matrix (Fin k) (Fin m) ℝ) (b : Matrix (Fin k) (Fin 1) ℝ) (Z : Ω → Matrix (Fin m) (Fin 1) ℝ),
    Var (fun ω ↦ A * Z ω + b) = A * Var Z * A.transpose) :
  Var beta_hat = (sigma ^ 2) • (⅟(X.transpose * X)) := by
  sorry







theorem theorem_31028_problem
  (n : ℕ) [NeZero n]
  (F : Type*) [Field F]
  (A B : Matrix (Fin n) (Fin n) F) :
  let E : Fin n → Fin n → Matrix (Fin n) (Fin n) F := fun i j ↦ Matrix.stdBasisMatrix i j 1
  let orb : Set (Matrix (Fin n) (Fin n) F) := {X | ∃ T : Matrix (Fin n) (Fin n) F, IsUnit T.det ∧ X = T * A * T⁻¹}
  let S : Set (Matrix (Fin n) (Fin n) F) := {M | ∃ a : Fin n → F, M = ∑ j : Fin n, a j • E (Fin.last (n - 1)) j}
  (∃ T : Matrix (Fin n) (Fin n) F, IsUnit T.det ∧ ∃ s ∈ S, B = T * A * T⁻¹ + s) ↔
  B ∈ {K | ∃ X ∈ orb, ∃ Y ∈ S, K = X + Y} := by
  sorry







theorem theorem_31776_problem
  (n : ℕ)
  (F : (Fin n → ℝ) → (Fin n → ℝ))
  (hF : ContDiff ℝ 1 F)
  (τ : Set (Fin n → ℝ))
  (hτ_conn : IsPathConnected τ)
  (h_det_nonzero : ∀ x ∈ τ, (fderiv ℝ F x).det ≠ 0)
  (z₁ z₂ : Fin n → ℝ)
  (hz₁ : z₁ ∈ τ)
  (hz₂ : z₂ ∈ τ)
  (h_z₁_pos : (fderiv ℝ F z₁).det > 0) :
  (fderiv ℝ F z₂).det > 0 := by
  sorry



theorem theorem_31639_problem (n : ℕ)
  (C : Matrix (Fin n) (Fin n) ℂ)
  (hC : Invertible C)
  (x : Fin n → ℂ)
  (y : Fin n → ℂ)
  (h_def : y = Matrix.mulVec C (fun i => Complex.log (1 + Complex.exp ((Matrix.mulVec (⅟C) x) i)))) :
  y = Matrix.mulVec C (fun i => Complex.log (1 + Complex.exp ((Matrix.mulVec (⅟C) x) i))) := by
  sorry

theorem theorem_31659_problem
  (n : ℕ)
  (F : (Fin n → ℝ) → (Fin n → ℝ))
  (k : Fin n)
  (x b c : Fin n → ℝ)
  (hF : ContDiff ℝ 2 F) :
  let F_k := fun y ↦ F y k
  let Hessian : Matrix (Fin n) (Fin n) ℝ := fun i j ↦
    (fderiv ℝ (fderiv ℝ F_k) x) (Pi.single i 1) (Pi.single j 1)
  (fderiv ℝ (fderiv ℝ F_k) x) b c = Matrix.dotProduct b (Matrix.mulVec Hessian c) := by
  sorry





theorem theorem_31573_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] (hdim : FiniteDimensional.finrank ℝ V = 3)
  (f : V → ℝ) (x : V) (pts : Fin 3 → V)
  (hindep : LinearIndependent ℝ (fun i => x - pts i)) :
  ∃! g : V, ∀ i : Fin 3, inner g (x - pts i) = f x - f (pts i) := by
  sorry







