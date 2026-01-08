import Mathlib
import Mathlib.Tactic



theorem theorem_42069_problem
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  (E : Submodule ℝ X)
  (f₀ g₀ : E →ₗ[ℝ] ℝ)
  (h_bound : ∀ (e : E), |f₀ e| + |g₀ e| ≤ ‖e‖) :
  ∃ (f g : X →ₗ[ℝ] ℝ),
    (∀ (e : E), f e = f₀ e) ∧
    (∀ (e : E), g e = g₀ e) ∧
    (∀ (x : X), |f x| + |g x| ≤ ‖x‖) := by
  sorry







theorem theorem_42707_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (A : V →L[ℝ] V)
  (f : V → ℝ)
  (hf : ∀ x, f x = inner (A x) (A x))
  (x h : V) :
  fderiv ℝ f x h = 2 * inner (A x) (A h) := by
  sorry



theorem theorem_42233_problem
  {K : Type*} [Field K]
  {m n : ℕ}
  (U V : Matrix (Fin m) (Fin n) K)
  (E : Matrix (Fin m) (Fin m) K)
  (hE : Invertible E)
  (h_row_equiv : V = E * U)
  (j : Fin n)
  (α : Fin n → K)
  (h_comb_U : (fun i ↦ U i j) = ∑ k in Finset.Iio j, α k • (fun i ↦ U i k)) :
  (fun i ↦ V i j) = ∑ k in Finset.Iio j, α k • (fun i ↦ V i k) := by
  sorry

theorem theorem_43126_problem
  (G X : Type*) [AddGroup G] [AddAction G X]
  (n : ℕ)
  (V : Submodule ℂ (X → ℂ))
  (basis : Basis (Fin n) ℂ V)
  (h_inv : ∀ (g : G) (v : V), (fun x ↦ v.1 ((-g) +ᵥ x)) ∈ V) :
  ∃ ρ : Multiplicative G →* Matrix.GeneralLinearGroup (Fin n) ℂ,
    ∀ (g : G) (j : Fin n),
      (fun x ↦ (basis j).1 ((-g) +ᵥ x)) =
        ∑ i : Fin n, (ρ (Multiplicative.ofAdd g)).val i j • (basis i : X → ℂ) := by
  sorry

theorem theorem_43370_problem (ns : ℕ)
  (μ ρ θ : Fin ns → ℝ)
  (y_T ε_T : ℝ)
  (prob : Fin ns → ℝ)
  (y_hat : ℝ)
  -- E_cond s represents E[y_{T+1} | S_{T+1}=s, Ψ_T]
  (E_cond : Fin ns → ℝ)
  -- The one-step-ahead forecast is the conditional expectation of y_{T+1} given Ψ_T
  -- which decomposes into the sum of conditional expectations weighted by state probabilities.
  (h_forecast_def : y_hat = ∑ s, prob s * E_cond s)
  -- The MS-ARMA model specification: for each regime s, the expected value follows the ARMA dynamics.
  (h_model : ∀ s, E_cond s = μ s + ρ s * y_T + θ s * ε_T) :
  y_hat = ∑ s, prob s * (μ s + ρ s * y_T + θ s * ε_T) := by
  sorry











theorem theorem_42819_problem {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V] :
  ∃ B : Set V, LinearIndependent F ((↑) : B → V) ∧ Submodule.span F B = ⊤ := by
  sorry



theorem theorem_43619_problem {F V : Type*} [Field F] [AddCommGroup V] [Module F V] (S : Set V) :
  LinearIndependent F (fun (v : S) => (v : V)) ↔
  ∀ (T : Finset V), (T : Set V) ⊆ S →
  ¬ ∃ (a : V → F), Finset.sum T (fun i => a i • i) = 0 ∧ ∃ i ∈ T, a i ≠ 0 := by
  sorry











theorem theorem_43721_problem (n : ℕ) :
  let φ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun z i =>
      if i.val % 2 = 0 then (z ⟨i.val / 2, by
        have h := i.isLt
        omega⟩).re
      else (z ⟨i.val / 2, by
        have h := i.isLt
        omega⟩).im
  (inferInstance : TopologicalSpace (EuclideanSpace ℂ (Fin n))) =
    TopologicalSpace.induced φ (inferInstance : TopologicalSpace (EuclideanSpace ℝ (Fin (2 * n)))) := by
  sorry

theorem theorem_43756_problem
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix n n ℝ) (B : Matrix m m ℝ)
  (hA : A.PosSemidef) (hB : B.PosSemidef)
  (Asqrt : Matrix n n ℝ) (hAsqrt : Asqrt.PosSemidef) (hAsqrt_sq : Asqrt ^ 2 = A)
  (Bsqrt : Matrix m m ℝ) (hBsqrt : Bsqrt.PosSemidef) (hBsqrt_sq : Bsqrt ^ 2 = B) :
  ConvexOn ℝ Set.univ (fun (X : Matrix m n ℝ) =>
    let Y := Bsqrt * X * Asqrt
    (Y * Y.transpose).trace) := by
  sorry





theorem theorem_43237_problem
  {LatentSpace : Type*}
  (p q likelihood : LatentSpace → ℝ)
  (hp_pos : ∀ z, 0 < p z)
  (hq_pos : ∀ z, 0 < q z)
  (hl_pos : ∀ z, 0 < likelihood z)
  (E : (LatentSpace → ℝ) → ℝ)
  (h_lin : ∀ f g, E (fun z ↦ f z + g z) = E f + E g)
  (h_neg : ∀ f, E (fun z ↦ - f z) = - E f)
  (KL : ℝ)
  (h_KL : KL = E (fun z ↦ Real.log (q z) - Real.log (p z)))
  (L_rec : LatentSpace → ℝ)
  (h_L_rec : ∀ z, L_rec z = - Real.log (likelihood z))
  (ELBO : ℝ)
  (h_ELBO : ELBO = E (fun z ↦ Real.log (likelihood z * p z) - Real.log (q z))) :
  E L_rec + KL = - ELBO := by
  sorry

theorem theorem_43620_problem
  (I : Set ℝ)
  (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
  (v0 : EuclideanSpace ℝ (Fin 3))
  (t0 : ℝ)
  (ht0 : t0 ∈ I)
  (h_diff : DifferentiableOn ℝ alpha I)
  (h_cond : ∀ t ∈ I, inner (alpha t - alpha t0) v0 = (0 : ℝ)) :
  alpha '' I ⊆ {p | inner (p - alpha t0) v0 = (0 : ℝ)} := by
  sorry









theorem theorem_44231_problem (X : Type*)
  (f_n g_n : ℕ → X → ℝ) (f g : X → ℝ)
  (h_funif : TendstoUniformly f_n f Filter.atTop)
  (h_gunif : TendstoUniformly g_n g Filter.atTop)
  (h_eq : ∀ n x, f_n n x = g_n n x) :
  ∀ x, f x = g x := by
  sorry



theorem theorem_44388_problem
  {𝕜 : Type*} [Field 𝕜]
  {V₁ V₂ W : Type*}
  [AddCommGroup V₁] [Module 𝕜 V₁]
  [AddCommGroup V₂] [Module 𝕜 V₂]
  [AddCommGroup W] [Module 𝕜 W]
  (ρ : V₁ →ₗ[𝕜] V₂ →ₗ[𝕜] W)
  (m n : ℕ)
  (x : Fin m → V₁)
  (y : Fin n → V₂)
  (lam : Fin m → 𝕜)
  (mu : Fin n → 𝕜) :
  ρ (∑ i : Fin m, lam i • x i) (∑ j : Fin n, mu j • y j) =
  ∑ i : Fin m, ∑ j : Fin n, (lam i * mu j) • ρ (x i) (y j) := by
  sorry













theorem theorem_45228_problem
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
  (B_star : Set (NormedSpace.Dual ℂ X))
  (hB : B_star = Metric.closedBall 0 1)
  (Z : Set (WeakDual ℂ X))
  (hZ_sub : (Z : Set (NormedSpace.Dual ℂ X)) ⊆ B_star)
  (hZ_closed : IsClosed Z)
  (τ : WeakDual ℂ X → (X → ℂ))
  (hτ : τ = fun f x ↦ (f : NormedSpace.Dual ℂ X) x) :
  IsClosed (τ '' Z) := by
  sorry











theorem theorem_45195_problem :
  Filter.Tendsto (fun (n : ℕ) => Real.sqrt (1 + (n : ℝ) ^ 2)) Filter.atTop Filter.atTop := by
  sorry



theorem theorem_44820_problem (n : ℕ) (a x y : Fin n → ℝ) (b θ : ℝ)
  (hθ : 0 < θ ∧ θ < 1)
  (h1 : 0 ≤ Matrix.dotProduct a x + b)
  (h2 : 0 ≤ Matrix.dotProduct a y + b) :
  (Matrix.dotProduct a x + b) ^ θ * (Matrix.dotProduct a y + b) ^ (1 - θ) ≤
  θ * ((Matrix.dotProduct a x + b) / θ) + (1 - θ) * ((Matrix.dotProduct a y + b) / (1 - θ)) := by
  sorry











theorem theorem_45975_problem
  (K : Type*) [Field K]
  (V W : Type*) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (n m : ℕ)
  (U : Basis (Fin n) K V)
  (B : Basis (Fin m) K W)
  (T : V →ₗ[K] W)
  (M : Matrix (Fin m) (Fin n) K)
  (hM : M = LinearMap.toMatrix U B T) :
  ∀ (i : Fin m) (j : Fin n), M i j = (B.repr (T (U j))) i := by
  sorry



theorem theorem_45887_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [CommRing R]
  (A : Matrix n (Fin 1) R)
  (x : Matrix (Fin 1) n R)
  (b : Matrix (Fin 1) (Fin 1) R) :
  A.transpose * x.transpose * b = b * x * A := by
  sorry

















theorem theorem_46213_problem (n : ℕ) (hn : n ≠ 0)
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (C : Matrix (Fin n) (Fin n) ℝ)
  (hC : C = A * B - B * A) :
  ¬ IsNilpotent ((1 : Matrix (Fin n) (Fin n) ℝ) - C) := by
  sorry

theorem theorem_46503_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  (T : E →ₗ[𝕜] F)
  (h : IsClosed (T.graph : Set (E × F))) :
  Continuous T := by
  sorry





theorem theorem_46887_problem (R : Type*) [CommRing R] (I : Ideal R)
  (M : Type*) [AddCommGroup M] [Module R M]
  (h_fg : Module.Finite R M)
  (h_IM : I • (⊤ : Submodule R M) = ⊤)
  (h_jac : I ≤ Ideal.jacobson ⊥) :
  (⊤ : Submodule R M) = ⊥ := by
  sorry



theorem theorem_46943_problem (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
  (e f : V) :
  (TensorProduct.comm F V V) (e ⊗ₜ[F] e + f ⊗ₜ[F] f) = e ⊗ₜ[F] e + f ⊗ₜ[F] f := by
  sorry



theorem theorem_46438_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (V : Submodule ℝ E) (hV : IsClosed (V : Set E))
  (f : ℝ → E) (hf : Differentiable ℝ f)
  (h_ortho : ∀ t, ∀ v ∈ V.orthogonal, inner (deriv f t) v = (0 : ℝ))
  (h_init : f 0 ∈ V) :
  ∀ t, f t ∈ V := by
  sorry

theorem theorem_46679_problem
  (n : ℕ)
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (f g x y : Fin n → ℝ)
  (C : Matrix (Fin n) (Fin n) ℂ)
  (h z : Fin n → ℂ)
  (hC : C = A.map Complex.ofReal + Complex.I • B.map Complex.ofReal)
  (hh : h = fun i => Complex.mk (f i) (g i))
  (hz : z = fun i => Complex.mk (x i) (y i)) :
  C.mulVec z = h ↔
  (Matrix.fromBlocks A (-B) B A).mulVec (Sum.elim x y) = Sum.elim f g := by
  sorry

theorem theorem_46788_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (u : ℝ → E) (t : ℝ)
  (h : DifferentiableAt ℝ u t) :
  deriv (fun x => ‖u x‖^2) t = 2 * inner (u t) (deriv u t) := by
  sorry

theorem theorem_46372_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [CommRing R]
  (A B C D : Matrix n n R)
  (hB : IsUnit B)
  (hC : IsUnit C)
  (hD : IsUnit D)
  (h_sum : IsUnit (B⁻¹ + C⁻¹ - D⁻¹))
  (h_eq : (B⁻¹ + C⁻¹ - D⁻¹) * A = 1) :
  A = (B⁻¹ + C⁻¹ - D⁻¹)⁻¹ := by
  sorry

theorem theorem_46386_problem 
  (m N p : ℕ) 
  (n : Fin N → ℕ) 
  (Y : Fin m → (j : Fin N) → Fin (n j) → ℝ)
  (beta0 : Fin m → ℝ)
  (beta : Fin p → Fin m → ℝ)
  (x : Fin p → (j : Fin N) → Fin (n j) → ℝ)
  (u_group : Fin m → Fin N → ℝ)
  (u_indiv : Fin m → (j : Fin N) → Fin (n j) → ℝ)
  (epsilon : Fin m → (j : Fin N) → Fin (n j) → ℝ)
  (h_model : ∀ (h : Fin m) (j : Fin N) (i : Fin (n j)), 
    Y h j i = beta0 h + (∑ k : Fin p, beta k h * x k j i) + u_group h j + u_indiv h j i + epsilon h j i) :
  ∀ (h : Fin m) (j : Fin N) (i : Fin (n j)), 
    Y h j i = beta0 h + (∑ k : Fin p, beta k h * x k j i) + u_group h j + u_indiv h j i + epsilon h j i := by
  sorry











theorem theorem_46442_problem (x : ℝ) (hx : x ≠ 0)
  (A B : Matrix (Fin 2) (Fin 2) ℝ)
  (hA : A = !![0, 1/x; 1/x, 0])
  (hB : B = !![0, x; x, 0]) :
  A * B = 1 := by
  sorry



theorem theorem_47173_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (n : ℕ)
  (T : V →ₗ[F] V)
  (evals : Fin n → F)
  (e : Basis (Fin n) F V)
  (h_distinct : Function.Injective evals)
  (h_eigen : ∀ i, T (e i) = evals i • e i)
  (W : Submodule F V)
  (hW : ∀ i, e i ∈ W) :
  ∀ v ∈ W, T v ∈ W := by
  sorry

theorem theorem_47543_problem (n : ℕ) (γ : ℝ → Matrix (Fin n) (Fin n) ℝ)
  (h_cont : Continuous γ) (h_det : Matrix.det (γ 0) = 1) :
  ∃ ε > 0, ∀ t, |t| < ε → Matrix.det (γ t) ≠ 0 := by
  sorry

theorem theorem_46331_problem (m n : ℕ) (C : Set (Fin m → ℝ))
  (hC : Convex ℝ C) (f : (Fin m → ℝ) →ᵃ[ℝ] (Fin n → ℝ)) :
  Convex ℝ (f '' C) := by
  sorry

theorem theorem_47325_problem (A B C D E : Fin 3 → ℝ) :
  (∃ P : Fin 3 → ℝ, 
    (∃ lam : ℝ, lam ∈ Set.Icc 0 1 ∧ P = A + lam • (B - A)) ∧ 
    (∃ α : ℝ, α ∈ Set.Icc 0 1 ∧ ∃ β : ℝ, β ∈ Set.Icc 0 1 ∧ P = C + α • (D - C) + β • (E - C))) ↔ 
  (∃ lam : ℝ, lam ∈ Set.Icc 0 1 ∧ ∃ α : ℝ, α ∈ Set.Icc 0 1 ∧ ∃ β : ℝ, β ∈ Set.Icc 0 1 ∧ 
    A + lam • (B - A) = C + α • (D - C) + β • (E - C)) := by
  sorry

theorem theorem_47282_problem
  (P₁ P₂ u₁ v₁ u₂ v₂ : Fin 3 → ℝ) :
  (∃ x : Fin 3 → ℝ, (∃ t k : ℝ, x = P₁ + t • u₁ + k • v₁) ∧ (∃ s p : ℝ, x = P₂ + s • u₂ + p • v₂)) ↔
  (Matrix.transpose (Matrix.of ![u₁, v₁, -u₂, -v₂])).rank =
  (Matrix.transpose (Matrix.of ![u₁, v₁, -u₂, -v₂, P₂ - P₁])).rank := by
  sorry



theorem theorem_47229_problem
  (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (h_diff : DifferentiableAt ℝ f x)
  (hx : x ≠ 0)
  (hf : f x ≠ 0) :
  (norm (fderiv ℝ f x) * norm x) / abs (f x) = (norm x * norm (gradient f x)) / abs (f x) := by
  sorry







theorem theorem_47707_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (v w : E) (lam : ℂ) :
  Complex.abs lam ^ 2 * ‖v‖ ^ 2 - 2 * (lam * inner v w).re + ‖w‖ ^ 2 ≤
  Complex.abs lam ^ 2 * ‖v‖ ^ 2 + 2 * Complex.abs lam * Complex.abs (inner v w) + ‖w‖ ^ 2 := by
  sorry





