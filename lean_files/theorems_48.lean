import Mathlib
import Mathlib.Tactic



theorem theorem_256551_problem
  (n₁ n₂ μ₁ μ₂ σ₁Sq σ₂Sq w : ℝ)
  (h_sum_n : n₁ + n₂ ≠ 0)
  (h_denom_W : n₁ * σ₁Sq + n₂ * σ₂Sq ≠ 0)
  (h_w : w ≠ 0) :
  let σ_B_sq := (μ₁ - μ₂)^2
  let σ_W_sq := (n₁ * σ₁Sq + n₂ * σ₂Sq) / (n₁ + n₂)
  let m₁ := w * μ₁
  let m₂ := w * μ₂
  let s₁Sq := w^2 * σ₁Sq
  let s₂Sq := w^2 * σ₂Sq
  let σ_B_proj_sq := (m₁ - m₂)^2
  let σ_W_proj_sq := (n₁ * s₁Sq + n₂ * s₂Sq) / (n₁ + n₂)
  let J_w := σ_B_proj_sq / σ_W_proj_sq
  J_w = σ_B_sq / σ_W_sq := by
  sorry





theorem theorem_256963_problem 
  (b : ℝ) 
  (hb : 1 < b)
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (T : E →ₗ[ℝ] E)
  (f : ℕ → E)
  (hf_nonzero : ∀ n, f n ≠ 0)
  (h_ratio : ∀ n, ‖T (f n)‖ / ‖f n‖ = n * b^(n - 2)) :
  ¬ ∃ M : ℝ, ∀ x : E, ‖T x‖ ≤ M * ‖x‖ := by
  sorry









theorem theorem_256951_problem
  (S : Set ℝ)
  (logJ : ℝ → ℝ)
  (E_logJ_perm : ℝ → ℝ)
  (sigma : ℝ → ℝ)
  (Gap : ℝ → ℝ)
  (kappa : ℝ)
  (hGap : ∀ s, Gap s = logJ s - E_logJ_perm s)
  (s_star : ℝ)
  (h_s_star_in_S : s_star ∈ S)
  (h_optimal : ∀ s ∈ S, Gap s - kappa * sigma s ≤ Gap s_star - kappa * sigma s_star) :
  ∀ s ∈ S, (logJ s - E_logJ_perm s) - kappa * sigma s ≤ (logJ s_star - E_logJ_perm s_star) - kappa * sigma s_star := by
  sorry



theorem theorem_257355_problem (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) (c : Fin m → ℝ) :
  A.mulVec y = c ↔ A.mulVec y ≥ c ∧ -(A.mulVec y) ≥ -c := by
  sorry



theorem theorem_256913_problem
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (f : E × F → ℝ)
  (Dom : Set (E × F))
  (a : E) (b : F)
  (hDom : IsOpen Dom)
  (hab : (a, b) ∈ Dom)
  (hf : ContDiffOn ℝ ⊤ f Dom) :
  ∀ (x : E) (y : F),
    fderiv ℝ f (a, b) (x, y) =
    inner (gradient (fun u => f (u, b)) a) x +
    inner (gradient (fun v => f (a, v)) b) y := by
  sorry







theorem theorem_257442_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  {n : ℕ}
  (E : Basis (Fin n) K V)
  (F : Basis (Fin n) K V)
  (P : Matrix (Fin n) (Fin n) K)
  (hP : ∀ i, F i = ∑ j, (P j i) • E j)
  (v : V) :
  (E.repr v : Fin n → K) = P.mulVec (F.repr v) := by
  sorry



theorem theorem_257586_problem :
  ∃ (K : Type) (_ : Field K) (n : ℕ) (A : Matrix (Fin n) (Fin n) K),
    A ^ 2 = 0 ∧
    let H₁ := LinearMap.ker (Matrix.toLin' A)
    let H₂ : Submodule K (Fin n → K) := ⊤
    let m₁ := FiniteDimensional.finrank K H₁
    let m₂ := FiniteDimensional.finrank K H₂
    let p₁ := m₂ - m₁
    p₁ ≠ 1 := by
  sorry

theorem theorem_257519_problem
  (m n : ℕ)
  (hm : 0 < m)
  (c : Fin n → ℝ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b1 b2 : Fin m → ℝ)
  (y1 y2 : Fin m → ℝ)
  (h_diff : ∀ i : Fin m, i ≠ ⟨0, hm⟩ → b1 i = b2 i)
  (h_gt : b1 ⟨0, hm⟩ < b2 ⟨0, hm⟩)
  (h_opt1 : (∀ j, c j ≤ Matrix.vecMul y1 A j) ∧ 0 ≤ y1 ∧
    ∀ y, (∀ j, c j ≤ Matrix.vecMul y A j) ∧ 0 ≤ y → Matrix.dotProduct b1 y1 ≤ Matrix.dotProduct b1 y)
  (h_opt2 : (∀ j, c j ≤ Matrix.vecMul y2 A j) ∧ 0 ≤ y2 ∧
    ∀ y, (∀ j, c j ≤ Matrix.vecMul y A j) ∧ 0 ≤ y → Matrix.dotProduct b2 y2 ≤ Matrix.dotProduct b2 y) :
  y2 ⟨0, hm⟩ ≤ y1 ⟨0, hm⟩ := by
  sorry





theorem theorem_258037_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  (n : ℕ)
  (T : V →ₗ[K] W)
  (w : Basis (Fin n) K W)
  (h : ∀ i, ∃ v, T v = w i) :
  ∃ S : W →ₗ[K] V, T.comp S = LinearMap.id := by
  sorry

theorem theorem_257907_problem
  (Time : Type) [DecidableEq Time]
  (Pre : Set Time)
  (y2012 : Time)
  (gamma lambda : ℝ)
  -- E represents the expected outcome E[y | Treatment, t]
  (E : Bool → Time → ℝ)
  (h_y2012_pre : y2012 ∈ Pre)
  (h_exist_other : ∃ t ∈ Pre, t ≠ y2012)
  -- The regression model implies specific forms for expectations in the pretreatment period
  -- y = γ T + λ (T * I_{t=2012}) + ε
  (h_model_treated : ∀ t ∈ Pre, E true t = gamma + if t = y2012 then lambda else 0)
  (h_model_control : ∀ t ∈ Pre, E false t = 0)
  -- Parallel trends assumption: difference between treated and control is constant
  (h_parallel : ∀ t s, t ∈ Pre → s ∈ Pre →
    (E true t - E false t) = (E true s - E false s)) :
  lambda = 0 := by
  sorry

theorem theorem_258082_problem (n : ℕ) (x : Fin n → ℝ)
  (h_triangle : ∑ i, (x i)^2 > 0) :
  (fun i => x i / Real.sqrt (∑ j, (x j)^2)) ∈ { y : Fin n → ℝ | ∑ i, (y i)^2 = 1 } := by
  sorry











theorem theorem_258354_problem 
  {n : ℕ} 
  (Knot : Type) 
  (K : Knot)
  (A : Matrix (Fin n) (Fin n) ℤ)
  (mirror : Knot → Knot)
  (seifert : Knot → Matrix (Fin n) (Fin n) ℤ)
  (equivalent : Knot → Knot → Prop)
  -- Condition: A is the Seifert matrix of K
  (hA : seifert K = A)
  -- Condition: K_* (mirror image) has Seifert matrix -A^T
  (h_mirror_seifert : seifert (mirror K) = -A.transpose)
  -- Condition: K is amphichiral, meaning K is equivalent to K_*
  (h_amphichiral : equivalent K (mirror K))
  -- Context: Equivalent knots have S-equivalent Seifert matrices
  -- We define S-equivalence here as similarity by a unimodular matrix per the problem description
  (h_knot_theory : ∀ (k1 k2 : Knot), equivalent k1 k2 → 
    ∃ S : Matrix (Fin n) (Fin n) ℤ, IsUnit S.det ∧ seifert k1 * S = S * seifert k2) :
  -- Conclusion: A is S-equivalent to -A^T (exists unimodular S such that S⁻¹AS = -A^T)
  -- Note: S⁻¹AS = -A^T is equivalent to AS = S(-A^T) for unimodular S
  ∃ S : Matrix (Fin n) (Fin n) ℤ, IsUnit S.det ∧ A * S = S * (-A.transpose) := by
  sorry



theorem theorem_258395_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (x y z : V)
  (a b α β γ : ℝ)
  (hx : ‖x‖ = 1)
  (hy : ‖y‖ = 1)
  (hz : ‖z‖ = 1)
  (h_eq : z = a • x + b • y)
  (hα : α = inner x y)
  (hβ : β = inner x z)
  (hγ : γ = inner y z) :
  (α - 1) * (b - a) = β - γ := by
  sorry







theorem theorem_258400_problem
  (X : Type*) [MetricSpace X] [CompactSpace X]
  (f_seq : ℕ → C(X, ℝ)) (f : C(X, ℝ)) :
  Filter.Tendsto f_seq Filter.atTop (nhds f) ↔
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x : X, |f_seq n x - f x| < ε := by
  sorry



theorem theorem_258844_problem (R : ℝ) (hR : 0 < R) :
  let z : ℝ → ℂ := fun θ ↦ R * Complex.exp (θ * I)
  let f : ℂ → ℂ := fun w ↦ w⁻¹
  ∫ θ in (0)..(2 * π), f (z θ) * deriv z θ = 2 * π * I := by
  sorry





theorem theorem_259285_problem (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, (∃ q : ℚ, (q : ℝ) = x) → f x = 0)
  (h2 : ∀ x : ℝ, (¬ ∃ q : ℚ, (q : ℝ) = x) → f x = 1) :
  ∀ x : ℝ, ¬ ContinuousAt f x := by
  sorry





theorem theorem_258922_problem
  (z : ℕ+ → ℂ)
  (a : ℕ+ → ℝ)
  (c : ℕ+ → ℝ)
  (ha : ∀ n, a n = ((n : ℝ) + 1) / n)
  (hc : ∀ n, c n = a n * Complex.abs (z n)) :
  (⨆ n, c n) ≤ (⨆ m, a m) * (⨆ k, Complex.abs (z k)) := by
  sorry









theorem theorem_259459_problem
  (n : ℕ)
  {R : Type*} [CommRing R]
  (A B E : Matrix (Fin n) (Fin n) R)
  (hE : E = 1) :
  Matrix.fromBlocks E A B E =
    (Matrix.fromBlocks (E - A * B) A 0 E) * (Matrix.fromBlocks E 0 B E) := by
  sorry



theorem theorem_259616_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (D : ContinuousMultilinearMap 𝕜 (fun _ : Fin 3 => E) 𝕜)
  (a b c : 𝕜 → E) (a' b' c' : E) (t : 𝕜)
  (ha : HasDerivAt a a' t)
  (hb : HasDerivAt b b' t)
  (hc : HasDerivAt c c' t) :
  HasDerivAt (fun t => D ![a t, b t, c t])
    (D ![a', b t, c t] + D ![a t, b', c t] + D ![a t, b t, c']) t := by
  sorry





















theorem theorem_261094_problem
  {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (J : E → E →L[ℝ] F)
  (hJ : Differentiable ℝ J)
  (x_k x_star : E) :
  ∫ t : ℝ in (0)..1, (J (x_k + t • (x_k - x_star))) (x_k - x_star) =
  (J x_k) (x_k - x_star) +
  ∫ t : ℝ in (0)..1, ((J (x_k + t • (x_k - x_star))) - J x_k) (x_k - x_star) := by
  sorry





theorem theorem_260710_problem
  (n : ℕ)
  (r c : Fin n → ℕ)
  (A B : Matrix (Fin n) (Fin n) ℕ)
  (h_consistent : ∑ i, r i = ∑ j, c j)
  (hAr : ∀ i, ∑ j, A i j = r i)
  (hAc : ∀ j, ∑ i, A i j = c j)
  (hBr : ∀ i, ∑ j, B i j = r i)
  (hBc : ∀ j, ∑ i, B i j = c j)
  (h_sub : ∀ (i j : Fin n), (i : ℕ) < n - 1 → (j : ℕ) < n - 1 → A i j = B i j) :
  A = B := by
  sorry

theorem theorem_260080_problem :
  let S : Set (ℕ → ℚ) := {f | ∀ n, f n = 0 ∨ f n = 1}
  let V := Submodule.span ℚ S
  ∃ (ι : Type) (_ : Basis ι ℚ V), ¬ Set.Countable (Set.univ : Set ι) := by
  sorry

theorem theorem_260741_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (h_inf : ¬ FiniteDimensional ℝ E) :
  ¬ IsCompact (Metric.closedBall (0 : E) 1) := by
  sorry



theorem theorem_260894_problem
  {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  (A : E →ₗ[ℝ] F) (b : F) (q : F → ℝ)
  (h_ker : LinearMap.ker A = ⊥)
  (h_q : StrictConvexOn ℝ (Set.range (fun x => A x + b)) q) :
  StrictConvexOn ℝ Set.univ (fun x => q (A x + b)) := by
  sorry





theorem theorem_261045_problem
  {F V W : Type*}
  [Field F]
  [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
  [FiniteDimensional F V]
  (T : V →ₗ[F] W) :
  FiniteDimensional.finrank F V =
  FiniteDimensional.finrank F (LinearMap.range T) +
  FiniteDimensional.finrank F (LinearMap.ker T) := by
  sorry











theorem theorem_261330_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [CommRing R]
  (C : ℕ → Matrix n n R)
  (H : Matrix n n R)
  (h_recurrence : ∀ m : ℕ, C (m + 1) = (1 - H) * C m) :
  ∀ m : ℕ, C m = (1 - H) ^ m * C 0 := by
  sorry

theorem theorem_260583_problem
  (A : Matrix (Fin 2) (Fin 2) ℝ)
  (B : Matrix (Fin 2) (Fin 1) ℝ)
  (C : Matrix (Fin 1) (Fin 2) ℝ)
  (hA : A = !![1, 0; 0, 1])
  (hB : B = !![0; 1])
  (hC : C = !![0, 1]) :
  ¬ ∃ (X : Matrix (Fin 1) (Fin 2) ℝ) (Y : Matrix (Fin 2) (Fin 1) ℝ), A = B * X + Y * C := by
  sorry

theorem theorem_261422_problem
  (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (f : V →ₗ[F] V)
  (h : ∀ v : V, ∃ c : F, f v = c • v) :
  ∃ c : F, f = c • LinearMap.id := by
  sorry



theorem theorem_261451_problem (n : ℕ) (v : Fin n → ℂ) (hn : n > 0) :
  let A := Matrix.circulant v
  let ω := Complex.exp (-2 * (Real.pi : ℂ) * Complex.I / n)
  let w : Fin n → ℂ := fun k => ∑ j, v j * ω ^ ((j : ℕ) * (k : ℕ))
  A.det = ∏ k, w k := by
  sorry





theorem theorem_261477_problem
  (n m : ℕ)
  (f : (Fin n → ℝ) → (Fin m → ℝ))
  (g : (Fin n → ℝ) → ℝ)
  (x₀ : Fin n → ℝ)
  (hf : DifferentiableAt ℝ f x₀)
  (hg : DifferentiableAt ℝ g x₀) :
  fderiv ℝ (fun x => g x • f x) x₀ =
  g x₀ • fderiv ℝ f x₀ + (fderiv ℝ g x₀).smulRight (f x₀) := by
  sorry





theorem theorem_261267_problem {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  (f : V →ₗ[F] W) (n : ℕ) (v_seq : Fin n → V)
  (h_indep : LinearIndependent F v_seq)
  (v : V)
  (h_not_span : v ∉ Submodule.span F (Set.range v_seq))
  (h_eq : ∃ i, f v = f (v_seq i)) :
  ¬ Function.Injective f := by
  sorry

theorem theorem_262025_problem (f : ℝ → ℝ) (h : Monotone f) :
  Set.Countable {x | ¬ ContinuousAt f x} := by
  sorry

theorem theorem_262106_problem (R : Matrix (Fin 3) (Fin 3) ℝ)
  (h : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
  R.det = 1 := by
  sorry





theorem theorem_262292_problem 
  (D : Set ℂ) (hD_open : IsOpen D) (hD_connected : IsConnected D)
  (f g : ℂ → ℂ) 
  (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
  (z_seq : ℕ → ℂ) (z₀ : ℂ)
  (hz_seq : ∀ n, z_seq n ∈ D)
  (hz₀ : z₀ ∈ D)
  (h_lim : Filter.Tendsto z_seq Filter.atTop (nhds z₀))
  (h_neq : ∀ n, z_seq n ≠ z₀)
  (h_val : ∀ n, f (z_seq n) = g (z_seq n)) :
  ∀ z ∈ D, f z = g z := by
  sorry









theorem theorem_262036_problem
  (F : Type*) [Field F]
  (V : Type*) [AddCommGroup V] [Module F V]
  (M : Set V)
  (M_zero : Set (Module.Dual F V))
  (hM_zero : M_zero = {ϕ | ∀ m ∈ M, ϕ m = 0})
  (M_zero_zero : Set V)
  (hM_zero_zero : M_zero_zero = {v | ∀ ϕ ∈ M_zero, ϕ v = 0})
  (τ : V →ₗ[F] Module.Dual F (Module.Dual F V))
  (hτ_def : ∀ (v : V) (ϕ : Module.Dual F V), τ v ϕ = ϕ v)
  (hτ_iso : Function.Bijective τ) :
  τ '' M_zero_zero = {f | ∀ ϕ ∈ M_zero, f ϕ = 0} := by
  sorry

