import Mathlib
import Mathlib.Tactic



theorem theorem_125809_problem
  (F : Type*) [Field F]
  (n m : ℕ)
  (A : (Fin n → F) →ₗ[F] (Fin m → F)) :
  FiniteDimensional.finrank F (LinearMap.ker A) +
  FiniteDimensional.finrank F (LinearMap.range A) = n := by
  sorry

theorem theorem_125742_problem
  (H1 H2 : ℝ → ℂ)
  (a : ℝ)
  (ha : 1 < a)
  (H : ℝ → ℂ)
  (hH : H = fun f ↦ H1 f * H2 f)
  (H1' : ℝ → ℂ)
  (hH1' : H1' = fun f ↦ H1 (a * f - (a - 1) * 1000))
  (H2' : ℝ → ℂ)
  (hH2' : H2' = fun f ↦ H2 (a * f - (a - 1) * 1000))
  (H' : ℝ → ℂ)
  (hH' : H' = fun f ↦ H1' f * H2' f)
  (h_diff1 : DifferentiableAt ℝ H1 1000)
  (h_diff2 : DifferentiableAt ℝ H2 1000) :
  deriv H' 1000 = a * deriv H 1000 := by
  sorry











theorem theorem_126520_problem (x y : ℝ → ℝ)
  (hx : Differentiable ℝ x)
  (hy : Differentiable ℝ y)
  (h1 : ∀ t, deriv x t = 2 * x t - y t + 16 * Real.exp (-t))
  (h2 : ∀ t, deriv y t = 3 * x t - 2 * y t - 8 * t) :
  ∃ c₁ c₂ : ℝ, ∀ t,
    x t = (1/2) * Real.exp (-t) * (-16 * (Real.exp t + 1) * t + c₁ * (3 * Real.exp (2 * t) - 1) - c₂ * Real.exp (2 * t) - 24 + c₂) ∧
    y t = (1/2) * (-32 * t - 3 * Real.exp (-t) * (16 * t + 8 + c₁ - c₂) + (3 * c₁ - c₂) * Real.exp t + 16) := by
  sorry



theorem theorem_126643_problem (a b c x y z : ℝ) (h : a ≠ 0) :
  a * x^2 + 2 * b * x * y + 2 * c * x * z = 
  a * (x + (b / a) * y + (c / a) * z)^2 - (b^2 / a) * y^2 - (c^2 / a) * z^2 - (2 * b * c / a) * y * z := by
  sorry

theorem theorem_127104_problem
  (y : ℕ → ℕ → ℝ)
  (h : ∀ n k, y n k = if n = k ∨ n = k + 1 then 1 else 0) :
  LinearIndependent ℝ y := by
  sorry



theorem theorem_126610_problem
  (B C : Matrix (Fin 2) (Fin 2) ℝ)
  (x : ℝ)
  (A : Matrix (Fin 2) (Fin 2) ℝ)
  (hA : A = (1 + x • C) * B * (1 + x • C.transpose)) :
  A.det = B.det * (1 + C.trace * x + C.det * x^2)^2 := by
  sorry













theorem theorem_127029_problem
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (b : OrthonormalBasis ι ℝ E)
  (vals : ι → ℝ)
  (P O : E →ₗ[ℝ] E)
  (hP : ∀ i, P (b i) = vals i • b i)
  (hO : ∀ i, vals i > 0 → O (b i) = b i) :
  O.comp P = P := by
  sorry

theorem theorem_127141_problem
  (n : ℕ)
  (K : Type*) [Field K]
  (S : Set (Matrix (Fin n) (Fin n) K))
  (hS_id : (1 : Matrix (Fin n) (Fin n) K) ∈ S)
  (A : Matrix (Fin n) (Fin n) K)
  (hA_in : A ∈ S)
  (hA_min : ∀ B ∈ S, (1 - A).rank ≤ (1 - B).rank) :
  A = 1 := by
  sorry

theorem theorem_127031_problem
  (n : ℕ)
  (c : Fin n → ℝ)
  (s : Fin n → ℝ)
  (h_perm : ∃ σ : Equiv.Perm (Fin n), s = c ∘ σ)
  (h_sort : Antitone s)
  (hn : n > 0) :
  sSup {y | ∃ (x : Fin n → ℝ), (∀ i, x i = 0 ∨ x i = 1) ∧ (∑ i, x i ≥ 1) ∧
    y = (∑ i, c i * x i) / Real.sqrt (∑ i, x i)} =
  sSup {y | ∃ k : Fin n, y = (∑ i in Finset.Iic k, s i) / Real.sqrt ((Finset.Iic k).card : ℝ)} := by
  sorry



theorem theorem_127188_problem
  (K : Type*) [Field K]
  (C : Type*) [AddCommGroup C] [Module K C] [FiniteDimensional K C]
  (D : Type*) [AddCommGroup D] [Module K D] [FiniteDimensional K D]
  (B_C : LinearMap.BilinForm K C)
  (B_D : LinearMap.BilinForm K D)
  (F : C →ₗ[K] D)
  (h : ∃ (I : Type*) (X : I → C),
    (Submodule.span K (Set.range X) = ⊤) ∧
    (Submodule.span K (Set.range (fun i => F (X i))) = ⊤) ∧
    (∀ i j : I, B_C (X i) (X j) = B_D (F (X i)) (F (X j)))) :
  ∀ v w : C, B_C v w = B_D (F v) (F w) := by
  sorry



theorem theorem_127757_problem (m n : ℕ) (A B : Matrix (Fin m) (Fin n) ℝ)
  (h : ∀ u : Fin n → ℝ, Matrix.mulVec A u = Matrix.mulVec B u) :
  A = B := by
  sorry







theorem theorem_127554_problem
  (K : Type*) [Field K]
  (X Y : Type*)
  [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y] :
  Nonempty (X ≃ₗ[K] Y) ↔ Nonempty ((X × X) ≃ₗ[K] (Y × Y)) := by
  sorry



theorem theorem_127411_problem
  (Point Line Conic : Type)
  (mem_conic : Point → Conic → Prop)
  (is_tangent : Line → Conic → Prop)
  (tangent_at : Line → Conic → Point → Prop)
  (polar : Conic → Point → Line)
  (is_ellipse : Conic → Prop)
  (Gamma1 Gamma2 : Conic)
  (h_ell1 : is_ellipse Gamma1)
  (h_ell2 : is_ellipse Gamma2)
  (Gamma3 : Set Point)
  -- Definition: Gamma3 is the polar reciprocal of Gamma2 w.r.t Gamma1.
  -- A point is in Gamma3 iff its polar w.r.t Gamma1 is tangent to Gamma2.
  (h_Gamma3_def : ∀ P, P ∈ Gamma3 ↔ is_tangent (polar Gamma1 P) Gamma2)
  -- Geometric Property: The polar of a point on an ellipse is the tangent at that point.
  (h_polar_tangent : ∀ (C : Conic) (P : Point), 
    is_ellipse C → mem_conic P C → tangent_at (polar C P) C P)
  -- Geometric Property: Tangent lines are unique at a point.
  (h_tangent_unique : ∀ (L1 L2 : Line) (C : Conic) (P : Point), 
    tangent_at L1 C P → tangent_at L2 C P → L1 = L2)
  (T : Point)
  -- T is in the intersection of Gamma1 and Gamma3
  (h_T_G1 : mem_conic T Gamma1)
  (h_T_G3 : T ∈ Gamma3)
  (L : Line)
  -- L is the tangent to Gamma1 at T
  (h_L_tan : tangent_at L Gamma1 T) :
  -- Conclusion: L is tangent to Gamma2
  is_tangent L Gamma2 := by
  sorry



theorem theorem_127752_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  (A B : V →L[𝕜] V) :
  ‖A.comp B‖ ≤ ‖A‖ * ‖B‖ := by
  sorry













theorem theorem_127914_problem (a r s eta eta' eta'' : ℝ) :
  ∃ (b u : ℝ) (ρ : ℝ → ℝ),
    (∃ c₂ c₁ c₀ : ℝ, ∀ l, ρ l = c₂ * l^2 + c₁ * l + c₀) ∧
    ∀ h k l : ℝ,
      a * (h + r * k + s * l)^2 + eta * k^2 + eta' * k * l + eta'' * l^2 =
      a * (h + r * k + s * l)^2 + b * (k + u * l)^2 + ρ l := by
  sorry







theorem theorem_127894_problem (m n p q : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (B : Matrix (Fin n) (Fin p) ℝ)
  (C : Matrix (Fin p) (Fin q) ℝ)
  (h : Matrix.rank B = min n p) :
  Matrix.rank (A * B * C) ≤ min (Matrix.rank A) (min (Matrix.rank B) (Matrix.rank C)) := by
  sorry

theorem theorem_128029_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (x y : V) :
  inner (Complex.I • x) y = Complex.I * inner x y := by
  sorry



theorem theorem_128694_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (A L : Matrix n n ℂ)
  (hL : L = 1 + A)
  (hA_diag : ∀ i, A i i = 0)
  (hA_sum : A + A.conjTranspose = 0)
  (hA_prod : A * A.conjTranspose = 0) :
  L * L.conjTranspose = 1 := by
  sorry









theorem theorem_128918_problem
  (n : ℕ)
  (f : (Fin n → ℝ) → ℝ)
  (u₀ : Fin n → ℝ)
  (h_diff : DifferentiableAt ℝ f u₀)
  (h_cond : ∀ (v : Fin n → ℝ) (t : ℝ), t * (fderiv ℝ f u₀ v) ≥ 0) :
  ∀ (v : Fin n → ℝ), fderiv ℝ f u₀ v = 0 := by
  sorry



theorem theorem_128887_problem (n m r : ℕ) (A : Matrix (Fin n) (Fin m) ℝ) :
  Matrix.rank A ≤ r ↔ ∃ V : Submodule ℝ (Fin n → ℝ), FiniteDimensional.finrank ℝ V ≤ r ∧ ∀ j, (fun i => A i j) ∈ V := by
  sorry

theorem theorem_128899_problem
  (n : ℕ)
  (F A : Matrix (Fin n) (Fin n) ℝ)
  (nabla : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
  (h_nabla : ∀ R, nabla R = F * R - R * A)
  (R₁ R₂ : Matrix (Fin n) (Fin n) ℝ) :
  nabla (R₁ + R₂) = nabla R₁ + nabla R₂ := by
  sorry

theorem theorem_129299_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) [Invertible A] :
  (∀ i j, 0 ≤ A⁻¹ i j) ↔
  (∀ b : Fin n → ℝ, (∀ i, 0 ≤ b i) → ∀ i, 0 ≤ (Matrix.mulVec A⁻¹ b) i) := by
  sorry





theorem theorem_128875_problem
  {L : Type*} [NontriviallyNormedField L]
  {B : Type*} [NormedAddCommGroup B] [NormedSpace L B]
  {B' : Type*} [NormedAddCommGroup B'] [NormedSpace L B']
  (hB' : CompleteSpace B')
  (T : B ≃L[L] B') :
  CompleteSpace B := by
  sorry



theorem theorem_128995_problem
  {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  (T : ℕ → X →L[𝕜] X)
  (h : ∀ x : X, ∃ y : X, ∀ φ : X →L[𝕜] 𝕜, Filter.Tendsto (fun n ↦ φ (T n x)) Filter.atTop (nhds (φ y))) :
  ∃ C, ∀ n, ‖T n‖ ≤ C := by
  sorry

theorem theorem_129190_problem (m k : ℕ)
  (U : Matrix (Fin m) (Fin k) ℝ)
  (V : Matrix (Fin m) (Fin k) ℝ) :
  Matrix.det (1 + U * V.transpose) = Matrix.det (1 + V.transpose * U) := by
  sorry



theorem theorem_129672_problem (n m : ℕ) (hm : 0 < m)
  (a : Fin m → EuclideanSpace ℝ (Fin n))
  (b : Fin m → ℝ)
  (x : EuclideanSpace ℝ (Fin n)) :
  (∑ k : Fin m, (1 / m : ℝ) • ((inner (a k) x - b k) • a k)) =
  (1 / m : ℝ) • ∑ k : Fin m, ((inner (a k) x - b k) • a k) := by
  sorry

theorem theorem_129916_problem 
  (M : Type*) [Ring M] 
  (E : Fin 2 → Fin 2 → M) 
  (a x : M)
  (hE : ∀ i j k l : Fin 2, E i j * E k l = if j = k then E i l else 0)
  (hx : x = (E 0 0 + E 0 1) * a * (E 0 0 + E 1 0) + (E 1 0 + E 1 1) * a * (E 0 1 + E 1 1)) :
  ∀ i j : Fin 2, x * E i j = E i j * x := by
  sorry





theorem theorem_129490_problem (MW : Bool → Bool → Bool → ℝ) :
  ∃ α δ₁ δ₂ δ₃ δ₄ δ₅ δ₆ δ₇ : ℝ,
  ∀ (e_i c_c p_t : Bool),
  let E_i : ℝ := if e_i then 1 else 0
  let C_c : ℝ := if c_c then 1 else 0
  let P_t : ℝ := if p_t then 1 else 0
  MW e_i c_c p_t = α + δ₁ * E_i + δ₂ * C_c + δ₃ * P_t +
                   δ₄ * (E_i * P_t) + δ₅ * (C_c * P_t) + δ₆ * (C_c * E_i) +
                   δ₇ * (E_i * C_c * P_t) := by
  sorry







theorem theorem_130115_problem
  (t : ℕ → ℝ → ℝ)
  (f : ℝ → ℝ)
  (h_cont : ∀ n, ContinuousOn (t n) (Set.Icc 0 1))
  (h_unif : TendstoUniformlyOn (fun N x ↦ ∑ n in Finset.range N, t n x) f Filter.atTop (Set.Icc 0 1)) :
  ContinuousOn f (Set.Icc 0 1) := by
  sorry

theorem theorem_130290_problem 
  (I : ℕ → Set ℝ)
  (hI : ∀ n : ℕ, 0 < n → I n = Set.Ioo (1 / (n : ℝ)) 1)
  (S : Set ℝ)
  (hS : S = ⋃ (n : ℕ) (_ : 0 < n), I n) :
  S = Set.Ioo 0 1 := by
  sorry

theorem theorem_129909_problem
  (m n : ℕ)
  (G : Matrix (Fin m) (Fin n) ℝ)
  (d : Fin m → ℝ)
  (a : ℝ)
  (ha : 0 < a)
  (f : (Fin n → ℝ) → ℝ)
  (hf : ∀ x, f x = (1 / 2) * Matrix.dotProduct (G.mulVec x - d) (G.mulVec x - d) +
                   (a / 2) * Matrix.dotProduct x x)
  (x_star : Fin n → ℝ)
  (h_min : ∀ x, f x_star ≤ f x) :
  (G.transpose * G + a • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec x_star = G.transpose.mulVec d := by
  sorry









theorem theorem_130268_problem
  {𝕜 V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  (h_inf : ¬ FiniteDimensional 𝕜 V)
  (h_basis : ∃ (ι : Type*) (_ : Countable ι), Nonempty (Basis ι 𝕜 V)) :
  ¬ CompleteSpace V := by
  sorry



theorem theorem_130657_problem
  (d : ℕ)
  (D T : Type*) -- D: Distributions, T: Test functions
  [AddCommGroup D] -- Distributions form an additive group
  (pair : D → T → ℝ) -- The pairing <u, φ>
  (partial_D : Fin d → D → D) -- Partial derivative on distributions
  (partial_T : Fin d → T → T) -- Partial derivative on test functions
  -- Hypothesis: Linearity of the pairing with respect to the distribution
  (h_linear : ∀ (u v : D) (φ : T), pair (u + v) φ = pair u φ + pair v φ)
  -- Hypothesis: Definition of distributional derivative
  (h_partial_def : ∀ (i : Fin d) (u : D) (φ : T), pair (partial_D i u) φ = - pair u (partial_T i φ))
  (u : Fin d → D) -- Vector valued distribution
  (div_u : D) -- The divergence of u
  -- Condition: Definition of divergence as sum of partials
  (h_div_def : div_u = ∑ i, partial_D i (u i)) :
  -- Conclusion: The action formula derived in the solution
  ∀ φ : T, pair div_u φ = - ∑ i, pair (u i) (partial_T i φ) := by
  sorry









theorem theorem_130703_problem
  (m n k : ℕ)
  (h_mn : m > n)
  (G : Matrix (Fin m) (Fin n) ℝ)
  (h_rank : G.rank = n)
  (F : Matrix (Fin n) (Fin m) ℝ)
  (h_F : F * G = 1)
  (K : Matrix (Fin m) (Fin k) ℝ)
  (h_K : G.transpose * K = 0)
  (H : Matrix (Fin k) (Fin m) ℝ)
  (h_H : H = K.transpose) :
  H * G = 0 := by
  sorry

theorem theorem_130646_problem
  (n m k : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (B : Matrix (Fin n) (Fin m) ℝ)
  (D : Matrix (Fin n) (Fin k) ℝ)
  (R : Matrix (Fin m) (Fin m) ℝ)
  (Q : Matrix (Fin n) (Fin n) ℝ)
  (P P_dot : Matrix (Fin n) (Fin n) ℝ)
  (x : Matrix (Fin n) (Fin 1) ℝ)
  (u : Matrix (Fin m) (Fin 1) ℝ)
  (μ : ℝ)
  (hR_inv : Invertible R)
  (hP_symm : P.IsSymm)
  -- Note: The Riccati equation is defined with the negative sign on P_dot to be consistent
  -- with the solution's derivation and the target result, correcting the sign in the problem description.
  (h_riccati : -P_dot = P * A + A.transpose * P - P * (B * R⁻¹ * B.transpose - μ • (D * D.transpose)) * P + Q) :
  let f_partial_t := (1 / 2 : ℝ) * (x.transpose * P_dot * x) 0 0
  let f_grad_T := x.transpose * P
  let drift_term := f_partial_t + (f_grad_T * (A * x + B * u)) 0 0 + (1 / 2 : ℝ) * Matrix.trace (D.transpose * P * D)
  let target_term := (1 / 2 : ℝ) * (
    (x.transpose * (P * B * R⁻¹ * B.transpose * P - Q) * x) 0 0 +
    2 * (x.transpose * P * B * u) 0 0 +
    Matrix.trace (D.transpose * P * D) -
    μ * (x.transpose * P * D * D.transpose * P * x) 0 0
  )
  drift_term = target_term := by
  sorry



theorem theorem_130953_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (T : H →L[ℝ] H)
  (h : ∀ x y : H, ‖T (x - y)‖ = ‖ContinuousLinearMap.adjoint T (x - y)‖) :
  ContinuousLinearMap.adjoint T * T = T * ContinuousLinearMap.adjoint T := by
  sorry







theorem theorem_130824_problem
  {n : ℕ} {R : Type*} [CommRing R]
  (i j : Fin n.succ) :
  let D_ij := fun (M : Matrix (Fin n.succ) (Fin n.succ) R) ↦ (M.submatrix i.succAbove j.succAbove).det
  let f := fun (M : Matrix (Fin n.succ) (Fin n.succ) R) ↦ M i j * D_ij M
  ∀ (k : Fin n.succ) (A : Matrix (Fin n.succ) (Fin n.succ) R) (v w : Fin n.succ → R) (c : R),
    (f (A.updateRow k (v + w)) = f (A.updateRow k v) + f (A.updateRow k w)) ∧
    (f (A.updateRow k (c • v)) = c * f (A.updateRow k v)) := by
  sorry



theorem theorem_130964_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (x y z : V) (ρ : ℝ) (hρ : 0 < ρ) :
  inner y (x - z) + (ρ / 2) * ‖x - z‖^2 =
  (ρ / 2) * ‖(x - z) + (1 / ρ) • y‖^2 - (1 / (2 * ρ)) * ‖y‖^2 := by
  sorry







