import Mathlib
import Mathlib.Tactic

theorem theorem_219689_problem (f : ℝ → ℝ) (t : ℝ)
  (h_smooth : ContDiff ℝ ⊤ f)
  (h_conv : HasSum (fun n : ℕ ↦ (deriv^[n] f t) / (n.factorial : ℝ)) (f (t + 1))) :
  f (t + 1) = ∑' n : ℕ, (deriv^[n] f t) / (n.factorial : ℝ) := by
  sorry





theorem theorem_219801_problem (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) (h : w ≠ 0) :
  gradient (fun x => ‖x‖) w = ‖w‖⁻¹ • w := by
  sorry

theorem theorem_219898_problem {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
  (hA : A.IsHermitian) (hB : B.IsHermitian)
  (h : ∀ x : Fin n → ℂ, Matrix.dotProduct (star x) x = 1 →
    Matrix.dotProduct (star x) (Matrix.mulVec (A - B) x) = 0) :
  A = B := by
  sorry

theorem theorem_220013_problem
  {H H' : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℝ H']
  (T : H →ₗ[ℝ] H')
  (h : ∀ x : H, ‖T x‖ = ‖x‖)
  (x y : H) :
  inner (T x) (T y) = (inner x y : ℝ) := by
  sorry





theorem theorem_220436_problem (k : ℝ) (hk : 0 < k) :
  LinearIndependent ℝ ![fun (x : ℝ) => Real.sin (k * x), fun (x : ℝ) => Real.cos (k * x)] := by
  sorry



theorem theorem_220098_problem
  (n k : ℕ)
  (v : Fin k → Fin n → ℝ)
  (α_weights : Fin k → ℝ)
  (c : Fin n → ℝ)
  (α_offset : ℝ) :
  let t := fun i => (∑ j : Fin n, c j * v i j) - α_offset
  let S_plus := Finset.univ.filter (fun i => t i > 0)
  let S_minus := Finset.univ.filter (fun i => t i < 0)
  |∑ i : Fin k, Real.sign (t i) * α_weights i| =
  |(∑ i in S_plus, α_weights i) - (∑ i in S_minus, α_weights i)| := by
  sorry



theorem theorem_220137_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (h_n : n > 0) :
  ∃ (z_opt : ℝ) (w_opt r_opt : Fin n → ℝ),
    (A.mulVec w_opt = r_opt) ∧
    (∑ i, w_opt i = 1) ∧
    (∀ i, z_opt ≤ r_opt i) ∧
    (∀ i, 0 ≤ w_opt i) ∧
    ∀ (z : ℝ) (w r : Fin n → ℝ),
      (A.mulVec w = r) →
      (∑ i, w i = 1) →
      (∀ i, z ≤ r i) →
      (∀ i, 0 ≤ w i) →
      z ≤ z_opt := by
  sorry

theorem theorem_220124_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (S : Set E) (x : E) (ε : ℝ)
  (h_conv : Convex ℝ S)
  (h_symm : ∀ s ∈ S, -s ∈ S)
  (h_ball : Metric.ball x ε ⊆ S) :
  Metric.ball 0 (ε / 2) ⊆ S := by
  sorry

theorem theorem_220546_problem
  (n : ℕ) (hn : n > 0)
  (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f) :
  let f₀ : ℝ → ℝ := fun _ ↦ 1 / Real.sqrt 2
  let f_k : ℕ → ℝ → ℝ := fun k x ↦ Real.cos (k * Real.pi * x)
  let g_k : ℕ → ℝ → ℝ := fun k x ↦ Real.sin (k * Real.pi * x)
  let S : Set (ℝ → ℝ) := {h | h = f₀ ∨ ∃ k ∈ Finset.Icc 1 n, h = f_k k ∨ h = g_k k}
  let W : Submodule ℝ (ℝ → ℝ) := Submodule.span ℝ S
  let inner : (ℝ → ℝ) → (ℝ → ℝ) → ℝ := fun u v ↦ ∫ x in (-1 : ℝ)..1, u x * v x
  let a₀ : ℝ := inner f f₀
  let a : ℕ → ℝ := fun i ↦ inner f (f_k i)
  let b : ℕ → ℝ := fun i ↦ inner f (g_k i)
  let P_W_f : ℝ → ℝ := fun x ↦ (a₀ / Real.sqrt 2) +
    (∑ i in Finset.Icc 1 n, a i * Real.cos (i * Real.pi * x)) +
    (∑ i in Finset.Icc 1 n, b i * Real.sin (i * Real.pi * x))
  P_W_f ∈ W ∧ ∀ w ∈ W, inner (f - P_W_f) w = 0 := by
  sorry









theorem theorem_220433_problem
  {m : Type*} [DecidableEq m] [Fintype m]
  {R : Type*} [CommRing R]
  (A : Matrix m m R)
  (h : A ^ 2 = A + 1)
  (n : ℕ) (hn : n > 0) :
  A ^ n = (Nat.fib n : R) • A + (Nat.fib (n - 1) : R) • 1 := by
  sorry

theorem theorem_220754_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (T : V →ₗ[K] V)
  (hT : ∃ k : ℕ, 0 < k ∧ T ^ k = 0) :
  ∃ (n : ℕ) (b : Basis (Fin n) K V),
    ∀ i j : Fin n, i ≥ j → LinearMap.toMatrix b b T i j = 0 := by
  sorry

theorem theorem_220705_problem
  (ϕ : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
  (hϕ : ∀ (a b c d : ℝ), ϕ !![a, b; c, d] = !![b - c, a - d; d - a, c - b]) :
  ↑(LinearMap.ker ϕ) = { X : Matrix (Fin 2) (Fin 2) ℝ | ∃ a b : ℝ, X = !![a, b; b, a] } := by
  sorry





theorem theorem_221021_problem {n : ℕ} {K : Type*} [Field K]
  (A B : Matrix (Fin n) (Fin n) K)
  (h : A * B = 0) :
  A.rank + B.rank ≤ n := by
  sorry

theorem theorem_221142_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {T : Type*} [CommGroup T]
  (θ : T →* Fˣ)
  (ρ : T → (V →ₗ[F] V))
  (hρ : ∀ (g : T) (v : V), ρ g v = (θ g : F) • v) :
  ∀ (g : T) (f : Module.Dual F V) (v : V),
    f (ρ g⁻¹ v) = ((θ g)⁻¹ : F) • f v := by
  sorry



theorem theorem_220920_problem (n : ℕ) (f : (Fin n → ℝ) → ℝ)
  (h_cont : Continuous f)
  (h_lim : Filter.Tendsto f (Filter.cocompact (Fin n → ℝ)) (nhds 0)) :
  UniformContinuous f := by
  sorry

theorem theorem_220657_problem (f : ℕ → ℝ → ℝ)
  (h : ∀ n : ℕ, n > 0 → ∀ x : ℝ, 0 ≤ f n x ∧ f n x ≤ 1 / (n : ℝ)) :
  TendstoUniformly f 0 Filter.atTop := by
  sorry









theorem theorem_221427_problem (a b : ℝ) (hab : a ≤ b)
  (f : C(Set.Icc a b, ℝ)) (ε : ℝ) (hε : 0 < ε) :
  ∃ p : Polynomial ℚ,
    ∀ x : Set.Icc a b, |f x - (p.map (algebraMap ℚ ℝ)).eval (x : ℝ)| < ε := by
  sorry

theorem theorem_221026_problem
  (n m : ℕ)
  (x : Fin n → ℝ)
  (y : Fin m → ℝ)
  (mu1 mu2 sigma2 : ℝ)
  (hn : 0 < n)
  (hm : 0 < m)
  (hsigma : 0 < sigma2)
  (H : Matrix (Fin 3) (Fin 3) ℝ)
  (hH : H = Matrix.diagonal ![
    -((n : ℝ) / sigma2),
    -((m : ℝ) / sigma2),
    2 * ((m + n : ℝ) / sigma2) - 4 * (∑ i, (x i - mu1)^2 / sigma2^2) - 4 * (∑ j, (y j - mu2)^2 / sigma2^2)
  ])
  (h_cond : sigma2 < (4 / (2 * (m + n : ℝ))) * ((∑ i, (x i - mu1)^2) + (∑ j, (y j - mu2)^2))) :
  Matrix.PosDef (-H) := by
  sorry







theorem theorem_221829_problem
  (m n : ℕ)
  (K : Type*) [Field K]
  (hm : m ≥ 3)
  (hn : n ≥ 3)
  (M : Matrix (Fin m) (Fin n) K) :
  M.rank ≤ 2 ↔
  ∀ (r : Fin 3 → Fin m) (c : Fin 3 → Fin n), (M.submatrix r c).det = 0 := by
  sorry



theorem theorem_221546_problem (n : ℕ) (F : (Fin n → ℝ) → (Fin n → ℝ))
  (h : ∀ i : Fin n, UniformContinuous (fun x => F x i)) :
  UniformContinuous F := by
  sorry

theorem theorem_221743_problem
  (n k m : ℕ)
  (y : Matrix (Fin n) (Fin 1) ℝ)
  (X₁ : Matrix (Fin n) (Fin k) ℝ)
  (X₂ : Matrix (Fin n) (Fin m) ℝ)
  (h_inv_X2 : Invertible (X₂.transpose * X₂))
  (P : Matrix (Fin n) (Fin n) ℝ)
  (hP : P = X₂ * (X₂.transpose * X₂)⁻¹ * X₂.transpose)
  (r_y : Matrix (Fin n) (Fin 1) ℝ)
  (hr_y : r_y = (1 - P) * y)
  (r_X₁ : Matrix (Fin n) (Fin k) ℝ)
  (hr_X₁ : r_X₁ = (1 - P) * X₁)
  (h_inv_rX1 : Invertible (r_X₁.transpose * r_X₁))
  (gamma_hat : Matrix (Fin k) (Fin 1) ℝ)
  (hgamma : gamma_hat = (r_X₁.transpose * r_X₁)⁻¹ * r_X₁.transpose * r_y)
  (beta1_hat : Matrix (Fin k) (Fin 1) ℝ)
  (beta2_hat : Matrix (Fin m) (Fin 1) ℝ)
  (h_ols : X₁.transpose * (y - X₁ * beta1_hat - X₂ * beta2_hat) = 0 ∧
           X₂.transpose * (y - X₁ * beta1_hat - X₂ * beta2_hat) = 0) :
  beta1_hat = gamma_hat := by
  sorry

theorem theorem_221682_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (a : ℝ → ℝ) (f : E × ℝ → ℝ)
  (ha_smooth : ContDiff ℝ ⊤ a)
  (ha_nz : ∀ t, a t ≠ 0)
  (hf_smooth : ContDiff ℝ ⊤ f)
  (r : E) (tau : ℝ) :
  let x := (a tau)⁻¹ • r
  deriv (fun τ' => f ((a τ')⁻¹ • r, τ')) tau =
    deriv (fun t' => f (x, t')) tau -
    (deriv a tau / (a tau)^2) * (fderiv ℝ (fun v => f (v, tau)) x r) := by
  sorry







theorem theorem_221868_problem {n : ℕ} {F : Type*} [Field F]
  (A : Matrix (Fin n) (Fin n) F)
  (hA : A ≠ 0)
  (h_det : A.det ≠ 0) :
  A⁻¹ = (A.det)⁻¹ • A.adjugate := by
  sorry





theorem theorem_221910_problem
  (zA zB zC : ℂ)
  (a b c α₁ α₂ α : ℝ)
  (h1 : zB - zA = ↑c * Complex.exp (↑α₁ * Complex.I))
  (h2 : zC - zA = ↑b * Complex.exp (↑α₂ * Complex.I))
  (h3 : α = α₂ - α₁)
  (h4 : a = Complex.abs (zB - zC)) :
  a^2 = c^2 + b^2 - 2 * b * c * Real.cos α := by
  sorry

theorem theorem_222235_problem {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
  (ϕ : Matrix n n K → Matrix n n K)
  (hϕ : ∀ x, ϕ x = Matrix.diagonal x.diag) :
  IsLinearMap K ϕ := by
  sorry











theorem theorem_222054_problem
  (n p : ℕ)
  (hp : p ≥ 1)
  (hn : n ≥ p + 1)
  (X : Matrix (Fin n) (Fin (p + 1)) ℝ)
  (h_intercept : ∀ i, X i 0 = 1)
  (h_invertible : Invertible (Matrix.transpose X * X)) :
  ∃ y₁ y₂ : Fin n → ℝ,
    (∑ i, y₁ i) / (n : ℝ) = (∑ i, y₂ i) / (n : ℝ) ∧
    ∃ j : Fin (p + 1), j ≠ 0 ∧
      let β := fun (y : Fin n → ℝ) =>
        Matrix.mulVec (⅟(Matrix.transpose X * X)) (Matrix.mulVec (Matrix.transpose X) y)
      (β y₁) j ≠ (β y₂) j := by
  sorry











theorem theorem_222379_problem :
  let E := ℕ+ →₀ ℝ
  let e := fun (n : ℕ+) ↦ Finsupp.single n 1
  let norm_inf := fun (x : E) ↦ ⨆ n, |x n|
  ∀ f : E →ₗ[ℝ] E,
  (∀ n, f (e n) = (1 / (n : ℝ)) • e n) →
  ∃ C ≥ 0, ∀ x, norm_inf (f x) ≤ C * norm_inf x := by
  sorry





theorem theorem_222675_problem
  {n : ℕ}
  {R : Type*} [Ring R]
  (A B C : Matrix (Fin n) (Fin n) R) :
  A * (B * C) = (A * B) * C := by
  sorry





theorem theorem_223076_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
  (h : ∃ P : Matrix (Fin n) (Fin n) ℝ, IsUnit P ∧ A = P * B * P⁻¹) :
  A.det = B.det := by
  sorry



theorem theorem_223095_problem
  (n : ℕ)
  (A : Type*) [CommRing A]
  (M : Matrix (Fin n) (Fin n) A) :
  M * M.adjugate = M.det • (1 : Matrix (Fin n) (Fin n) A) := by
  sorry

theorem theorem_222945_problem (f : ℝ → ℝ) (p : ℝ)
  (h_diff : DifferentiableAt ℝ f p) :
  deriv f p = (fderiv ℝ f p) 1 := by
  sorry

theorem theorem_223155_problem
  {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (w : J → ℝ) (m : I → ℝ)
  (x : I → J → ℝ)
  (α : I → ℝ) (β : J → ℝ) (γ : I → J → ℝ)
  (h_primal_eq1 : ∀ i, ∑ j, x i j = 1)
  (h_primal_eq2 : ∀ j, ∑ i, x i j = 1)
  (h_primal_ineq : ∀ i j, x i j + (∑ k in Finset.univ.filter (fun k => w k < w j), x i k) + (∑ l in Finset.univ.filter (fun l => m l < m i), x l j) ≤ 1)
  (h_primal_nonneg : ∀ i j, 0 ≤ x i j)
  (h_dual_ineq : ∀ i j, α i + β j + γ i j + (∑ k in Finset.univ.filter (fun k => w k > w j), γ i k) + (∑ l in Finset.univ.filter (fun l => m l > m i), γ l j) ≤ 1)
  (h_dual_nonpos : ∀ i j, γ i j ≤ 0) :
  (∑ i, α i) + (∑ j, β j) + (∑ i, ∑ j, γ i j) ≤ ∑ i, ∑ j, x i j := by
  sorry



theorem theorem_223150_problem (n : ℕ) {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R) :
  Matrix.trace A = ∑ i, A i i := by
  sorry



theorem theorem_223492_problem
  {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  (p : ℝ) (hp : 1 ≤ p)
  (x u : X) (y v : Y) :
  (‖x + u‖ ^ p + ‖y + v‖ ^ p) ^ (1 / p) ≤
  (‖x‖ ^ p + ‖y‖ ^ p) ^ (1 / p) + (‖u‖ ^ p + ‖v‖ ^ p) ^ (1 / p) := by
  sorry

theorem theorem_223500_problem
  (n K : ℕ)
  (theta : Fin K → Fin n → ℝ)
  (alpha : Fin K → ℝ)
  (h_theta_nonneg : ∀ k i, 0 ≤ theta k i)
  (h_theta_sum : ∀ k, ∑ i, theta k i = 1)
  (h_alpha_nonneg : ∀ k, 0 ≤ alpha k)
  (h_alpha_sum : ∑ k, alpha k = 1) :
  let theta_new := λ i ↦ ∑ k, alpha k * theta k i
  (∑ i, theta_new i = 1) ∧
  (∀ i, 0 ≤ theta_new i) := by
  sorry



theorem theorem_223870_problem
  {K : Type*} [Field K]
  {m n r : ℕ}
  (A : Matrix (Fin m) (Fin n) K)
  (row_idx : Fin r → Fin m)
  (col_idx : Fin r → Fin n)
  (hA : A.rank = r)
  (hR : (A.submatrix row_idx id).rank = r)
  (hC : (A.submatrix id col_idx).rank = r) :
  IsUnit (A.submatrix row_idx col_idx).det := by
  sorry

theorem theorem_223894_problem
  {R : Type*} [CommRing R]
  {m1 m2 n1 n2 : Type*}
  [Fintype m1] [Fintype m2] [Fintype n1] [Fintype n2]
  [DecidableEq m1] [DecidableEq m2] [DecidableEq n1] [DecidableEq n2]
  (A1 : Matrix m1 n1 R) (A2 : Matrix m2 n2 R)
  (B11 : Matrix n1 n1 R) (B12 : Matrix n1 n2 R)
  (B21 : Matrix n2 n1 R) (B22 : Matrix n2 n2 R) :
  let A : Matrix (m1 ⊕ m2) (n1 ⊕ n2) R := Matrix.fromBlocks A1 0 0 A2
  let B : Matrix (n1 ⊕ n2) (n1 ⊕ n2) R := Matrix.fromBlocks B11 B12 B21 B22
  A * B * A.transpose =
    Matrix.fromBlocks
      (A1 * B11 * A1.transpose) (A1 * B12 * A2.transpose)
      (A2 * B21 * A1.transpose) (A2 * B22 * A2.transpose) := by
  sorry



theorem theorem_223677_problem
  (g₀ g₁ g₂ : ℝ)
  (EX EY : ℝ → ℝ)
  (β_XY : ℝ)
  (h_g_diff : g₂ ≠ g₀)
  (h_model : ∃ α_Y : ℝ, ∀ g, EY g = α_Y + β_XY * EX g)
  (β_X β_Y : ℝ)
  (h_def_β_X : β_X = (EX g₂ - EX g₀) / (g₂ - g₀))
  (h_def_β_Y : β_Y = (EY g₂ - EY g₀) / (g₂ - g₀))
  (h_β_X_nz : β_X ≠ 0) :
  β_XY = β_Y / β_X := by
  sorry

theorem theorem_224197_problem (β : ℝ) (hβ : 0 < β)
  (f : ℝ × ℝ → ℝ) (hf : ∀ x, f x = (|x.1| + |x.2|)^2)
  (normH_sq : ℝ × ℝ → ℝ) (hnorm : ∀ x, normH_sq x = x.1^2 + x.2^2)
  (g : ℝ × ℝ → ℝ) (hg : ∀ x, g x = f x - (β / 2) * normH_sq x) :
  ¬ ConvexOn ℝ Set.univ g := by
  sorry

theorem theorem_224039_problem 
  (m n : ℕ) 
  (X : Matrix (Fin m) (Fin n) ℝ) 
  (Y : Fin m → ℝ) 
  (β_opt : Fin n → ℝ)
  (h_min : ∀ β : Fin n → ℝ, 
    (1 / 2 : ℝ) * Matrix.dotProduct (Matrix.mulVec X β_opt - Y) (Matrix.mulVec X β_opt - Y) ≤ 
    (1 / 2 : ℝ) * Matrix.dotProduct (Matrix.mulVec X β - Y) (Matrix.mulVec X β - Y)) :
  Matrix.mulVec (X.transpose * X) β_opt = Matrix.mulVec X.transpose Y := by
  sorry

theorem theorem_224388_problem
  {F : Type*} [Field F]
  {σ : Type*} [DecidableEq σ]
  (k : ℕ)
  (M : Matrix (Fin k) (Fin k) (MvPolynomial σ F))
  (D : MvPolynomial σ F)
  (h_det : M.det = D)
  (h_k_gt_1 : 1 < k)
  (h_k_lt_d : k < D.totalDegree) :
  ∃ P Q : Matrix (Fin k) (Fin k) (MvPolynomial σ F),
    IsUnit P.det ∧ IsUnit Q.det ∧
    P * M * Q = Matrix.diagonal (fun i => if i.val = 0 then D else 1) := by
  sorry

theorem theorem_224130_problem
  (f : ℂ → ℂ)
  (r : ℝ)
  (Mr : ℝ)
  (hf : Continuous f)
  (hr : 0 < r)
  (hMr : Mr = sSup ((Complex.abs ∘ f) '' {z | Complex.abs z = r}))
  (h_const : ∃ c : ℂ, ∀ z, Complex.abs z = r → f z = c) :
  Mr = Complex.abs (f 0) := by
  sorry



theorem theorem_224250_problem (v : (Fin 3 → ℝ) → (Fin 3 → ℝ))
  (hv : ContDiff ℝ 1 v) :
  ∀ p : Fin 3 → ℝ,
  fderiv ℝ v p (v p) = fun i => ∑ j : Fin 3, v p j * fderiv ℝ (fun x => v x i) p (Pi.single j 1) := by
  sorry

theorem theorem_225097_problem (a b c d : ℝ)
  (A : Matrix (Fin 2) (Fin 2) ℝ)
  (hA : A = !![d, d + a; d + b, d + c])
  (h_det : A.det = d) :
  d = d * (c - a - b) - a * b := by
  sorry









theorem theorem_225261_problem
  {n : ℕ}
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (e : Basis (Fin n) ℝ V)
  (M : Matrix (Fin n) (Fin n) ℝ)
  (hM : ∀ i j, M i j = ⟪e i, e j⟫_ℝ)
  (v w : V)
  (v_vec w_vec : Fin n → ℝ)
  (hv : v = ∑ i, v_vec i • e i)
  (hw : w = ∑ i, w_vec i • e i) :
  ⟪v, w⟫_ℝ = Matrix.dotProduct v_vec (Matrix.mulVec M w_vec) := by
  sorry



theorem theorem_224913_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (p q : V →L[ℝ] V)
  (hp : p ^ 2 = p)
  (hq : q ^ 2 = q) :
  ∀ x : V, ‖p ((1 - q) x)‖ ≤ ‖(q - q ^ 2) x‖ := by
  sorry







