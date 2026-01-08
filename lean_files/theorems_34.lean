import Mathlib
import Mathlib.Tactic









theorem theorem_181700_problem (n p : ℕ)
  (X : Matrix (Fin n) (Fin p) ℝ)
  (i j : Fin p) :
  (X.transpose * X) i j = Matrix.dotProduct (fun k => X k i) (fun k => X k j) := by
  sorry



theorem theorem_181283_problem
  (Z : ℝ → ℝ) (x : ℝ → ℝ)
  (hZ : Differentiable ℝ Z)
  (h_ode : ∀ t, deriv (deriv x) t = -2 * (Z (x t) + (deriv x t) ^ 2) * (deriv x t) - deriv Z (x t)) :
  let y := deriv x
  let X : ℝ → (Fin 2 → ℝ) := fun t ↦ ![x t, y t]
  let f : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun v ↦ ![v 1, -2 * (Z (v 0) + (v 1) ^ 2) * (v 1) - deriv Z (v 0)]
  ∀ t, deriv X t = f (X t) := by
  sorry







theorem theorem_181666_problem (E A B C D : Matrix (Fin 2) (Fin 2) ℝ)
  (h_singular : E.det = 0) :
  ¬ LinearIndependent ℝ ![A * E, B * E, C * E, D * E] := by
  sorry













theorem theorem_182078_problem (theta_min theta_max s_1 s_2 : ℝ)
  (h1 : theta_min + theta_max = 180)
  (h2 : 90 * s_2 + s_1 = theta_max - theta_min)
  (h3 : 90 * s_2 - s_1 = |180 - (theta_min + theta_max)|) :
  s_2 = s_1 / 90 := by
  sorry

theorem theorem_182083_problem (n k : ℕ) (h : k ≤ n) :
  (Fintype.card { G : Matrix (Fin n) (Fin k) (ZMod 2) // G.rank < k } : ℝ) /
  (Fintype.card (Matrix (Fin n) (Fin k) (ZMod 2))) =
  1 - ∏ j in Finset.range k, (1 - (1 : ℝ) / 2 ^ (n - j)) := by
  sorry







theorem theorem_181846_problem
  (α : Type*) [Fintype α] [DecidableEq α]
  (m n : ℕ)
  (R C Q : Matrix (Fin m) (Fin n) α → Matrix (Fin m) (Fin n) α)
  (M : ℕ → Matrix (Fin m) (Fin n) α)
  (h_rec : ∀ k, M (k + 1) = Q (C (R (M k)))) :
  ∃ p : ℕ, p > 0 ∧ ∃ N, ∀ k ≥ N, M (k + p) = M k := by
  sorry







theorem theorem_182388_problem (f : ℂ → ℂ)
  (h1 : Differentiable ℂ f)
  (h2 : ∃ M : ℝ, ∀ z : ℂ, Complex.abs (f z) ≤ M) :
  ∃ c : ℂ, ∀ z : ℂ, f z = c := by
  sorry



theorem theorem_182729_problem (n : ℕ) (x c : Fin n → ℝ)
  (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
  Matrix.dotProduct (x - c) (Matrix.mulVec A (x - c)) =
  Matrix.dotProduct x (Matrix.mulVec A x) -
  2 * Matrix.dotProduct c (Matrix.mulVec A x) +
  Matrix.dotProduct c (Matrix.mulVec A c) := by
  sorry







theorem theorem_182798_problem
  {𝕜 Z : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] :
  Nonempty ((NormedSpace.Dual 𝕜 (UniformSpace.Completion Z)) ≃ₗᵢ[𝕜] (NormedSpace.Dual 𝕜 Z)) := by
  sorry



theorem theorem_182424_problem
  (n : ℕ)
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (h_dim : FiniteDimensional.finrank ℝ E = n)
  (f : E → E) (a x y : E)
  (hf : Differentiable ℝ f)
  (A : E →L[ℝ] E) (hA : A = fderiv ℝ f a)
  (A_inv : E →L[ℝ] E)
  (hA_inv_left : A_inv.comp A = ContinuousLinearMap.id ℝ E)
  (hA_inv_right : A.comp A_inv = ContinuousLinearMap.id ℝ E)
  (ϕ : E → E)
  (hϕ : ϕ = fun z ↦ z + A_inv (y - f z)) :
  fderiv ℝ ϕ x = ContinuousLinearMap.id ℝ E - A_inv.comp (fderiv ℝ f x) := by
  sorry

theorem theorem_182571_problem
  (n K : ℕ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (x : Fin n → E)
  (C : Fin n → Fin K)
  (N : Fin K → ℕ)
  (hN : ∀ k, N k = (Finset.univ.filter (fun i => C i = k)).card)
  (x_bar : Fin K → E)
  (hx_bar : ∀ k, x_bar k = (N k : ℝ)⁻¹ • ∑ i in Finset.univ.filter (fun j => C j = k), x i) :
  (1 / 2 : ℝ) * ∑ k : Fin K, ∑ i in Finset.univ.filter (fun a => C a = k), ∑ j in Finset.univ.filter (fun b => C b = k), ‖x i - x j‖^2 =
  ∑ k : Fin K, (N k : ℝ) * ∑ i in Finset.univ.filter (fun a => C a = k), ‖x i - x_bar k‖^2 := by
  sorry

theorem theorem_182652_problem (F_yy F_zz F_yz : ℝ) :
  (∃! sol : ℝ × ℝ, F_yy * sol.1 + F_yz * sol.2 = 0 ∧ F_yz * sol.1 + F_zz * sol.2 = 0) ↔
  F_yy * F_zz - F_yz ^ 2 ≠ 0 := by
  sorry











theorem theorem_183465_problem
  (I : Set ℝ)
  (hI_open : IsOpen I)
  (hI_conn : IsConnected I)
  (p q : ℝ → ℝ)
  (hp : ContinuousOn p I)
  (hq : ContinuousOn q I)
  (y₁ y₂ : ℝ → ℝ)
  (hy₁_diff : ContDiffOn ℝ 2 y₁ I)
  (hy₂_diff : ContDiffOn ℝ 2 y₂ I)
  (hy₁_sol : ∀ t ∈ I, deriv (deriv y₁) t + p t * deriv y₁ t + q t * y₁ t = 0)
  (hy₂_sol : ∀ t ∈ I, deriv (deriv y₂) t + p t * deriv y₂ t + q t * y₂ t = 0)
  (hW : ∀ t ∈ I, y₁ t * deriv y₂ t - y₂ t * deriv y₁ t = 0) :
  ∃ c₁ c₂ : ℝ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ ∀ t ∈ I, c₁ * y₁ t + c₂ * y₂ t = 0 := by
  sorry

theorem theorem_183047_problem
  (n : ℕ)
  (R : Matrix (Fin n) (Fin n) ℝ)
  (h_upper : ∀ i j : Fin n, j < i → R i j = 0)
  (h_orth : R.transpose * R = 1)
  (h_pos : ∀ i : Fin n, 0 < R i i) :
  R = 1 := by
  sorry



theorem theorem_183014_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (v va Δp : E)
  (Q R b : ℝ)
  (hQ : Q = inner va v)
  (hR : R = inner va Δp)
  (hb : b = 2 * inner Δp v - 2 * inner Δp (Q • va) - 2 * inner v (R • va) + 2 * inner (R • va) (Q • va)) :
  b = 2 * inner (Δp - R • va) (v - Q • va) := by
  sorry











theorem theorem_183357_problem {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) :
  let I := (1 : Matrix (Fin 2) (Fin 2) R)
  let Z := (0 : Matrix (Fin 2) (Fin 2) R)
  (Matrix.fromBlocks I A Z I) * (Matrix.fromBlocks I B Z I) = 
  Matrix.fromBlocks I (A + B) Z I := by
  sorry



theorem theorem_184161_problem
  (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (S : Set (Fin n))
  (hA_nonneg : ∀ i j, 0 ≤ A i j)
  (hA_charpoly : A.charpoly = (X - 1) ^ n)
  (hS_closed : ∀ i ∈ S, ∀ j, A i j > 0 → j ∈ S)
  (hS_strongly_connected : ∀ i ∈ S, ∀ j ∈ S, Relation.ReflTransGen (fun u v ↦ A u v > 0) i j)
  (hS_nonempty : S.Nonempty) :
  S.ncard = 1 := by
  sorry

theorem theorem_183797_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (hn : n > 0)
  (hA : ∀ i j, 0 ≤ A i j) :
  (∃ k : ℕ, k > 0 ∧ ∀ i j, 0 < (A ^ k) i j) ↔
  (∀ i j, 0 < (A ^ (n ^ 2 - 2 * n + 2)) i j) := by
  sorry





theorem theorem_184019_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [CommRing R]
  (S_222 I_22 S_221 A : Matrix n n R)
  (h_comm : S_222 * I_22 = I_22 * S_222)
  (hA : A = I_22 * I_22 - S_221 * S_222) :
  A.det = (I_22 * I_22 - S_221 * S_222).det := by
  sorry





theorem theorem_184027_problem
  (m n p : ℕ)
  (hm : m < n)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (B : Matrix (Fin m) (Fin 1) ℝ)
  (G : Matrix (Fin p) (Fin n) ℝ)
  (H : Matrix (Fin p) (Fin 1) ℝ)
  (hA_rank : A.rank = m)
  (Q : Matrix (Fin n) (Fin (n - m)) ℝ)
  (hQ_ker : A * Q = 0)
  (hQ_rank : Q.rank = n - m)
  [Invertible (A * A.transpose)]
  (q : Matrix (Fin n) (Fin 1) ℝ)
  (hq : q = A.transpose * (A * A.transpose)⁻¹ * B)
  [Invertible (Q.transpose * G.transpose * G * Q)]
  (X_star : Matrix (Fin n) (Fin 1) ℝ)
  (hX_cons : A * X_star = B)
  (hX_opt : ∀ X : Matrix (Fin n) (Fin 1) ℝ, A * X = B →
    ((G * X_star - H).transpose * (G * X_star - H)) 0 0 ≤ ((G * X - H).transpose * (G * X - H)) 0 0) :
  X_star = Q * (Q.transpose * G.transpose * G * Q)⁻¹ * Q.transpose * G.transpose * (H - G * q) + q := by
  sorry





theorem theorem_183757_problem
  (M : ℝ)
  (A : Set ℝ)
  (g : ℝ → ℝ)
  (f : ℝ → ℝ)
  (fn : ℕ → ℝ → ℝ)
  (hA : A ⊆ Set.Icc (-M) M)
  (h_range_fn : ∀ n, Set.MapsTo (fn n) A (Set.Icc (-M) M))
  (h_range_f : Set.MapsTo f A (Set.Icc (-M) M))
  (h_conv : TendstoUniformlyOn fn f Filter.atTop A)
  (h_g : UniformContinuousOn g (Set.Icc (-M) M)) :
  TendstoUniformlyOn (fun n ↦ g ∘ (fn n)) (g ∘ f) Filter.atTop A := by
  sorry





theorem theorem_184111_problem (n : ℕ) (a b : ℝ) (hn : n > 0)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : ∀ (i j : Fin n), A i j = 
    if i = j then a 
    else if |(i : ℤ) - (j : ℤ)| = 1 then b 
    else 0) :
  ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' A) μ ↔ 
    ∃ k : ℕ, k ∈ Finset.Icc 1 n ∧ μ = a - 2 * b * Real.cos ((k : ℝ) * Real.pi / ((n : ℝ) + 1)) := by
  sorry



theorem theorem_184426_problem 
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {R : Type*} [Field R]
  (X : Matrix m n R)
  (h_symm : (X.transpose * X).IsSymm)
  (h_inv : IsUnit (X.transpose * X)) :
  ((X.transpose * X)⁻¹).IsSymm := by
  sorry













theorem theorem_184845_problem (f : ℝ → ℝ) :
  MeasurableSet {x | ContinuousAt f x} := by
  sorry



theorem theorem_185039_problem
  (p y : ℝ → ℝ)
  (c : ℝ)
  (h_diff : Differentiable ℝ y)
  (h_sol : ∀ x, deriv y x + p x * y x = 0) :
  ∀ x, deriv (fun x ↦ c * y x) x + p x * (c * y x) = 0 := by
  sorry

theorem theorem_185112_problem (f : ℂ → ℂ)
  (h_holo : DifferentiableOn ℂ f (Metric.closedBall 0 2))
  (h_zero : f 0 = 0)
  (h_deriv : deriv f 0 = 0) :
  ∃ M > 0, ∀ z ∈ Metric.closedBall 0 2, z ≠ 0 → Complex.abs (f z / z ^ 2) ≤ M := by
  sorry





theorem theorem_185134_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (W : Submodule ℝ V)
  (f : W →ₗ[ℝ] ℝ)
  (p : V → ℝ)
  (hp_sub : ∀ x y : V, p (x + y) ≤ p x + p y)
  (hp_hom : ∀ (c : ℝ) (x : V), 0 ≤ c → p (c • x) = c * p x)
  (hf : ∀ w : W, f w ≤ p w) :
  ∃ g : V →ₗ[ℝ] ℝ, (∀ w : W, g w = f w) ∧ (∀ x : V, g x ≤ p x) := by
  sorry

theorem theorem_185020_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (r : ℝ → E) (t : ℝ)
  (h_diff : Differentiable ℝ r) :
  deriv (fun ε ↦ (1 + ε)⁻¹ • r ((1 + ε)^2 * t)) 0 =
  -r t + (2 * t) • deriv r t := by
  sorry

theorem theorem_185513_problem
  (n : ℕ)
  (f : (Fin n → ℝ) → ℝ)
  (g : (Fin n → ℝ) → ℝ)
  (φ : ℝ → ℝ)
  (hg : ConvexOn ℝ Set.univ g)
  (hφ_mono : Monotone φ)
  (hφ_conv : ConvexOn ℝ Set.univ φ)
  (h_eq : ∀ x, f x = φ (g x)) :
  ConvexOn ℝ Set.univ f := by
  sorry





theorem theorem_185515_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f g : E → ℝ) (p : E) (a b : ℝ)
  (hf : DifferentiableAt ℝ f p)
  (hg : DifferentiableAt ℝ g p) :
  fderiv ℝ (fun x ↦ a * f x + b * g x) p =
  a • fderiv ℝ f p + b • fderiv ℝ g p := by
  sorry















theorem theorem_185354_problem
  {n m p : ℕ}
  {K : Type*} [Field K]
  (A : Matrix (Fin n) (Fin n) K)
  (B : Matrix (Fin n) (Fin m) K)
  (C : Matrix (Fin p) (Fin n) K)
  (D : Matrix (Fin p) (Fin m) K)
  (P : Matrix (Fin n) (Fin n) K)
  (s : K)
  (hP : IsUnit P.det)
  (h_res : IsUnit (s • (1 : Matrix (Fin n) (Fin n) K) - A).det) :
  let A_tilde := P * A * P⁻¹
  let B_tilde := P * B
  let C_tilde := C * P⁻¹
  let D_tilde := D
  let H_tilde := C_tilde * (s • (1 : Matrix (Fin n) (Fin n) K) - A_tilde)⁻¹ * B_tilde + D_tilde
  let H := C * (s • (1 : Matrix (Fin n) (Fin n) K) - A)⁻¹ * B + D
  H_tilde = H := by
  sorry

theorem theorem_185639_problem
  (d T : ℕ)
  (X : Type*)
  (x : X)
  (g : Fin (T + 1) → X → (Fin d → ℝ))
  (f : Fin (T + 1) → (Fin d → ℝ) → ℝ)
  (w : Fin (T + 1) → (Fin d → ℝ))
  (α : Fin (T + 1) → ℝ)
  (h : Fin (T + 1) → X → ℝ)
  (F_T : ℝ)
  (h_alpha_pos : ∀ t, 0 < α t)
  (h_h_def : ∀ t y, h t y = Matrix.dotProduct (w t) (g t y))
  (h_F_def : F_T = ∑ t : Fin (T + 1), f t (g t x))
  (h_boost_framework : ∀ t, f t (g t x) = α t * h t x) :
  F_T = ∑ t : Fin (T + 1), α t * h t x := by
  sorry

theorem theorem_185666_problem
  (n : ℕ)
  (x y z : EuclideanSpace ℝ (Fin n))
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hz : z ≠ 0)
  (hz_eq : z = -x - y)
  (A B C : ℝ)
  (hA : A = Real.arccos (- (inner x y) / (norm x * norm y)))
  (hB : B = Real.arccos (- (inner y z) / (norm y * norm z)))
  (hC : C = Real.arccos (- (inner z x) / (norm z * norm x)))
  (h_bound : 0 < A + B + C ∧ A + B + C < 3 * Real.pi) :
  A + B + C = Real.pi := by
  sorry



theorem theorem_185810_problem
  {𝕜 : Type*} [NormedField 𝕜]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  (E F : Submodule 𝕜 Z)
  (hF : IsClosed (F : Set Z))
  (hE : FiniteDimensional 𝕜 E) :
  IsClosed ((E + F) : Set Z) := by
  sorry

theorem theorem_185714_problem
  (a : ℕ → ℝ → ℝ)
  (M : ℕ → ℝ)
  (x₀ : ℝ)
  (h_nonneg : ∀ n, ∀ x ∈ Set.Ici x₀, 0 ≤ a n x)
  (h_mono : ∀ n, MonotoneOn (a n) (Set.Ici x₀) ∨ AntitoneOn (a n) (Set.Ici x₀))
  (h_conv : ∀ x ∈ Set.Ici x₀, Summable (fun n ↦ a n x))
  (h_bound : ∀ n, ∀ t ∈ Set.Ici x₀, a n t ≤ M n)
  (h_M_conv : Summable M) :
  TendstoUniformlyOn (fun N x ↦ ∑ n ∈ Finset.range N, a n x)
    (fun x ↦ ∑' n, a n x) Filter.atTop (Set.Ici x₀) := by
  sorry

