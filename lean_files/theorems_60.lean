import Mathlib
import Mathlib.Tactic













theorem theorem_321587_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  (n : ℕ)
  (f : G → F)
  (A : E →L[𝕜] G)
  (b : G)
  (x : E)
  (u : Fin n → E)
  (hf : ContDiff 𝕜 n f) :
  let h : E → G := fun y => A y + b
  let g : E → F := fun y => f (h y)
  iteratedFDeriv 𝕜 n g x u = iteratedFDeriv 𝕜 n f (h x) (A ∘ u) := by
  sorry





theorem theorem_322210_problem
  (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (u v : EuclideanSpace ℝ (Fin n))
  (hf : Differentiable ℝ f)
  (t : ℝ) :
  deriv (fun t => f (u + t • v)) t = inner (gradient f (u + t • v)) v := by
  sorry



theorem theorem_321974_problem (p : ℕ) (K V : Type*)
  [Field K] [Fintype K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (h_card : Fintype.card K = p)
  (h_dim : FiniteDimensional.finrank K V = 3) :
  Nat.card { S : Submodule K V // FiniteDimensional.finrank K S = 2 } = p^2 + p + 1 := by
  sorry

theorem theorem_322110_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (T : E →L[𝕜] E)
  (h : spectralRadius 𝕜 T < 1) :
  IsUnit (1 - T) := by
  sorry







theorem theorem_321984_problem
  (n K : ℕ)
  (x y : Fin n → ℝ)
  (κ : Fin K → ℝ)
  (C : ℝ)
  (hC : C > 0) :
  let basis (t : ℝ) (k : Fin K) := max 0 (t - κ k)
  let f (u : Fin K → ℝ) (t : ℝ) := ∑ k, u k * basis t k
  let Fit (u : Fin K → ℝ) := ∑ i, (y i - f u (x i))^2
  let Complexity (u : Fin K → ℝ) := ∑ k, (u k)^2
  ∃ u_star : Fin K → ℝ, Complexity u_star ≤ C ∧
    ∀ u : Fin K → ℝ, Complexity u ≤ C → Fit u_star ≤ Fit u := by
  sorry

theorem theorem_322389_problem (a b n : ℝ)
  (f g : ℝ → ℝ)
  (h_ab : a < b)
  (hn1 : 1 ≤ n)
  (hn2 : 2 * Real.pi / (b - a) ≤ n)
  (hf : f = fun x ↦ Real.sin (n * x))
  (hg : g = fun x ↦ Real.cos (n * x)) :
  sSup ((fun x ↦ |deriv f x - deriv g x|) '' Set.Icc a b) ≥
  sSup ((fun x ↦ |f x - g x|) '' Set.Icc a b) := by
  sorry









theorem theorem_322350_problem (k : ℕ)
  (Ez : Matrix (Fin k) (Fin 1) ℝ)
  (Varz : Matrix (Fin k) (Fin k) ℝ)
  (hVarz : Invertible Varz)
  (α : ℝ) :
  let one : Matrix (Fin 1) (Fin 1) ℝ := 1
  let EzzT := Varz + Ez * Ez.transpose
  let ExxT : Matrix (Sum (Fin 1) (Fin k)) (Sum (Fin 1) (Fin k)) ℝ :=
    Matrix.fromBlocks one Ez.transpose Ez EzzT
  let Ealpha_xT : Matrix (Fin 1) (Sum (Fin 1) (Fin k)) ℝ :=
    fun _ j => match j with
      | Sum.inl _ => α
      | Sum.inr i => α * Ez i 0
  let target : Matrix (Fin 1) (Sum (Fin 1) (Fin k)) ℝ :=
    fun _ j => match j with
      | Sum.inl _ => α
      | Sum.inr _ => 0
  Ealpha_xT * ExxT⁻¹ = target := by
  sorry



theorem theorem_323001_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  (hX : ¬ FiniteDimensional 𝕜 X) :
  ∃ T : X →L[𝕜] X, IsCompactOperator T ∧ ¬ FiniteDimensional 𝕜 (LinearMap.range T) := by
  sorry









theorem theorem_322990_problem (n d : ℕ) (k : Fin d → ℕ)
  (h_size : ∀ i, 1 ≤ k i)
  (h_sum : Finset.univ.sum k = n) :
  Finset.univ.sum (fun i => k i - 1) = n - d := by
  sorry

theorem theorem_323273_problem (n : ℕ)
  (p : Fin (n + 1) → ℝ)
  (hp : Matrix.dotProduct p p = 1)
  (X : Fin (n + 1) → ℝ)
  (hX : X = p)
  (v : Fin n → (Fin (n + 1) → ℝ))
  (hv_tan : ∀ i, Matrix.dotProduct p (v i) = 0)
  (hv_basis : LinearIndependent ℝ v)
  (ω : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ → ℝ)
  (hω : ∀ M, ω M = Matrix.det M) :
  ω (Matrix.vecCons X v) = Matrix.det (Matrix.vecCons X v) := by
  sorry









theorem theorem_323661_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (i j : Fin m) :
  (A * A.transpose) i j = Matrix.dotProduct (A i) (A j) := by
  sorry



theorem theorem_323760_problem (k : ℝ) (hk : 0 < k) (f : ℝ → ℝ)
  (hf : ∀ x ∈ Set.Ioi 0, f x = if x ≥ k then 0 else (1 / x) * Real.exp (-1 / (k - x))) :
  ContDiffOn ℝ ⊤ f (Set.Ioi 0) := by
  sorry





theorem theorem_323677_problem
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (P : Matrix n n ℝ) (B : Matrix m n ℝ) (R : Matrix m m ℝ)
  (hP : P.PosDef) (hR : R.PosDef) :
  (P⁻¹ + B.transpose * R⁻¹ * B)⁻¹ * B.transpose * R⁻¹ =
  P * B.transpose * (B * P * B.transpose + R)⁻¹ := by
  sorry

theorem theorem_324044_problem
  (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℂ)
  (f : Polynomial ℂ)
  (c : ℂ)
  (h : Module.End.HasEigenvalue (Matrix.toLin' (Polynomial.aeval A f)) c) :
  ∃ z : ℂ, Polynomial.eval z f = c ∧ Module.End.HasEigenvalue (Matrix.toLin' A) z := by
  sorry





theorem theorem_324290_problem
  {K : Type*} [Field K]
  {V2 V3 : Type*} [AddCommGroup V2] [Module K V2]
  [AddCommGroup V3] [Module K V3]
  {ι : Type*}
  (V1 : Submodule K V2)
  (p : V2 →ₗ[K] V3)
  (h_surj : Function.Surjective p)
  (h_ker : LinearMap.ker p = V1)
  (F2 : ι → Submodule K V2)
  (F3 : ι → Submodule K V3)
  (h_map : ∀ j, (F2 j).map p = F3 j) :
  ∃ s : V3 →ₗ[K] V2, p.comp s = LinearMap.id ∧
    ∀ j, (F3 j).map s = LinearMap.range s ⊓ F2 j := by
  sorry



theorem theorem_323474_problem
  {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (g : M → M → R)
  (J : M → M)
  (h : M → M → R)
  (D : M → R → R) -- Represents the action of a vector field on a function Z(f)
  (nabla : M → M → M) -- Represents the connection ∇_Z X
  -- Definitions of the covariant derivatives for the specific tensor types
  (nabla_g : M → M → M → R) -- (∇_Z g)(X, Y)
  (nabla_J : M → M → M)      -- (∇_Z J)(X)
  (nabla_h : M → M → M → R)  -- (∇_Z h)(X, Y)
  -- Condition: h defined in terms of g and J
  (h_def : ∀ X Y, h X Y = g (J X) Y)
  -- Conditions: Standard definitions of covariant derivatives implied by the problem context
  (H_nabla_g : ∀ Z X Y, nabla_g Z X Y = D Z (g X Y) - g (nabla Z X) Y - g X (nabla Z Y))
  (H_nabla_J : ∀ Z X, nabla_J Z X = nabla Z (J X) - J (nabla Z X))
  (H_nabla_h : ∀ Z X Y, nabla_h Z X Y = D Z (h X Y) - h (nabla Z X) Y - h X (nabla Z Y)) :
  -- Goal: The identity stated in the problem
  ∀ Z X Y, nabla_h Z X Y = nabla_g Z (J X) Y + g (nabla_J Z X) Y := by
  sorry



theorem theorem_324274_problem
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (X : Type*) [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [TopologicalAddGroup X] [ContinuousSMul 𝕜 X]
  (Y : Set X) :
  ({f : X →L[𝕜] 𝕜 | ∀ y ∈ Y, f y = 0} = {0}) ↔ closure Y = Set.univ := by
  sorry





theorem theorem_324104_problem (n : ℕ)
  (f : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
  (u v w : Fin n → ℝ)
  (e : Fin n → Fin n → ℝ)
  (he : ∀ i j, e i j = if i = j then 1 else 0)
  (lin_1 : ∀ v w, IsLinearMap ℝ (fun x ↦ f x v w))
  (lin_2 : ∀ u w, IsLinearMap ℝ (fun y ↦ f u y w))
  (lin_3 : ∀ u v, IsLinearMap ℝ (fun z ↦ f u v z)) :
  f u v w = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
    u i * v j * w k * f (e i) (e j) (e k) := by
  sorry





theorem theorem_324511_problem (a b : ℝ) (h_ab : a ≤ b)
  (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
  (h1 : ∀ x ∈ Set.Icc a b, Monotone (fun n ↦ fn n x))
  (h2 : ∀ x ∈ Set.Icc a b, Filter.Tendsto (fun n ↦ fn n x) Filter.atTop (nhds (f x)))
  (h3 : ContinuousOn f (Set.Icc a b)) :
  TendstoUniformlyOn fn f Filter.atTop (Set.Icc a b) := by
  sorry



















theorem theorem_325156_problem
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (U' : Matrix (Fin n) (Fin n) ℝ)
  (M' : Matrix (Fin m) (Fin n) ℝ)
  (h_inv : IsUnit U')
  (h_eq : M' = A * U') :
  A = M' * U'⁻¹ := by
  sorry

















theorem theorem_326089_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {n : ℕ} (h_dim : FiniteDimensional.finrank K V = n)
  (f : V →ₗ[K] V)
  (v : Fin n → V) :
  let ι := ExteriorAlgebra.ι K
  let wedge := ((List.ofFn v).map ι).prod
  ExteriorAlgebra.map f wedge = (LinearMap.det f) • wedge := by
  sorry





theorem theorem_325825_problem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
  (h : Matrix.trace (A.conjTranspose * A) = Matrix.trace (A ^ 2)) :
  A = A.conjTranspose := by
  sorry

theorem theorem_325755_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (α : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ)
  (h_iso : ∀ (M : Matrix n n ℝ), M.IsSymm →
    ∀ (R : Matrix n n ℝ), R ∈ Matrix.orthogonalGroup n ℝ →
    α (R.transpose * M * R) = R.transpose * (α M) * R) :
  ∃ a b c : ℝ, ∀ (M : Matrix n n ℝ), M.IsSymm →
    α M = (a * M.trace) • (1 : Matrix n n ℝ) + b • M + c • M.transpose := by
  sorry





theorem theorem_325951_problem :
  ∀ p : ℝ × ℝ × ℝ,
  (∃ t : ℝ,
    let q : ℝ × ℝ × ℝ := (t, t, 1 + t)
    (p.1 - q.1)^2 + (p.2.1 - q.2.1)^2 + (p.2.2 - q.2.2)^2 = 1 ∧
    (p.1 - q.1) * 1 + (p.2.1 - q.2.1) * 1 + (p.2.2 - q.2.2) * 1 = 0) ↔
  (∃ t a : ℝ, abs a ≤ Real.sqrt ((2 : ℝ) / 3) ∧
    let h := Real.sqrt (2 - 3 * a^2)
    (p = (t + a, t + (-a + h) / 2, 1 + t + (-a - h) / 2) ∨
     p = (t + a, t + (-a - h) / 2, 1 + t + (-a + h) / 2))) := by
  sorry

theorem theorem_326312_problem
  (m n : ℕ)
  (X : Matrix (Fin m) (Fin n) ℝ)
  (w : Fin n → ℝ)
  (hw_pos : ∀ i, 0 < w i)
  (hw_sum : ∑ i, w i = 1) :
  let W := Matrix.diagonal w
  let ones : Matrix (Fin n) (Fin 1) ℝ := fun _ _ ↦ 1
  let M := X * W * X.transpose - X * W * (ones * ones.transpose) * W * X.transpose
  M.PosSemidef := by
  sorry

theorem theorem_326059_problem
  (u0 u1 v0 v1 : Fin 3 → ℝ)
  (P : (Fin 3 → ℝ) → (Fin 2 → ℝ))
  (hP : P = fun u => ![u 0, u 1])
  (s t : ℝ)
  (hs : 0 ≤ s ∧ s ≤ 1)
  (ht : 0 ≤ t ∧ t ≤ 1)
  (h_inter : P (u0 + s • (u1 - u0)) = P (v0 + t • (v1 - v0)))
  (h_transversal : Matrix.det ![P (u1 - u0), P (v1 - v0)] ≠ 0) :
  (u0 + s • (u1 - u0)) 2 ≤ (v0 + t • (v1 - v0)) 2 ↔
  0 ≤ Matrix.det ![v0 - u0, u1 - u0, v1 - v0] * Matrix.det ![P (u1 - u0), P (v1 - v0)] := by
  sorry

theorem theorem_326313_problem
  (n : ℕ)
  (ν w_B μ_B : EuclideanSpace ℝ (Fin n))
  (h_ortho : inner ν (w_B - μ_B) = (0 : ℝ))
  (h_bound : ‖ν‖ ≤ 1)
  (h_denom : w_B ≠ μ_B) :
  ‖ν + Real.sqrt (1 - ‖ν‖^2) • (‖w_B - μ_B‖⁻¹ • (w_B - μ_B))‖ = 1 := by
  sorry

theorem theorem_326357_problem (K S V1 V2 : Type*)
  [Field K]
  [AddCommGroup V1] [Module K V1]
  [AddCommGroup V2] [Module K V2]
  (h1 : Basis S K V1)
  (h2 : Basis S K V2) :
  Nonempty (V1 ≃ₗ[K] V2) := by
  sorry













theorem theorem_327205_problem
  (n : ℕ)
  (V : Fin n → ℝ → ℝ) -- V^j(t), a family of functions indexed by j
  (t₀ : ℝ)
  (E : Type*) [AddCommGroup E] [Module ℝ E] -- The space containing the vector field operators
  (partial_x : Fin n → E) -- The operators d/dx^j
  :
  ∑ j : Fin n, deriv (V j) t₀ • partial_x j =
  ∑ k : Fin n, deriv (V k) t₀ • partial_x k := by
  sorry





theorem theorem_326907_problem
  (R : Type*) [CommRing R]
  (m : Ideal R) [m.IsMaximal]
  (M : Type*) [AddCommGroup M] [Module R M]
  (e : M)
  (he : e ≠ 0)
  (h_vec : ∀ r ∈ m, r • e = 0) :
  Nonempty ((R ⧸ m) ≃ₗ[R] (Submodule.span R {e})) := by
  sorry

theorem theorem_326963_problem
  {n m : Type*} [Fintype n] [Fintype m]
  (A : m → n → ℂ)
  (B : m → ℂ)
  (w z omega : m → n → ℝ)
  (phi : n → ℝ)
  (x : n → ℂ)
  (h_w : ∀ k j, w k j = Complex.abs (A k j) ^ 2 + Complex.abs (B k) ^ 2)
  (h_z : ∀ k j, z k j = 2 * Complex.abs (A k j) * Complex.abs (B k))
  (h_omega : ∀ k j, omega k j = Complex.arg (A k j) - Complex.arg (B k))
  (h_phi : ∀ j, 0 ≤ phi j ∧ phi j ≤ 2 * Real.pi)
  (h_x : ∀ j, x j = Complex.cos (phi j : ℂ) + Complex.I * Complex.sin (phi j : ℂ)) :
  ∑ k : m, ∑ j : n, Complex.abs (A k j * x j - B k) ^ 2 =
  ∑ k : m, ∑ j : n, (w k j - z k j * Real.cos (phi j + omega k j)) := by
  sorry





theorem theorem_327091_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (x_i w B : E) (b γ_i : ℝ)
  (h_w : w ≠ 0)
  (h_gamma : γ_i = (inner w x_i + b) / ‖w‖)
  (h_B_on_boundary : inner w B + b = 0)
  (h_B_proj_direction : ∃ k : ℝ, B = x_i - k • w) :
  B = x_i - (γ_i / ‖w‖) • w := by
  sorry

theorem theorem_327383_problem
  (a b θ : ℝ)
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (M : Matrix (Fin 2) (Fin 2) ℝ)
  (hM : M = !![1 / a ^ 2, 0; 0, 1 / b ^ 2])
  (Q : Matrix (Fin 2) (Fin 2) ℝ)
  (hQ : Q = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ])
  (M' : Matrix (Fin 2) (Fin 2) ℝ)
  (hM' : M' = Q.transpose * M * Q) :
  M'.trace = 1 / a ^ 2 + 1 / b ^ 2 := by
  sorry

