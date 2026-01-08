import Mathlib
import Mathlib.Tactic

theorem theorem_384179_problem
  (k : ℕ) (hk : k > 0)
  (ζ : ℂ) (v : ℝ)
  (α β : Matrix (Fin 2) (Fin 1) ℂ)
  (A : Matrix (Fin 2) (Fin 2) ℂ)
  (hα : α = !![1; ζ ^ (-v : ℂ)])
  (hβ : β = !![ζ ^ (-v : ℂ); ζ ^ (v : ℂ)])
  (hA : A = (1 + ζ ^ (v : ℂ)) • (α * β.transpose)) :
  (A.conjTranspose ^ k * A ^ k).trace = 
    4 * (1 + ζ ^ (v : ℂ)) ^ (2 * k - 1) * (1 + ζ ^ (-v : ℂ)) ^ (2 * k - 1) := by
  sorry





theorem theorem_384669_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  (h_inf : ¬ FiniteDimensional 𝕜 X)
  {ι : Type*} (b : Basis ι 𝕜 X) :
  Set.Finite {i : ι | Continuous (b.coord i)} := by
  sorry













theorem theorem_385437_problem
  (m : ℕ)
  (A : Matrix (Fin m) (Fin m) ℂ)
  (c : ℂ)
  (n : ℕ)
  (h_alg_mult : (Matrix.charpoly A).rootMultiplicity c = n) :
  FiniteDimensional.finrank ℂ (LinearMap.ker (Matrix.toLin' ((A - c • (1 : Matrix (Fin m) (Fin m) ℂ)) ^ n))) = n := by
  sorry



theorem theorem_385700_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) :
  Matrix.det (A * B) = Matrix.det A * Matrix.det B := by
  sorry

theorem theorem_380397_problem
  (k : Type*) [Field k]
  (n : ℕ) (hn : 2 ≤ n)
  (U : Submodule k (Fin n → k))
  (hU : ∀ x : Fin n → k, x ∈ U ↔ ∑ i, x i = 0)
  (V : Submodule k (Fin n → k))
  (hV : V = Submodule.span k {fun (_ : Fin n) ↦ (1 : k)}) :
  ∀ W : Submodule k (Fin n → k),
    (∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → k), v ∈ W → v ∘ σ ∈ W) →
    (W = ⊥ ∨ W = V ∨ W = U ∨ W = ⊤) := by
  sorry

theorem theorem_385614_problem :
  ∃ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ),
    (∀ x : Fin n → ℝ, x ≠ 0 → Matrix.dotProduct x ((A * B).mulVec x) > 0) ∧
    ¬ (∀ x : Fin n → ℝ, x ≠ 0 → Matrix.dotProduct x ((B * A).mulVec x) > 0) := by
  sorry

theorem theorem_385283_problem (d : ℕ)
  (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : Measurable f) :
  ∫ x, ∑ i : Fin d, ‖(x i : ℂ) * f x‖^2 = ∫ x, ‖x‖^2 * ‖f x‖^2 := by
  sorry

theorem theorem_385472_problem (n : ℕ) (hn : n > 0) :
  (∃ (v_poly w_poly : Fin n → MvPolynomial (Fin 4 × Fin n) ℚ),
    (∀ i, (v_poly i).IsHomogeneous 2) ∧
    (∀ i, (w_poly i).IsHomogeneous 2) ∧
    (∀ (a b c d : Fin n → ℚ),
      let input : Fin 4 × Fin n → ℚ := fun ⟨k, j⟩ =>
        if k = 0 then a j
        else if k = 1 then b j
        else if k = 2 then c j
        else d j
      let v : Fin n → ℚ := fun i => MvPolynomial.eval input (v_poly i)
      let w : Fin n → ℚ := fun i => MvPolynomial.eval input (w_poly i)
      let inner (x y : Fin n → ℚ) := ∑ k, x k * y k
      (inner a a + inner b b) * (inner c c + inner d d) = inner v v + inner w w)) →
  n = 1 ∨ n = 2 ∨ n = 4 := by
  sorry

theorem theorem_385960_problem
  (n : ℕ)
  (f : (Fin n → ℝ) → ℝ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (h_concave : ConcaveOn ℝ Set.univ f) :
  ConcaveOn ℝ Set.univ (fun x => f (A.mulVec x)) := by
  sorry

theorem theorem_385344_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G U : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup U] [NormedSpace 𝕜 U]
  (star : E →L[𝕜] F →L[𝕜] G) -- The associative bilinear product stated in the problem
  (A : U → E) -- Tensor A depending on variable(s)
  (B : U → F) -- Tensor B depending on variable(s)
  (x : U) -- The point of evaluation
  (hA : DifferentiableAt 𝕜 A x) -- A is differentiable
  (hB : DifferentiableAt 𝕜 B x) -- B is differentiable
  : fderiv 𝕜 (fun u => star (A u) (B u)) x =
    (star.flip (B x)).comp (fderiv 𝕜 A x) + (star (A x)).comp (fderiv 𝕜 B x) := by
  sorry



theorem theorem_385952_problem (𝕜 X : Type*) [RCLike 𝕜]
  [AddCommGroup X] [Module 𝕜 X]
  [TopologicalSpace X] [TopologicalAddGroup X] [ContinuousSMul 𝕜 X]
  (Y : Submodule 𝕜 X) (hY : Y ≠ ⊤) :
  interior (Y : Set X) = ∅ := by
  sorry









theorem theorem_386118_problem
  {Ω : Type*}
  (L : (Ω → ℝ) → (Ω → ℝ))
  (g : Ω → Ω → ℝ)
  (δ : Ω → Ω → ℝ)
  (integral : (Ω → ℝ) → ℝ)
  (k : Ω → ℝ)
  -- Condition: L applied to Green's function is delta (L acts on the second argument t)
  (h_green : ∀ x, L (g x) = δ x)
  -- Condition: Interchange of linear operator L and the integral
  (h_interchange : ∀ t, L (fun t' => integral (fun x => k x * g x t')) t =
    integral (fun x => k x * L (g x) t))
  -- Condition: Sifting property of the delta function
  (h_sift : ∀ t, integral (fun x => k x * δ x t) = k t) :
  -- Conclusion: L applied to the integral yields k
  L (fun t => integral (fun x => k x * g x t)) = k := by
  sorry

theorem theorem_385995_problem
  {G K : Type*} [Group G] [Field K]
  {n : ℕ}
  (φ : Fin n → G →* Kˣ)
  (h_distinct : Function.Injective φ)
  (a : Fin n → K)
  (h_lin_dep : ∀ g : G, ∑ i, a i * (φ i g : K) = 0) :
  ∀ i, a i = 0 := by
  sorry









theorem theorem_385890_problem
  (m n k : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (U : Matrix (Fin m) (Fin k) ℝ)
  (V : Matrix (Fin n) (Fin k) ℝ)
  (U_tilde : Matrix (Fin m) (Fin k) ℝ)
  (V_tilde : Matrix (Fin n) (Fin k) ℝ)
  (h_rank : A.rank = k)
  (h1 : A = U * V.transpose)
  (h2 : A = U_tilde * V_tilde.transpose) :
  U * V.transpose = U_tilde * V_tilde.transpose := by
  sorry

theorem theorem_385891_problem (α β θ ρ : ℝ) (hα : 0 < α) (hβ : 0 < β) :
  { p : ℝ × ℝ | ((p.1 - θ) / α)^2 + ((p.2 - ρ) / β)^2 < 1 } =
  Set.image (fun p => (α * p.1 + θ, β * p.2 + ρ)) { p : ℝ × ℝ | p.1^2 + p.2^2 < 1 } := by
  sorry



theorem theorem_386569_problem
  {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [TopologicalRing 𝕜]
  (X : Type*) [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [TopologicalAddGroup X] [ContinuousSMul 𝕜 X]
  (Y : Type*) [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y] [TopologicalAddGroup Y] [ContinuousSMul 𝕜 Y]
  (θ : X →ₗ[𝕜] Y)
  (h : ContinuousAt θ 0) :
  Continuous θ := by
  sorry

theorem theorem_386375_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
  (h_distinct : A.charpoly.Separable)
  (h_commute : A * B = B * A) :
  ∃ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P.det ∧
    (P⁻¹ * A * P).IsDiag ∧ (P⁻¹ * B * P).IsDiag := by
  sorry



theorem theorem_385959_problem (x y z : ℝ)
  (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (h_vol : x * y * z = 1000)
  (h_min : ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → a * b * c = 1000 →
    6 * (x * y + y * z + z * x) ≤ 6 * (a * b + b * c + c * a)) :
  x = 10 ∧ y = 10 ∧ z = 10 := by
  sorry

theorem theorem_386802_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [Field K]
  (J Y : Matrix n n K)
  [Invertible Y]
  (Z' : Matrix n n K)
  (hZ : Z' = Y * J * ⅟Y) :
  ∀ μ, Module.End.HasEigenvalue (Matrix.toLin' Z') μ ↔ Module.End.HasEigenvalue (Matrix.toLin' J) μ := by
  sorry

theorem theorem_386480_problem
  (n N k : ℕ)
  (A : Matrix (Fin n) (Fin N) ℝ)
  (U : Matrix (Fin n) (Fin n) ℝ)
  (S : Matrix (Fin n) (Fin N) ℝ)
  (V : Matrix (Fin N) (Fin N) ℝ)
  (P : Matrix (Fin k) (Fin n) ℝ)
  (Ak : Matrix (Fin k) (Fin N) ℝ)
  (h_svd : A = U * S * V.transpose)
  (h_Ak : Ak = P * A) :
  Ak = P * U * S * V.transpose := by
  sorry

theorem theorem_386597_problem 
  {n : Type*} [Fintype n] [DecidableEq n]
  (A B : Matrix n n ℝ)
  (hA_symm : A.IsSymm)
  (hB_symm : B.IsSymm)
  (hA : IsUnit A)
  (h_cond : IsUnit (1 + A⁻¹ * B)) :
  (A + B)⁻¹ = A⁻¹ - A⁻¹ * B * (1 + A⁻¹ * B)⁻¹ * A⁻¹ := by
  sorry

theorem theorem_386778_problem
  (n : ℕ)
  (V : Type*) [Fintype V] [Nonempty V]
  (u : V → Fin n → ℝ)
  (v : Fin n → ℝ)
  (c : V)
  (P : ℝ)
  (hP : P = Real.exp (Matrix.dotProduct (u c) v) / ∑ j : V, Real.exp (Matrix.dotProduct (u j) v)) :
  -Real.log P = -Matrix.dotProduct (u c) v + Real.log (∑ j : V, Real.exp (Matrix.dotProduct (u j) v)) := by
  sorry



theorem theorem_386879_problem
  (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (M : ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hM : M > 0)
  (h_lip : ∀ y z, dist (f y) (f z) ≤ M * dist y z)
  (h_diff : DifferentiableAt ℝ f x) :
  ‖gradient f x‖ ≤ M := by
  sorry



theorem theorem_386570_problem (m : ℕ)
  (A B : Matrix (Fin m) (Fin m) ℝ)
  (δ : Fin m → Fin m → Fin m → ℝ)
  (hδ : ∀ i j k, δ i j k = if i = j ∧ j = k then 1 else 0)
  (C : Fin m → Fin m → Fin m → ℝ)
  (hC : ∀ i j k, C i j k = ∑ p : Fin m, ∑ q : Fin m, A i p * δ p j q * B q k) :
  ∀ i j k, C i j k = A i j * B j k := by
  sorry



theorem theorem_387237_problem 
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (DA DB : Submodule ℂ H)
  (A : DA →ₗ[ℂ] H)
  (B : DB →ₗ[ℂ] H)
  (h_sub : DB ≤ DA)
  (h_ext : ∀ (y : DB), A ⟨y.1, h_sub y.2⟩ = B y)
  (lam : ℂ)
  (h_inv : Function.Bijective (fun (v : DA) => A v - lam • (v : H)))
  (x : DA)
  (hx_not_domB : (x : H) ∉ DB) :
  ¬ ∃ (y : DB), B y - lam • (y : H) = A x - lam • (x : H) := by
  sorry















theorem theorem_387494_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [Field K]
  (A B X : Matrix n n K)
  (hA : IsUnit A.det)
  (hB : IsUnit B.det)
  (h : (B.transpose * X).transpose - A * ((B⁻¹ * A)⁻¹ - B) = 0) :
  X.transpose = 1 - A := by
  sorry



theorem theorem_387556_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℚ)
  (h_poly : A.charpoly = B.charpoly)
  (h_distinct : A.charpoly.Separable) :
  ∃ P : Matrix (Fin n) (Fin n) ℚ, IsUnit P ∧ P⁻¹ * A * P = B := by
  sorry











theorem theorem_388177_problem
  (n : ℕ)
  (Q : Matrix (Fin n) (Fin n) ℝ)
  (v : Fin n → ℝ)
  (beta beta_d : ℝ)
  (h_eigen : Matrix.mulVec Q v = beta_d • v)
  (h_beta : beta > 0)
  (h_beta_d : beta_d < 0)
  (t : ℕ)
  (ht : t ≥ 1) :
  Matrix.mulVec (((1 : Matrix (Fin n) (Fin n) ℝ) - beta • Q) ^ t) v =
    ((1 : ℝ) + beta * |beta_d|) ^ t • v := by
  sorry

theorem theorem_388059_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
  (x p : E) (hp_in : p ∈ C)
  (hp_min : ∀ c ∈ C, ‖p - x‖ ≤ ‖c - x‖) :
  ∀ c ∈ C, inner (x - p) (c - p) ≤ (0 : ℝ) := by
  sorry

theorem theorem_387516_problem
  (n : ℕ)
  (F : (Fin n → ℝ) → (Fin n → ℝ))
  (x : Fin n → ℝ)
  (i j k : Fin n)
  (hF : ContDiff ℝ 2 F) :
  iteratedFDeriv ℝ 2 F x ![Pi.single k 1, Pi.single j 1] i =
  fderiv ℝ (fun y => fderiv ℝ F y (Pi.single j 1) i) x (Pi.single k 1) := by
  sorry

theorem theorem_388107_problem (p q : ℕ)
  (A B : Matrix (Fin p) (Fin q) ℝ)
  (h : LinearMap.range (Matrix.toLin' A) ≤ LinearMap.range (Matrix.toLin' B)) :
  FiniteDimensional.finrank ℝ (LinearMap.range (Matrix.toLin' A)) ≤
  FiniteDimensional.finrank ℝ (LinearMap.range (Matrix.toLin' B)) := by
  sorry

theorem theorem_388159_problem
  (V : ℝ → EuclideanSpace ℝ (Fin 3))
  (h : ContDiff ℝ 2 V) :
  ∀ t, deriv (fun t => crossProduct (V t) (deriv V t)) t =
       crossProduct (V t) (deriv (deriv V) t) := by
  sorry



theorem theorem_388270_problem {K : Type*} [Field K] (A : Matrix (Fin 2) (Fin 2) K) :
  A ^ 2 ≠ !![0, 1; 0, 0] := by
  sorry



theorem theorem_388247_problem :
  ∃ (F : Type) (_ : Field F) (_ : Fintype F)
    (V : Type) (_ : AddCommGroup V) (_ : Module F V)
    (ι₁ ι₂ : Type) (B₁ : Basis ι₁ F V) (B₂ : Basis ι₂ F V),
    Cardinal.mk F < Cardinal.mk ι₁ ∧
    Cardinal.mk F < Cardinal.mk ι₂ ∧
    Cardinal.mk ι₁ ≠ Cardinal.mk ι₂ := by
  sorry

theorem theorem_388652_problem
  {H : Type*} [AddCommGroup H] [Module ℂ H]
  (beta : H → H → ℂ)
  (h_lin_left : ∀ (c : ℂ) (v w : H), beta (c • v) w = c * beta v w)
  (h_lin_right_conj : ∀ (c : ℂ) (v w : H), beta v (c • w) = star c * beta v w)
  (w : H) (hw : beta w w ≠ 0)
  (v : H) :
  let P_w := (beta v w / beta w w) • w
  (∃ c : ℂ, P_w = c • w) ∧ beta (v - P_w) w = 0 := by
  sorry



theorem theorem_388906_problem
  (N : ℕ)
  (ω : Fin N → ℝ)
  (P : ℝ)
  (p : Fin N → ℝ)
  (j : Fin N)
  (h_sum : ∑ i, p i = P)
  (h_pos : ∀ i, 0 ≤ p i)
  (h_max : ∀ i, ω i ≤ ω j) :
  ∑ i, p i * Real.exp (ω i) ≤ P * Real.exp (ω j) := by
  sorry

theorem theorem_388927_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  -- Condition: S is the subspace of solutions to the linear wave equation (Closed Submodule)
  (S : Submodule ℝ V)
  (hS_closed : IsClosed (S : Set V))
  -- Condition: u_m is a set of particular solutions
  (u_m : ℤ → V)
  (hu_m_sol : ∀ m, u_m m ∈ S)
  -- Condition: {u_m} is a complete set (represented as a Hilbert Basis for S)
  (h_complete : ∃ (b : HilbertBasis ℤ ℝ S), ∀ m, (b m : V) = u_m m)
  -- Condition: u is a solution
  (u : V) (hu : u ∈ S) :
  -- Question: u can be expressed as a superposition of u_m
  ∃ (a : ℤ → ℝ), HasSum (fun m => a m • u_m m) u := by
  sorry





theorem theorem_389240_problem
  (n : ℕ)
  (f g : EuclideanSpace ℝ (Fin n) → ℝ)
  (c : ℝ)
  (p : EuclideanSpace ℝ (Fin n))
  (hf : DifferentiableAt ℝ f p)
  (hg : DifferentiableAt ℝ g p)
  (h_mem_S : g p = c)
  (h_extr : IsLocalExtrOn f {x | g x = c} p)
  (h_grad_nonzero : gradient g p ≠ 0) :
  ∃ k : ℝ, gradient f p = k • gradient g p := by
  sorry



theorem theorem_389450_problem (m n k p : ℕ)
  (hn : n > 0)
  (a : Matrix (Fin m) (Fin k) ℝ)
  (b : Matrix (Fin n) (Fin k) ℝ)
  (M : Matrix (Sum (Fin m) (Fin n)) (Fin k) ℝ)
  (Y : Matrix (Sum (Fin m) (Fin n)) (Fin p) ℝ)
  (hM : M = Sum.elim a b)
  (h1 : Y.rank = m + n)
  (h2 : M.rank ≤ m) :
  ¬ ∃ X : Matrix (Fin k) (Fin p) ℝ, M * X = Y := by
  sorry

theorem theorem_389117_problem
  {R : Type*} [CommRing R]
  {n N : ℕ}
  (A : Fin N → Matrix (Fin n) (Fin n) R) :
  Matrix.det (fun i j => ∑ k : Fin N, A k i j) =
  ∑ f : Fin n → Fin N, Matrix.det (fun i j => A (f i) i j) := by
  sorry







theorem theorem_389647_problem (n m : ℕ)
  (B : Matrix (Fin n) (Fin n) ℝ)
  (P : Matrix (Fin n) (Fin n) ℝ)
  (A C : Matrix (Fin n) (Fin m) ℝ)
  (h_inv : Invertible B)
  (h_prod : P * B = 1)
  (h_eq : A = B * C) :
  P * A = C := by
  sorry



theorem theorem_389623_problem
  (n k : ℕ)
  (X : Matrix (Fin n) (Fin k) ℝ)
  (A : Matrix (Fin k) (Fin k) ℝ)
  (hA : Invertible A)
  (hX : Invertible (X.transpose * X)) :
  (X * A) * ((X * A).transpose * (X * A))⁻¹ * (X * A).transpose =
  X * (X.transpose * X)⁻¹ * X.transpose := by
  sorry







theorem theorem_389837_problem
  (p q g y₁ y₂ : ℝ → ℝ)
  (h_diff_y1 : ContDiff ℝ 2 y₁)
  (h_diff_y2 : ContDiff ℝ 2 y₂)
  (h_hom_y1 : ∀ x, deriv (deriv y₁) x + p x * deriv y₁ x + q x * y₁ x = 0)
  (h_hom_y2 : ∀ x, deriv (deriv y₂) x + p x * deriv y₂ x + q x * y₂ x = 0)
  (W : ℝ → ℝ)
  (hW : ∀ x, W x = y₁ x * deriv y₂ x - y₂ x * deriv y₁ x)
  (hW_ne_zero : ∀ x, W x ≠ 0)
  (u v : ℝ → ℝ)
  (h_diff_u : Differentiable ℝ u)
  (h_diff_v : Differentiable ℝ v)
  (hu : ∀ x, deriv u x = (y₂ x * g x) / W x)
  (hv : ∀ x, deriv v x = (y₁ x * g x) / W x)
  (Yp : ℝ → ℝ)
  (hYp : ∀ x, Yp x = -y₁ x * u x + y₂ x * v x) :
  ∀ x, deriv (deriv Yp) x + p x * deriv Yp x + q x * Yp x = g x := by
  sorry









theorem theorem_392773_problem {k : Type*} [Field k] {n : ℕ}
  (A : Matrix (Fin n) (Fin n) k) :
  ∃ P : Matrix (Fin n) (Fin n) k, IsUnit P ∧ A.transpose = P * A * P⁻¹ := by
  sorry







