import Mathlib
import Mathlib.Tactic

theorem theorem_284650_problem
  (n : ℕ)
  {K : Type*} [Field K] [DecidableEq K]
  (X_G : Matrix (Fin n) (Fin n) K)
  (σ : Equiv.Perm (Fin n))
  (P : Matrix (Fin n) (Fin n) K)
  (hP : P = Matrix.of (fun i j => if i = σ j then (1 : K) else 0))
  (X_G_sigma : Matrix (Fin n) (Fin n) K)
  (h_def : X_G_sigma = P * X_G * P⁻¹) :
  X_G_sigma.det = X_G.det := by
  sorry





theorem theorem_284715_problem
  (n : ℕ)
  (c : ℝ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hc : 0 < c)
  (h_col : ∀ j, Real.sqrt (∑ i, (A i j) ^ 2) ≤ c * Real.sqrt (n : ℝ)) :
  |A.det| ≤ (c * Real.sqrt (n : ℝ)) ^ n := by
  sorry



theorem theorem_285029_problem (m : ℕ)
  (u v : Fin 100 → ℝ)
  (hu : ∀ j : Fin 100, u j = Real.cos (j : ℝ))
  (hv : ∀ j : Fin 100, v j = Real.sin (j : ℝ))
  (A : Matrix (Fin m) (Fin 100) ℝ)
  (hA : ∀ i : Fin m, A i = (Real.sin (100 * (i : ℝ))) • u + (Real.cos (100 * (i : ℝ))) • v) :
  A.rank ≤ 2 := by
  sorry

theorem theorem_285043_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  (T : V → W)
  (h : ∀ (x y : V) (α : K), T (α • x + y) = α • T x + T y) :
  IsLinearMap K T := by
  sorry



theorem theorem_284840_problem
  {n m : Type*} [NormedAddCommGroup n] [NormedSpace ℝ n] [FiniteDimensional ℝ n]
  [NormedAddCommGroup m] [NormedSpace ℝ m]
  (f : n → ℝ → m → n)
  (z : ℝ → n)
  (θ : m)
  (a : ℝ → (n →L[ℝ] ℝ)) -- a(t) is a dual vector (row vector)
  -- Condition: f is differentiable wrt state z (sufficient for Jacobian to exist)
  (hf : ∀ t, DifferentiableAt ℝ (fun x => f x t θ) (z t))
  -- Condition: z satisfies the system dynamics
  (hz : ∀ t, HasDerivAt z (f (z t) t θ) t)
  -- Condition: Definition of costate behavior relative to perturbation.
  -- The pairing a(t) * δz(t) is invariant for any valid perturbation δz.
  (h_costate : ∀ (δz : ℝ → n),
    (∀ t, HasDerivAt δz (fderiv ℝ (fun x => f x t θ) (z t) (δz t)) t) →
    (∀ t, HasDerivAt (fun t => a t (δz t)) 0 t))
  -- Condition: a(t) is differentiable (assumed for the equation to exist)
  (ha_diff : ∀ t, DifferentiableAt ℝ a t) :
  -- Conclusion: a'(t) = - a(t) * (∂f/∂z)
  ∀ t, HasDerivAt a (- (a t).comp (fderiv ℝ (fun x => f x t θ) (z t))) t := by
  sorry

theorem theorem_285281_problem
  (n : ℕ)
  {K : Type*} [Field K]
  (A B : Matrix (Fin n) (Fin n) K)
  (h : IsUnit (A + B)) :
  B * (A + B)⁻¹ * A = A * (A + B)⁻¹ * B := by
  sorry



















theorem theorem_284936_problem {I : Type*} (x : I → ℝ) :
  IsLinearMap ℝ (fun (y : ℝ) => (fun (i : I) => x i * y)) := by
  sorry



theorem theorem_284984_problem
  {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (Λ : X →ₗ[ℝ] Y)
  (ρ : ℝ) (hρ : 0 < ρ)
  (h : ∀ y ∈ Metric.ball (0 : Y) 1, ∃ x ∈ Metric.ball (0 : X) ρ, Λ x = y) :
  Metric.ball (0 : Y) 1 ⊆ Λ '' (Metric.ball (0 : X) ρ) := by
  sorry



theorem theorem_285957_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  (u : ℕ → X) (u_lim : X)
  (T : ℕ → X →L[𝕜] Y) (T_lim : X →L[𝕜] Y)
  (h_u : Filter.Tendsto u Filter.atTop (nhds u_lim))
  (h_T : Filter.Tendsto T Filter.atTop (nhds T_lim)) :
  Filter.Tendsto (fun n => T n (u n)) Filter.atTop (nhds (T_lim u_lim)) := by
  sorry

theorem theorem_286032_problem (f : ℂ → ℂ)
  (h1 : Differentiable ℂ f)
  (h2 : ∃ M : ℝ, ∀ z : ℂ, Complex.abs (f z) ≤ M) :
  ∃ c : ℂ, ∀ z : ℂ, f z = c := by
  sorry

theorem theorem_285549_problem
  {F : Type*} [Field F]
  (p₁ p₂ p₃ q₁ q₂ q₃ : Polynomial F)
  (x y z : RatFunc F)
  (W X Y Z : Polynomial F)
  (hq1 : q₁ ≠ 0) (hq2 : q₂ ≠ 0) (hq3 : q₃ ≠ 0)
  (hx : x = (p₁ : RatFunc F) / (q₁ : RatFunc F))
  (hy : y = (p₂ : RatFunc F) / (q₂ : RatFunc F))
  (hz : z = (p₃ : RatFunc F) / (q₃ : RatFunc F))
  (hW : W = q₁ * q₂ * q₃)
  (hX : X = p₁ * q₂ * q₃)
  (hY : Y = q₁ * p₂ * q₃)
  (hZ : Z = q₁ * q₂ * p₃) :
  x = (X : RatFunc F) / (W : RatFunc F) ∧
  y = (Y : RatFunc F) / (W : RatFunc F) ∧
  z = (Z : RatFunc F) / (W : RatFunc F) := by
  sorry









theorem theorem_286090_problem
  {K : Type*} [Field K]
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (M : Matrix m n K) :
  M.rank = M.transpose.rank := by
  sorry



theorem theorem_285777_problem
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (f : E → F) (A : Set E)
  (hA : IsCompact A)
  (h_diff : ContDiffOn ℝ 1 f A) :
  ∃ M : ℝ, M > 0 ∧ ∀ x ∈ A, ∀ y ∈ A, ‖f x - f y‖ ≤ M * ‖x - y‖ := by
  sorry

theorem theorem_286097_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι]
  (w : ι → ι → ℝ)
  (x : ι → E)
  (i : ι) :
  ‖∑ j, w i j • (x i - x j)‖^2 =
  ∑ j, ∑ k, w i j * w i k * inner (x i - x j) (x i - x k) := by
  sorry









theorem theorem_285958_problem
  {M R : Type*} [Ring M] [Ring R]
  (φ : M →+* R) -- Embedding of matrices into the operator ring
  (D : R)
  (deriv : M → M) -- Component-wise derivative map
  (h_product_rule : ∀ A : M, D * φ A = φ (deriv A) + φ A * D) -- The product rule DA = A' + AD
  (n r s : ℕ) (hn : n > 0) (hr : r > 0) (hs : s > 0)
  (A : M) :
  ∃ (F : ℕ → M), -- F_j are matrices
    D^s * (φ A * D^n)^r = φ (A^r) * D^(s + r * n) +
    ∑ j in Finset.range (s + r * n), φ (F j) * D^j := by
  sorry

theorem theorem_286062_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {ι : Type*} (B : Basis ι F V)
  (f : ℕ ↪ ι) :
  (⋃ i : ℕ, (Submodule.span F (Set.range B \ {B (f i)}) : Set V)) = Set.univ := by
  sorry













theorem theorem_286773_problem
  {I L : Type*}
  (C : L → Set I)
  (pi : L → I → ℝ)
  (h_disjoint : ∀ l₁ l₂, l₁ ≠ l₂ → Disjoint (C l₁) (C l₂))
  (h_supp : ∀ l i, i ∉ C l → pi l i = 0)
  (h_nonzero : ∀ l, pi l ≠ 0) :
  LinearIndependent ℝ pi := by
  sorry

theorem theorem_286651_problem
  (n : ℕ)
  (t : ℝ)
  (ht : t > 0)
  (B : Matrix (Fin n.succ) (Fin n.succ) ℝ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : A = B.submatrix Fin.succ Fin.succ)
  (C : Matrix (Fin n.succ) (Fin n.succ) ℝ)
  (hC : C = B - (Real.sqrt t - (Real.sqrt t)⁻¹) • Matrix.stdBasisMatrix 0 0 1) :
  C.det = -(Real.sqrt t - (Real.sqrt t)⁻¹) * A.det + B.det := by
  sorry

theorem theorem_286772_problem (n : ℕ) (α : ℝ)
  (h1 : 1 + ((n : ℝ) - 1) * α ≠ 0)
  (h2 : α ≠ 1) :
  let J : Matrix (Fin n) (Fin n) ℝ := fun _ _ ↦ 1
  let I : Matrix (Fin n) (Fin n) ℝ := 1
  let B : Matrix (Fin n) (Fin n) ℝ := (1 / (1 - α)) • (I - (α / (1 + ((n : ℝ) - 1) * α)) • J)
  α • (B * J) + (1 - α) • B = I := by
  sorry











theorem theorem_287084_problem
  (X Y : ℕ → Type*)
  [∀ n, AddCommGroup (X n)]
  [∀ n, AddCommGroup (Y n)]
  (f : ∀ n, X (n + 1) →+ X n)
  (g : ∀ n, Y (n + 1) →+ Y n)
  (hf : ∀ n, (f (n + 1)).range = (f n).ker)
  (hg : ∀ n, (g (n + 1)).range = (g n).ker) :
  let h : ∀ n, X (n + 1) × Y (n + 1) →+ X n × Y n := fun n ↦ (f n).prodMap (g n)
  ∀ n, (h (n + 1)).range = (h n).ker := by
  sorry

theorem theorem_286953_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (M : ℕ → H) (M_inf M'_inf : H)
  (h1 : Filter.Tendsto M Filter.atTop (nhds M_inf))
  (h2 : Filter.Tendsto M Filter.atTop (nhds M'_inf)) :
  M_inf = M'_inf := by
  sorry



theorem theorem_286393_problem {n : Type*} [Fintype n] [DecidableEq n]
  (A B : Matrix n n ℝ) (hA : A.PosDef) (hB : B.IsSymm) :
  ((A * B).charpoly.roots.countP (fun x => 0 < x) = B.charpoly.roots.countP (fun x => 0 < x)) ∧
  ((A * B).charpoly.roots.countP (fun x => x < 0) = B.charpoly.roots.countP (fun x => x < 0)) ∧
  ((A * B).charpoly.roots.countP (fun x => x = 0) = B.charpoly.roots.countP (fun x => x = 0)) := by
  sorry





theorem theorem_287468_problem (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ)
  (h_symm : S.IsSymm)
  (h_pos_def : S.PosDef) :
  ∃! G : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j : Fin n, i < j → G i j = 0) ∧
    (∀ i : Fin n, 0 < G i i) ∧
    S = G * G.transpose := by
  sorry







theorem theorem_286813_problem (u : ℝ → ℝ → ℝ) (u₀ : ℝ)
  (h_pde : ∀ x t, 1 < x → x < Real.exp 1 → 0 < t →
    deriv (fun τ => u x τ) t - x^2 * deriv (fun ξ => deriv (fun y => u y t) ξ) x - 2 * x * deriv (fun ξ => u ξ t) x = 0)
  (h_bc1 : ∀ t > 0, u 1 t = 0)
  (h_bc2 : ∀ t > 0, u (Real.exp 1) t = 0)
  (h_ic : ∀ x, 1 < x → x < Real.exp 1 → u x 0 = u₀) :
  ∀ x t, 1 < x → x < Real.exp 1 → 0 < t →
    u x t = ∑' s : ℕ,
      if s = 0 then 0 else
      (8 * u₀ * Real.pi * s * (1 - Real.exp (1/2 : ℝ) * (-1 : ℝ)^s) *
       Real.exp (- (t * (4 * Real.pi^2 * s^2 + 1)) / 4) *
       Real.sin (Real.pi * s * Real.log x)) /
      (Real.sqrt x * (4 * Real.pi^2 * s^2 + 1)) := by
  sorry



theorem theorem_287569_problem (n : ℕ) {R : Type*} [Field R]
  (A B C : Matrix (Fin n) (Fin n) R)
  (h1 : A * B = C)
  (h2 : IsUnit B) :
  A = C * B⁻¹ := by
  sorry



theorem theorem_287793_problem
  (n : ℕ)
  (hn : n > 0)
  (S : Set (Matrix (Fin n) (Fin n) ℝ))
  (A : Matrix (Fin n) (Fin n) ℝ)
  (j : Fin n)
  (B : Matrix (Fin n) (Fin n) ℝ)
  (hS_nonempty : S.Nonempty)
  (hA_mem : A ∈ S)
  (hA_nonzero : A ≠ 0)
  (hB_def : B = Matrix.stdBasisMatrix j ⟨0, hn⟩ 1)
  (h_prod_not_mem : A * B ∉ S) :
  ¬ (∀ (M : Matrix (Fin n) (Fin n) ℝ) (N : Matrix (Fin n) (Fin n) ℝ), M ∈ S → M * N ∈ S) := by
  sorry



theorem theorem_287737_problem (n : ℕ) (X Y Z : Matrix (Fin n) (Fin n) (ZMod 5))
  (hn : n ≠ 0)
  (h_neq : X * Y ≠ Z) :
  (Fintype.card {v : Fin n → ZMod 5 // Matrix.mulVec (X * Y) v ≠ Matrix.mulVec Z v} : ℚ) /
  (Fintype.card (Fin n → ZMod 5) : ℚ) ≥ 4 / 5 := by
  sorry













theorem theorem_287476_problem
  (φ : ℝ → ℝ) (ε : ℝ → ℝ)
  (hφ : Continuous φ)
  (hε : Continuous ε)
  (hε_pos : ∀ x, 0 < ε x) :
  ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ∀ x : ℝ, Complex.abs (f x - φ x) < ε x := by
  sorry



theorem theorem_288290_problem
  (n d : ℕ)
  (x : Fin n → Fin d → ℝ)
  (G : Matrix (Fin n) (Fin n) ℝ)
  (hG : ∀ i j, G i j = Matrix.dotProduct (x i) (x j))
  (g : Fin n → ℝ)
  (hg : ∀ i, g i = G i i)
  (one : Fin n → ℝ)
  (hone : ∀ i, one i = 1)
  (D : Matrix (Fin n) (Fin n) ℝ)
  (hD : ∀ i j, D i j = Matrix.dotProduct (x i - x j) (x i - x j)) :
  D = Matrix.vecMulVec g one + Matrix.vecMulVec one g - (2 : ℝ) • G := by
  sorry













theorem theorem_288273_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) :
  Matrix.rank A = Matrix.rank (Matrix.map A (algebraMap ℚ ℝ)) := by
  sorry



theorem theorem_288725_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (M N : Submodule ℝ E) (h : M ≤ N) :
  (M.subtype.comp (orthogonalProjection M).toLinearMap).comp (N.subtype.comp (orthogonalProjection N).toLinearMap) =
  (M.subtype.comp (orthogonalProjection M).toLinearMap) := by
  sorry

theorem theorem_288577_problem (a b c : ℂ) :
  (∃! v : ℝ × ℝ, 
    (a.re + b.re) * v.1 + (-a.im + b.im) * v.2 = c.re ∧ 
    (a.im + b.im) * v.1 + (a.re - b.re) * v.2 = c.im) ↔ 
  Complex.abs a ≠ Complex.abs b := by
  sorry

theorem theorem_288743_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  (S : Set V)
  (h_count : S.Countable)
  (h_inf : S.Infinite)
  (h_li : LinearIndependent F ((↑) : S → V)) :
  ∃ B : Set V, LinearIndependent F ((↑) : B → V) ∧ Submodule.span F B = ⊤ ∧ S ⊆ B := by
  sorry



theorem theorem_289036_problem
  (n p c : ℕ)
  (X : Matrix (Fin n) (Fin p) ℝ)
  (y : Matrix (Fin n) (Fin 1) ℝ)
  (beta : Matrix (Fin p) (Fin 1) ℝ)
  (C : Matrix (Fin c) (Fin p) ℝ)
  (d : Matrix (Fin c) (Fin 1) ℝ)
  (RSS_r RSS_f : ℝ)
  (h_n : n > p)
  (h_c : c > 0)
  (h_RSS_f : RSS_f > 0) :
  ∃ F : ℝ, F = ((RSS_r - RSS_f) / (c : ℝ)) / (RSS_f / ((n - p) : ℝ)) := by
  sorry



theorem theorem_288581_problem
  {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  (A : Matrix n m ℝ)
  (vnorm : (m → ℝ) → ℝ)
  (mnorm : Matrix m m ℝ → ℝ)
  (h_vnorm_pos : ∀ x, x ≠ 0 → 0 < vnorm x)
  (h_vnorm_hom : ∀ (c : ℝ) x, vnorm (c • x) = |c| * vnorm x)
  (h_induced : ∀ M, mnorm M = sSup {r | ∃ x, x ≠ 0 ∧ r = vnorm (M.mulVec x) / vnorm x})
  (h_singular : ∃ x, x ≠ 0 ∧ (A.transpose * A).mulVec x = 0) :
  ∀ α : ℝ, mnorm (α • (A.transpose * A) - 1) ≥ 1 := by
  sorry







theorem theorem_289042_problem
  (n : ℕ) (h_n : 0 < n)
  (ε : ℝ) (h_eps : 0 < ε ∧ ε < 1)
  (A : Matrix (Fin n) (Fin n) ℝ) (hA : Invertible A)
  (P : Matrix (Fin n) (Fin n) ℝ)
  (hP : P = Matrix.diagonal (fun i => if i.val = 0 then ε else 1))
  (hP_inv : Invertible P)
  (e1 : Matrix (Fin n) (Fin 1) ℝ)
  (he1 : e1 = fun i j => if i.val = 0 then 1 else 0)
  (Q : Matrix (Fin n) (Fin n) ℝ)
  (hQ : Q = A * P + ((n : ℝ) ^ 2 * (1 - ε)) • (e1 * e1.transpose)) :
  Q.det = ε * A.det * (1 + (n : ℝ) ^ 2 * (1 - ε) * (e1.transpose * P⁻¹ * A⁻¹ * e1) 0 0) := by
  sorry



