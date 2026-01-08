import Mathlib
import Mathlib.Tactic

















theorem theorem_392699_problem :
  TopologicalSpace.SeparableSpace (ContinuousMap { x : ℝ // 0 ≤ x } ℝ) := by
  sorry



theorem theorem_391124_problem 
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : E → ℝ) (G : E → E) (V : E)
  (hf : DifferentiableAt ℝ f V)
  (hG : DifferentiableAt ℝ G V) :
  fderiv ℝ (fun x ↦ f x • G x) V = 
  (fderiv ℝ f V).smulRight (G V) + f V • fderiv ℝ G V := by
  sorry

theorem theorem_391006_problem
  (F : Type*) [Field F]
  (G : Type*) [Group G] [Fintype G]
  (V₁ : Type*) [AddCommGroup V₁] [Module F V₁]
  (ρ₁ : Representation F G V₁) :
  ∃ ρ₂ : Representation F G (V₁ × V₁),
    ∀ g : G, ρ₂ g = LinearMap.prodMap (ρ₁ g) (ρ₁ g) := by
  sorry

theorem theorem_393630_problem (P n : ℕ) (p : ℝ) (x1 x2 : Fin n → ZMod 2)
  (hp : 0 ≤ p ∧ p ≤ 1)
  (m : ℕ) (hm : m = (Finset.univ.filter (fun i => (x1 + x2) i ≠ 0)).card) :
  (∑ k in Finset.range (m + 1), if Even k then (Nat.choose m k : ℝ) * p ^ k * (1 - p) ^ (m - k) else 0) ^ P =
  ((1 / 2 : ℝ) * (1 + (1 - 2 * p) ^ m)) ^ P := by
  sorry











theorem theorem_393029_problem
  (X Y : Type*)
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  (T : X →L[ℝ] Y)
  (x_n : ℕ → X) (x : X)
  (h_weak_conv : ∀ f : X →L[ℝ] ℝ, Filter.Tendsto (fun n ↦ f (x_n n)) Filter.atTop (nhds (f x))) :
  ∀ g : Y →L[ℝ] ℝ, Filter.Tendsto (fun n ↦ g (T (x_n n))) Filter.atTop (nhds (g (T x))) := by
  sorry



theorem theorem_390561_problem
  (V : Type*) [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] [Nontrivial V]
  (F : Set (Module.End ℂ V))
  (h_comm : ∀ f g, f ∈ F → g ∈ F → f * g = g * f) :
  ∃ v : V, v ≠ 0 ∧ ∀ f ∈ F, ∃ c : ℂ, f v = c • v := by
  sorry













theorem theorem_393730_problem (m₁ m₂ : ℝ) (h_mass : m₁ + m₂ ≠ 0) :
  let V := Fin 2 → ℝ
  -- Define the map from (v₁, v₂) to v_g = (m₁v₁ + m₂v₂)/(m₁ + m₂)
  let v_g_map : (V × V) →ₗ[ℝ] V :=
    (m₁ / (m₁ + m₂)) • LinearMap.fst ℝ V V + (m₂ / (m₁ + m₂)) • LinearMap.snd ℝ V V
  -- Define the map from (v₁, v₂) to v_rel = v₁ - v₂
  let v_rel_map : (V × V) →ₗ[ℝ] V :=
    LinearMap.fst ℝ V V - LinearMap.snd ℝ V V
  -- The combined transformation (v₁, v₂) ↦ (v_g, v_rel)
  let transform : (V × V) →ₗ[ℝ] (V × V) := LinearMap.prod v_g_map v_rel_map
  -- The problem asks for the Jacobian of the inverse transformation: {v_g, v} → {v₁, v₂}.
  -- This is equal to (det(transform))⁻¹.
  (LinearMap.det transform)⁻¹ = 1 := by
  sorry













theorem theorem_393920_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : E → E) (x : ℝ → E) (t : ℝ)
  (hf : ContDiff ℝ ⊤ f)
  (hx : ContDiff ℝ ⊤ x)
  (h_ode : ∀ s, deriv x s = f (x s)) :
  iteratedDeriv 1 x t = f (x t) ∧
  iteratedDeriv 2 x t = (fderiv ℝ f (x t)) (f (x t)) ∧
  iteratedDeriv 3 x t = (iteratedFDeriv ℝ 2 f (x t)) ![f (x t), f (x t)] +
    (fderiv ℝ f (x t)) ((fderiv ℝ f (x t)) (f (x t))) ∧
  iteratedDeriv 4 x t = (iteratedFDeriv ℝ 3 f (x t)) ![f (x t), f (x t), f (x t)] +
    3 • (iteratedFDeriv ℝ 2 f (x t)) ![(fderiv ℝ f (x t)) (f (x t)), f (x t)] +
    (fderiv ℝ f (x t)) ((iteratedFDeriv ℝ 2 f (x t)) ![f (x t), f (x t)]) +
    (fderiv ℝ f (x t)) ((fderiv ℝ f (x t)) ((fderiv ℝ f (x t)) (f (x t)))) := by
  sorry



theorem theorem_390937_problem
  (U V : Type*)
  [AddCommGroup U] [Module ℝ U]
  [AddCommGroup V] [Module ℝ V]
  (A_h : U →ₗ[ℝ] U)
  (P : V →ₗ[ℝ] U)
  (R : U →ₗ[ℝ] V)
  (A_2h : V →ₗ[ℝ] V)
  (h_def : A_2h = R ∘ₗ A_h ∘ₗ P) :
  A_2h = R ∘ₗ A_h ∘ₗ P := by
  sorry



theorem theorem_392289_problem
  (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : A.PosSemidef)
  (f : ℝ → ℝ)
  (hf : ∀ ε, f ε = Matrix.det (ε • (1 : Matrix (Fin n) (Fin n) ℝ) + A) - ε ^ n) :
  MonotoneOn f {ε | 0 ≤ ε} := by
  sorry

theorem theorem_392965_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
  (h : ∀ i j, A i j ≤ B i j) :
  A.trace ≤ B.trace := by
  sorry

















theorem theorem_390955_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (u v w : E)
  (a b c : ℝ)
  (hu : ‖u‖ = 1)
  (hv : ‖v‖ = 1)
  (hw : ‖w‖ = 1)
  (h_cos_a : inner u v = Real.cos a)
  (h_cos_b : inner u w = Real.cos b)
  (h_cos_c : inner v w = Real.cos c)
  (h_sin_a : Real.sin a ≠ 0)
  (h_sin_b : Real.sin b ≠ 0)
  (ta tb : E)
  (hta : ta = (Real.sin a)⁻¹ • (v - (Real.cos a) • u))
  (htb : tb = (Real.sin b)⁻¹ • (w - (Real.cos b) • u)) :
  Real.cos c = Real.cos a * Real.cos b + Real.sin a * Real.sin b * inner ta tb := by
  sorry





theorem theorem_393793_problem
  (b : Fin 3 → ℂ)
  (hQ : ∀ x, 1 - x - x^3 = ∏ i, (b i - x))
  (h_distinct : Function.Injective b)
  (a₀ : ℂ)
  (h_a₀ : a₀ = 1 / ∏ i, (b i - 1))
  (a : Fin 3 → ℂ)
  (h_a : ∀ k, a k = 1 / ((1 - b k) * ∏ j in Finset.univ.erase k, (b j - b k))) :
  ∀ x, x ≠ 1 → (∀ i, x ≠ b i) →
    1 / ((1 - x) * (1 - x - x^3)) = a₀ / (1 - x) + ∑ i, a i / (b i - x) := by
  sorry

theorem theorem_393088_problem
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  (f : E × G → ℝ) (A : E) (B : G)
  (h_smooth : ContDiff ℝ ⊤ f) :
  ∀ (H : E) (K : G),
  fderiv ℝ f (A, B) (H, K) =
  inner (gradient (fun x ↦ f (x, B)) A) H +
  inner (gradient (fun y ↦ f (A, y)) B) K := by
  sorry















theorem theorem_391705_problem
  (Lambda_up_down : Fin 4 → Fin 4 → ℝ)
  (Lambda_down_up : Fin 4 → Fin 4 → ℝ)
  (eta : Fin 4 → Fin 4 → ℝ)
  (h_eta : ∀ i j, eta i j = if i = j then (if i = 0 then -1 else 1) else 0)
  (h_relation : ∀ beta nu, Lambda_down_up beta nu = 
    ∑ rho : Fin 4, ∑ sigma : Fin 4, eta beta rho * eta nu sigma * Lambda_up_down rho sigma) :
  ∀ beta nu, ((beta = 0 ∧ nu ≠ 0) ∨ (beta ≠ 0 ∧ nu = 0)) →
    Lambda_down_up beta nu = - Lambda_up_down nu beta := by
  sorry

theorem theorem_390838_problem
  (n : ℕ)
  (K : Type*)
  (a : K → ℝ)
  (b : K → (Fin n → ℝ))
  (f : K → (Fin n → ℝ) → ℝ)
  (k j : K)
  (h_def : ∀ (i : K) (x : Fin n → ℝ), f i x = a i + Matrix.dotProduct (b i) x) :
  {x : Fin n → ℝ | f k x = f j x} =
  {x : Fin n → ℝ | Matrix.dotProduct (b k - b j) x + (a k - a j) = 0} := by
  sorry









theorem theorem_395043_problem (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
  (h : ∃ i j : Fin n, i ≠ j ∧ M i = M j) :
  M.det = 0 := by
  sorry

theorem theorem_394707_problem (n : ℕ) (A B x : Matrix (Fin n) (Fin n) ℝ)
  (hA_symm : A.IsSymm) (hA_pos : A.PosDef)
  (hB_symm : B.IsSymm) (hB_pos : B.PosDef)
  (hA_eq : A = 1) (hB_eq : B = 1) :
  x.transpose * x = 1 ↔ x ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  sorry

theorem theorem_396143_problem (A B : Matrix (Fin 2) (Fin 2) ℝ)
  (hA : A = !![1, 0; 0, 2])
  (hB : B = !![3, 1; 1, 3]) :
  A * B ≠ B * A := by
  sorry

theorem theorem_394420_problem (K : Type*) [Field K] (n : ℕ)
  (A P : Matrix (Fin n) (Fin n) K) (hP : IsUnit P) :
  Matrix.det (P⁻¹ * A * P) = Matrix.det A := by
  sorry

theorem theorem_395663_problem (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Nontrivial V] :
  ∃ f : V → V, (∀ x, ‖f x‖ = ‖x‖) ∧ ¬ IsLinearMap ℝ f := by
  sorry







theorem theorem_396644_problem
  {α : Type*}
  (A : Set α)
  (f g : ℕ → α → ℝ)
  (h_bound : ∀ n, ∀ x ∈ A, |f n x| ≤ g n x)
  (h_g_conv : ∃ G, TendstoUniformlyOn (fun n ↦ ∑ i in Finset.range n, g i) G Filter.atTop A) :
  ∃ F, TendstoUniformlyOn (fun n ↦ ∑ i in Finset.range n, f i) F Filter.atTop A := by
  sorry

theorem theorem_395994_problem
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (E : Submodule ℝ X)
  (h_codim : Module.rank ℝ (X ⧸ E) < Cardinal.continuum)
  (h_ker : ∃ φ : X →ₗ[ℝ] ℝ, ¬ Continuous φ ∧ E = LinearMap.ker φ)
  (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  (f : E →L[ℝ] Y) :
  IsOpenMap f := by
  sorry











theorem theorem_394823_problem (n : ℕ) (b : Fin n → ℝ) (v : ℝ) 
  (hb : b ≠ 0) :
  let H : Set (Fin n → ℝ) := {x | Matrix.dotProduct b x = v}
  FiniteDimensional.finrank ℝ (AffineSubspace.direction (affineSpan ℝ H)) = n - 1 := by
  sorry



theorem theorem_393310_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (x y z : E) (a : ℝ)
  (h_ne : a ≠ 1)
  (h_cond : ‖x - y‖ = a * ‖x - z‖) :
  ‖x - (1 - a ^ 2)⁻¹ • (y - a ^ 2 • z)‖ =
  Real.sqrt (‖y - a ^ 2 • z‖ ^ 2 / (1 - a ^ 2) ^ 2 - (‖y‖ ^ 2 - a ^ 2 * ‖z‖ ^ 2) / (1 - a ^ 2)) := by
  sorry







theorem theorem_396187_problem (n : ℕ)
  (g h : Matrix (Fin n) (Fin n) ℝ)
  (hg_symm : g.IsSymm)
  (hg_posdef : g.PosDef)
  (h_inv : h * g = 1) :
  ∑ i, ∑ j, h i j * g i j = (n : ℝ) := by
  sorry

theorem theorem_394379_problem (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (L : Matrix (Fin n) (Fin n) ℝ)
  (hL : ∀ i j, L i j = if i = j then (G.degree i : ℝ) else (if G.Adj i j then -1 else 0))
  (d : Fin n → ℝ)
  (hd_perm : ∃ σ : Equiv.Perm (Fin n), ∀ i, d i = (G.degree (σ i) : ℝ))
  (hd_mono : Monotone d)
  (μ : Fin n → ℝ)
  (hμ_eig : Multiset.map μ Finset.univ.val = L.charpoly.roots)
  (hμ_mono : Monotone μ) :
  ∀ i, μ i ≤ 2 * d i := by
  sorry

theorem theorem_397595_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
  (A : X →L[𝕜] X)
  (X₂ : Submodule 𝕜 X)
  (h_closed : IsClosed (X₂ : Set X))
  (h_inv : ∀ x ∈ X₂, A x ∈ X₂)
  (h_compact : IsCompactOperator A) :
  IsCompactOperator (A.restrict (by intros x hx; exact h_inv x hx)) := by
  sorry

theorem theorem_395414_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (b : ℝ) (hb : 0 < b)
  (h_space : ∀ x y : E, ‖x + y‖^2 + b * ‖x - y‖^2 ≤ 2 * ‖x‖^2 + 2 * ‖y‖^2)
  (x y : E) (n : ℕ) (hn : 1 ≤ n) :
  ‖x + y‖^2 - ‖x‖^2 ≥
  b * (1 - (1 : ℝ) / (2 ^ (n + 1))) * ‖y‖^2 +
  (2 ^ (n + 1) : ℝ) * (‖x + ((1 : ℝ) / (2 ^ (n + 1))) • y‖^2 - ‖x‖^2) := by
  sorry



theorem theorem_397608_problem (n k : ℕ)
  (V : Type*) [AddCommGroup V] [Module ℝ V]
  (A : (Fin n → ℝ) →ₗ[ℝ] V)
  (v : Fin k → (Fin n → ℝ))
  (hv : LinearIndependent ℝ v)
  (hA : Function.Injective A) :
  LinearIndependent ℝ (A ∘ v) := by
  sorry





theorem theorem_396545_problem
  {K : Type*} [Field K] [CharZero K]
  {d : ℕ} (hd : 1 < d)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (S : ι → Matrix (Fin d) (Fin d) K)
  (hS_traceless : ∀ i, Matrix.trace (S i) = 0)
  (f : K) (hf : f = (d : K) * ((d : K) ^ 2 - 1) / 12)
  (hS_orth : ∀ i j, Matrix.trace (S i * S j) = if i = j then f else 0)
  (M : Matrix (Fin d) (Fin d) K)
  (a : K) (b : ι → K)
  (hM : M = a • (1 : Matrix (Fin d) (Fin d) K) + ∑ i, b i • S i) :
  ∀ i, b i = Matrix.trace (S i * M) / f := by
  sorry

theorem theorem_396201_problem
  -- We model H¹(Ω) as a Hilbert space V
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  -- Abstract representations of the integral terms: ∫∇u·∇v and ∫uv on boundary
  (int_grad : V → V → ℝ)
  (int_bound : V → V → ℝ)
  -- Properties of these integrals (non-negative quadratic forms)
  (h_grad_nonneg : ∀ v, 0 ≤ int_grad v v)
  (h_bound_nonneg : ∀ v, 0 ≤ int_bound v v)
  -- The "sufficiently smooth boundary" condition implies a Trace-Poincaré type inequality
  -- relating these integrals to the H¹ norm.
  (h_smooth_domain : ∃ C > 0, ∀ v, int_grad v v + int_bound v v ≥ C * ‖v‖^2)
  -- Condition: α ≥ 1
  (α : ℝ) (hα : α ≥ 1)
  -- Definition of the bilinear form b
  (b : V → V → ℝ)
  (hb : ∀ u v, b u v = int_grad u v + α * int_bound u v) :
  -- Conclusion: b is coercive
  ∃ C1 > 0, ∀ v, b v v ≥ C1 * ‖v‖^2 := by
  sorry



theorem theorem_397344_problem (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℝ) 
  (hX : 0 < X.det) : 
  deriv (fun ε : ℝ => Real.log (Matrix.det (X + ε • Y))) 0 = Matrix.trace (X⁻¹ * Y) := by
  sorry

theorem theorem_396750_problem (n : ℕ)
  (X Y : Fin n → ℝ)
  (D2f : Fin n → Fin n → ℝ) :
  ∑ a : Fin n, ∑ b : Fin n, (X b * Y a * D2f b a - Y b * X a * D2f b a) =
  ∑ a : Fin n, ∑ b : Fin n, -X a * Y b * (D2f b a - D2f a b) := by
  sorry

