import Mathlib
import Mathlib.Tactic















theorem theorem_345909_problem
  {F : Type*} [Field F]
  {n : Type*} [Fintype n] [DecidableEq n]
  (G : Matrix n n F) (hG : IsUnit G)
  (M : Matrix n n F)
  (A B : Matrix n n F)
  (hA : A = G⁻¹)
  (hB : B = M) :
  M = A * G * B := by
  sorry





theorem theorem_345680_problem
  {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  (X : Set E) (Y : Set F)
  (hX : Convex ℝ X) (hY : Convex ℝ Y) :
  convexHull ℝ X ×ˢ convexHull ℝ Y ⊆ convexHull ℝ (X ×ˢ Y) := by
  sorry







theorem theorem_346145_problem (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (h_inf : ¬ FiniteDimensional ℝ E) :
  let weak_topology := TopologicalSpace.induced (fun x (f : E →L[ℝ] ℝ) ↦ f x) inferInstance
  @interior E weak_topology {x : E | ‖x‖ ≤ 1} = ∅ := by
  sorry

theorem theorem_346189_problem (m : ℝ) (A B : ℂ)
  (h : ∀ ϕ : ℝ, (A * Complex.exp (Complex.I * (m : ℂ) * (ϕ : ℂ)) + 
                 B * Complex.exp (-Complex.I * (m : ℂ) * (ϕ : ℂ))).im = 0) :
  A = star B := by
  sorry







theorem theorem_346164_problem
  (A : ℕ → (Fin 3 → ℝ)) -- Vertices of the polyhedron
  (A0 : Fin 3 → ℝ)      -- Fixed reference point
  (ι : Type*) [Fintype ι] -- Finite set of tetrahedra indices
  (l m k : ι → ℕ)       -- Indices l_i, m_i, n_i for each tetrahedron
  (V : ℝ)               -- The volume of the polyhedron
  -- Definition of the oriented volume of a tetrahedron given in the context
  (vol_tetra : (Fin 3 → ℝ) → (Fin 3 → ℝ) → (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ)
  (h_vol_def : ∀ (p0 p1 p2 p3 : Fin 3 → ℝ),
    vol_tetra p0 p1 p2 p3 = (1 / 6) * Matrix.det ![(p1 - p0), (p2 - p0), (p3 - p0)])
  -- Condition: P is decomposed into tetrahedra such that V is the sum of their oriented volumes
  (h_decomp : V = ∑ i : ι, vol_tetra A0 (A (l i)) (A (m i)) (A (k i))) :
  V = (1 / 6) * ∑ i : ι, Matrix.det ![(A (l i) - A0), (A (m i) - A0), (A (k i) - A0)] := by
  sorry

theorem theorem_346311_problem (X1 X2 A B : ℝ → ℝ)
  (hA : ∀ t, A t = (X1 t + X2 t) / Real.sqrt 2)
  (hB : ∀ t, B t = (X1 t - X2 t) / Real.sqrt 2) :
  ∀ t, (X1 t)^2 + (X2 t)^2 = (A t)^2 + (B t)^2 := by
  sorry



theorem theorem_344907_problem {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
  (W₁ W₂ : Submodule F E) :
  (W₁ ⊓ W₂).dualAnnihilator = W₁.dualAnnihilator ⊔ W₂.dualAnnihilator := by
  sorry



theorem theorem_345271_problem
  (m n : ℕ)
  (M : Matrix (Fin m) (Fin n) ℝ)
  (x : Fin m → ℝ)
  (hM : ∀ i j, 0 < M i j)
  (hx : ∀ i, 0 < x i) :
  ∃ a_star : Fin n → ℝ,
    (Matrix.mulVec M a_star ≤ x ∧ 0 ≤ a_star) ∧
    ∀ a : Fin n → ℝ, (Matrix.mulVec M a ≤ x ∧ 0 ≤ a) →
      Matrix.dotProduct (Matrix.vecMul (fun _ ↦ 1) M) a_star ≤
      Matrix.dotProduct (Matrix.vecMul (fun _ ↦ 1) M) a := by
  sorry

theorem theorem_346573_problem (D : ℝ → ℝ)
  (h1 : ∀ q : ℚ, D q = 1)
  (h2 : ∀ x : ℝ, Irrational x → D x = 0) :
  ∀ x : ℝ, ¬ ContinuousAt D x := by
  sorry











theorem theorem_347028_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (h_char : ringChar F ≠ 2)
  (b : V →ₗ[F] V →ₗ[F] F)
  (h_symm : ∀ x y, b x y = b y x)
  (x y : V) :
  b x y = (2 : F)⁻¹ * (b (x + y) (x + y) - b x x - b y y) := by
  sorry









theorem theorem_346848_problem 
  (x y x' y' : ℝ)
  (θ : ℝ)
  (hθ : θ = Real.arctan 0.02222)
  (h_trans_x : x' - 10 = (x - 10) * Real.cos θ - (y - 0.1773) * Real.sin θ)
  (h_trans_y : y' - 0.1773 = (x - 10) * Real.sin θ + (y - 0.1773) * Real.cos θ)
  (f : ℝ → ℝ)
  (hf : ∀ t, f t = -5 * (10 : ℝ)^(-6 : ℤ) * t^3 + 0.0004 * t^2 + 0.0582 * t - 0.4397) :
  y' = f x' ↔ y' = -5 * (10 : ℝ)^(-6 : ℤ) * x'^3 + 0.0004 * x'^2 + 0.0582 * x' - 0.4397 := by
  sorry







theorem theorem_346718_problem (y ε : ℤ → ℝ) (Φ₁ Φ₂ θ₁ Θ₁ Θ₂ c : ℝ) :
  let seasonal_AR_part : (ℤ → ℝ) → ℤ → ℝ := fun x t ↦ x t - Φ₁ * x (t - 12) - Φ₂ * x (t - 24)
  let seasonal_diff_part : (ℤ → ℝ) → ℤ → ℝ := fun x t ↦ x t - x (t - 12)
  let MA_part : (ℤ → ℝ) → ℤ → ℝ := fun x t ↦ x t + θ₁ * x (t - 1)
  let seasonal_MA_part : (ℤ → ℝ) → ℤ → ℝ := fun x t ↦ x t + Θ₁ * x (t - 12) + Θ₂ * x (t - 24)
  ∀ t : ℤ,
    seasonal_AR_part (seasonal_diff_part y) t = c + MA_part (seasonal_MA_part ε) t := by
  sorry







theorem theorem_347706_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  (x_seq : ℕ → X) (x : X)
  (h_strong : Filter.Tendsto x_seq Filter.atTop (nhds x))
  (h_weak : ∀ f : X →L[𝕜] 𝕜, Filter.Tendsto (fun n ↦ f (x_seq n)) Filter.atTop (nhds 0)) :
  x = 0 := by
  sorry









theorem theorem_347649_problem
  (n m : ℕ)
  (f : (Fin n → ℝ) → (Fin m → ℝ))
  (x v : Fin n → ℝ)
  (h : DifferentiableAt ℝ f x) :
  HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 := by
  sorry



theorem theorem_348351_problem {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
  (h : U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1) :
  U⁻¹ = U.conjTranspose := by
  sorry

theorem theorem_347716_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  (A : V →L[ℂ] V)
  (ν ρ : ℂ)
  (h_ne : ρ ≠ ν)
  (hν : IsUnit (ν • (1 : V →L[ℂ] V) - A))
  (hρ : IsUnit (ρ • (1 : V →L[ℂ] V) - A)) :
  (ρ - ν)⁻¹ • (Ring.inverse (ν • 1 - A) - Ring.inverse (ρ • 1 - A)) =
  Ring.inverse (ρ • 1 - A) * Ring.inverse (ν • 1 - A) := by
  sorry







theorem theorem_348661_problem (n : ℕ) (x y : Fin n → ℝ)
  (M : Matrix (Fin n) (Fin n) ℝ)
  (h_n : n ≥ 3)
  (h_M : ∀ i j, M i j = Real.cos (x i - y j)) :
  M.det = 0 := by
  sorry





theorem theorem_348773_problem
  {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
  (t1 t2 : TopologicalSpace X)
  (h_weaker : t1 ≤ t2)
  (h_id_closed : @IsClosedMap X X t2 t1 id) :
  t1 = t2 := by
  sorry



theorem theorem_348446_problem
  (a b c : ℝ)
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (S : Set (ℝ × ℝ))
  (hS : S = { p : ℝ × ℝ | a * p.1 + b * p.2 ≤ c }) :
  Convex ℝ S := by
  sorry

theorem theorem_348782_problem (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) :
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![a₁, a₃; 0, a₂]
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![b₁, b₃; 0, b₂]
  let plus_T := (a₁ + b₁, a₂ + b₂, a₃ + b₃)
  let times_T := (a₁ * b₁, a₂ * b₂, a₁ * b₃ + a₃ * b₂)
  let to_matrix (t : ℝ × ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![t.1, t.2.2; 0, t.2.1]
  (to_matrix plus_T = A + B) ∧ 
  (to_matrix times_T = A * B) := by
  sorry





















theorem theorem_349321_problem
  {k E : Type*} [Field k] [AddCommGroup E] [Module k E]
  (R S : Set (E →ₗ[k] k))
  (U V : Set E)
  (hU : U = {x : E | ∀ r ∈ R, r x = 0})
  (hV : V = {x : E | ∀ s ∈ S, s x = 0})
  (h1 : ∀ r ∈ R, r ∈ Submodule.span k S)
  (h2 : ∀ s ∈ S, s ∈ Submodule.span k R) :
  U = V := by
  sorry

theorem theorem_349228_problem
  (b0 b1 b2 b3 b4 b5 : ℝ)
  (H S : ℝ)
  (predicted_outcome : ℝ → ℝ → ℝ)
  (h_model : ∀ X Z : ℝ, predicted_outcome X Z = b0 + b1 * X + b2 * Z + b3 * (X * Z) + b4 * H + b5 * S) :
  predicted_outcome 1 1 - predicted_outcome 1 0 = b2 + b3 := by
  sorry

theorem theorem_349389_problem 
  (R : Matrix (Fin 3) (Fin 3) ℝ)
  (t : Matrix (Fin 3) (Fin 1) ℝ)
  (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
  (T : Matrix (Sum (Fin 3) (Fin 1)) (Sum (Fin 3) (Fin 1)) ℝ)
  (hT : T = Matrix.fromBlocks R t 0 1) :
  T⁻¹ = Matrix.fromBlocks R.transpose (-R.transpose * t) 0 1 := by
  sorry

theorem theorem_349278_problem
  (n : ℕ)
  (U : Set (Fin n → ℝ))
  (hU : IsOpen U)
  (f : (Fin n → ℝ) → ℝ)
  (α : ℝ)
  (hα : 1 < α)
  (h_ineq : ∀ x ∈ U, ∀ y ∈ U, |f x - f y| ≤ ‖x - y‖ ^ α) :
  ∀ x₀ ∈ U, ∃ r > 0, Metric.ball x₀ r ⊆ U ∧ ∀ y ∈ Metric.ball x₀ r, f y = f x₀ := by
  sorry



theorem theorem_349401_problem (α β : ℂ) (hαβ : α ≠ β) :
  let g : ℂ → ℂ := fun z ↦ (z - α) / (z - β)
  let branch_cut : Set ℂ := {w | w.im = 0 ∧ w.re ≤ 0}
  let segment : Set ℂ := {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = β + (t : ℂ) * (α - β)}
  let domain : Set ℂ := {z | z ≠ β ∧ g z ∉ branch_cut}
  domain = segmentᶜ := by
  sorry



theorem theorem_349543_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (T G : Module.End K V)
  (h_comm : G * T = T * G)
  (h_cyclic : ∃ v : V, ⊤ = Submodule.span K (Set.range (fun n : ℕ => (T ^ n) v))) :
  ∃ p : Polynomial K, G = Polynomial.aeval T p := by
  sorry





theorem theorem_350027_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (F : E → (E →L[ℝ] ℝ))
  (K : Set E) (hK : IsCompact K)
  (x : E)
  (ε : ℝ) (hε : 0 < ε)
  (V : Set E) (hV : V = Metric.ball x ε)
  (hVK : V ⊆ K)
  (h1 : ∀ y ∈ V, F x (y - x) ≥ 0)
  (h2 : ∀ y ∈ V, F x (x - y) ≥ 0) :
  F x = 0 := by
  sorry

theorem theorem_349819_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (f : Module.End F V) (n : ℕ) (lam μ : F) (v : V)
  (h_nilpotent : (f - lam • (1 : Module.End F V)) ^ n = 0)
  (h_v_ne_zero : v ≠ 0)
  (h_eigen : f v = μ • v) :
  μ = lam := by
  sorry





theorem theorem_349928_problem
  {E : Type*} [AddCommGroup E] [Module ℝ E]
  (S : Set E)
  (g : E → ℝ)
  (A B C : E)
  (t : ℝ)
  (hA : A ∈ S)
  (hB : B ∈ S)
  (hC : C ∈ S)
  (ht : 0 ≤ t ∧ t ≤ 1)
  (h_def : C = t • A + (1 - t) • B)
  (h_ineq : g C > t * g A + (1 - t) * g B) :
  ¬ ConvexOn ℝ S g := by
  sorry











theorem theorem_350006_problem (K c x y z : ℝ)
  (h1 : K > 2)
  (h2 : c > 0)
  (h3 : K = c^2 + 1 / c^2) :
  (c * x + (1 / c) * y)^2 + (c * y + (1 / c) * z)^2 + (c * z + (1 / c) * x)^2 =
  K * x^2 + K * y^2 + K * z^2 + 2 * x * y + 2 * y * z + 2 * x * z := by
  sorry





theorem theorem_350770_problem (n k : ℕ)
  (x_u : Matrix (Fin k) (Fin 1) ℝ)
  (Y : Matrix (Fin n) (Fin k) ℝ)
  (y : Fin n → Matrix (Fin k) (Fin 1) ℝ)
  (h : ∀ (i : Fin n) (j : Fin k), Y i j = y i j 0) :
  ∀ (i : Fin n), (x_u.transpose * Y.transpose) 0 i = (x_u.transpose * y i) 0 0 := by
  sorry

theorem theorem_350694_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (v₁ v₂ v₃ v₄ : V) :
  let w := fun (u v : V) => (inner u v : ℝ)
  Matrix.det ![![w v₁ v₃, w v₁ v₄], ![w v₂ v₃, w v₂ v₄]] +
  Matrix.det ![![w v₁ v₄, w v₁ v₂], ![w v₃ v₄, w v₂ v₃]] +
  Matrix.det ![![w v₁ v₂, w v₁ v₃], ![w v₂ v₄, w v₃ v₄]] = 0 := by
  sorry



theorem theorem_350725_problem
  {X : Type*} [AddCommGroup X] [Module ℝ X]
  (n₁ n₂ : X → ℝ)
  -- Axioms for norm n₁
  (h₁_nonneg : ∀ x, 0 ≤ n₁ x)
  (h₁_zero : ∀ x, n₁ x = 0 ↔ x = 0)
  (h₁_add : ∀ x y, n₁ (x + y) ≤ n₁ x + n₁ y)
  (h₁_smul : ∀ (c : ℝ) x, n₁ (c • x) = |c| * n₁ x)
  -- Axioms for norm n₂
  (h₂_nonneg : ∀ x, 0 ≤ n₂ x)
  (h₂_zero : ∀ x, n₂ x = 0 ↔ x = 0)
  (h₂_add : ∀ x y, n₂ (x + y) ≤ n₂ x + n₂ y)
  (h₂_smul : ∀ (c : ℝ) x, n₂ (c • x) = |c| * n₂ x)
  -- Equivalence condition: Identity map is continuous both ways (homeomorphism)
  -- Formalized as continuity at 0 for linear maps
  (h_equiv₁ : ∀ ε > 0, ∃ δ > 0, ∀ x, n₁ x < δ → n₂ x < ε)
  (h_equiv₂ : ∀ ε > 0, ∃ δ > 0, ∀ x, n₂ x < δ → n₁ x < ε) :
  ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧ ∀ x, C₁ * n₁ x ≤ n₂ x ∧ n₂ x ≤ C₂ * n₁ x := by
  sorry

