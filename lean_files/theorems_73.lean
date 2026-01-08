import Mathlib
import Mathlib.Tactic











theorem theorem_395296_problem
  {K : Type*} [Field K]
  (b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ : K)
  (M : Matrix (Fin 4) (Fin 4) K)
  (hM : M = !![b₁, b₂, b₃, b₄;
               c₁, c₂, c₃, c₄;
               b₃, b₄, b₁ + b₂, b₂ + b₃;
               c₃, c₄, c₁ + c₂, c₂ + c₃]) :
  M.rank = 4 ↔ M.det ≠ 0 := by
  sorry









theorem theorem_394239_problem
  {K V : Type*} [NormedField K] [AddCommGroup V] [Module K V]
  (p : V → ℝ)
  (h : ∀ (v : V) (r : K), p (r • v) ≤ ‖r‖ * p v) :
  ∀ (v : V) (r : K), p (r • v) = ‖r‖ * p v := by
  sorry



theorem theorem_396071_problem
  (X1 X2 : Type*)
  [NormedAddCommGroup X1] [NormedSpace ℝ X1]
  [NormedAddCommGroup X2] [NormedSpace ℝ X2]
  (e : X1 ≃ₗ[ℝ] X2)
  (h_dual : ∀ (f : X1 →ₗ[ℝ] ℝ), Continuous f ↔ Continuous (f ∘ e.symm))
  (x : ℕ → X1)
  (hx : ∀ n, ‖x n‖ = 1) :
  ∃ C > 0, ∀ n, ‖e (x n)‖ ≤ C := by
  sorry

theorem theorem_395988_problem
  {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
  (Integral : (ℝ → Y) → Y)
  (IntegralR : (ℝ → ℝ) → ℝ)
  (h_dual : ∀ (φ : Module.Dual ℝ Y) (g : ℝ → Y), φ (Integral g) = IntegralR (φ ∘ g))
  (L_x L_y : Y →ₗ[ℝ] Y)
  (f : ℝ → Y) :
  Integral (fun y ↦ L_x (L_y (f y))) = L_x (Integral (fun y ↦ L_y (f y))) := by
  sorry



theorem theorem_396883_problem
  (p : ℕ) [Fact p.Prime]
  (V : Type*) [AddCommGroup V] [Module (ZMod p) V]
  [FiniteDimensional (ZMod p) V]
  (k : ℕ) (hdim : FiniteDimensional.finrank (ZMod p) V = k)
  (G : Subgroup (V ≃ₗ[ZMod p] V))
  (hG : IsPGroup p G) :
  ∃ b : Basis (Fin k) (ZMod p) V,
    ∀ g : G,
      let M := LinearMap.toMatrix b b (g : V →ₗ[ZMod p] V)
      (∀ i j : Fin k, i > j → M i j = 0) ∧
      (∀ i : Fin k, M i i = 1) := by
  sorry



theorem theorem_395459_problem (u v w a b : ℝ) (hu : u ≠ 0) :
  let g : Matrix (Fin 2) (Fin 2) ℝ := !![u, 0; v, w]
  let h : Matrix (Fin 2) (Fin 2) ℝ := !![a, 0; b, a^2]
  let x := a
  let z := a^2
  let y := (v * a + w * b - a^2 * v) / u
  let k : Matrix (Fin 2) (Fin 2) ℝ := !![x, 0; y, z]
  g * h = k * g := by
  sorry





theorem theorem_397796_problem
  (X : Type*) [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [TopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  (K : Set (WeakDual ℝ X)) (hK : IsCompact K) :
  TopologicalSpace.MetrizableSpace K := by
  sorry



theorem theorem_399740_problem
  {n m : ℕ}
  {K : Type*} [Field K]
  (W : Matrix (Fin n) (Fin n) K)
  (V : Matrix (Fin m) (Fin n) K)
  (hW : W.rank < n)
  (hV : V.transpose.rank = n) :
  ¬ ∃ C : Matrix (Fin n) (Fin n) K, W.transpose * C * V.transpose = V.transpose := by
  sorry

theorem theorem_398642_problem (m n : ℕ) (hmn : m ≠ n) :
  Function.Bijective (Matrix.transpose : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin n) (Fin m) ℝ) := by
  sorry



theorem theorem_398271_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
  (1 + t • A).det = ((Matrix.charpoly A).roots.map (fun x => 1 + t * x)).prod := by
  sorry

theorem theorem_397296_problem
  {R : Type*} [NormedRing R]
  (A : R)
  (k m n : ℕ)
  (hk_pos : k > 0)
  (h_norm : ‖A ^ k‖ < 1) :
  ‖A ^ (m + n * k)‖ ≤
    ((Finset.range k).image (fun i => ‖A ^ i‖)).max' (by simp [Finset.nonempty_range_iff, Nat.ne_of_gt hk_pos]) * ‖A ^ k‖ ^ n := by
  sorry



theorem theorem_397827_problem (V : Type*) [AddCommGroup V] [Module ℂ V] :
  let ForV := RestrictScalars ℝ ℂ V
  let ForForV := RestrictScalars ℝ ℝ ForV
  let ForForForV := RestrictScalars ℝ ℝ ForForV
  Nonempty (ForForForV ≃ₗ[ℝ] ForV) := by
  sorry

















theorem theorem_398781_problem
  (n k : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (U : Matrix (Fin n) (Fin k) ℝ)
  (C : Matrix (Fin k) (Fin k) ℝ)
  (V : Matrix (Fin k) (Fin n) ℝ)
  (hA : IsUnit A)
  (hC : IsUnit C)
  (h_add : IsUnit (A + U * C * V))
  (h_inner : IsUnit (C⁻¹ + V * A⁻¹ * U)) :
  (A + U * C * V)⁻¹ = A⁻¹ - A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ := by
  sorry



theorem theorem_398432_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
  A.det = ∑ j : Fin n, A i j * (Matrix.updateRow A i (Pi.single j 1)).det := by
  sorry







theorem theorem_399491_problem (φ : ℂ →ₗ[ℝ] ℝ)
  (h_mul : ∀ x y : ℂ, φ (x * y) = φ x * φ y) :
  ∀ z : ℂ, φ z = 0 := by
  sorry



theorem theorem_398361_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (S T : X →L[𝕜] X)
  (hS_inj : Function.Injective S)
  (δ : ℝ)
  (hδ_def : δ = sInf {r | ∃ x : X, ‖x‖ = 1 ∧ r = ‖S x‖})
  (hδ_pos : 0 < δ)
  (hST : ‖S - T‖ < δ) :
  Function.Injective T := by
  sorry







theorem theorem_398761_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (w : E) (hw : w ≠ 0)
  (β : ℝ → E)
  (h_cont : Continuous β)
  (h_par : ∀ t, ∃ c : ℝ, β t = c • w)
  (h_norm : ∀ t, ‖β t‖ = 1) :
  (∀ t, β t = ‖w‖⁻¹ • w) ∨ (∀ t, β t = -(‖w‖⁻¹ • w)) := by
  sorry











theorem theorem_398479_problem
  (n m p : ℕ)
  (f : (Fin n → ℝ) → (Fin m → ℝ))
  (g : (Fin m → ℝ) → (Fin p → ℝ))
  (x h : Fin n → ℝ)
  (hf : Differentiable ℝ f)
  (hg : Differentiable ℝ g) :
  fderiv ℝ (g ∘ f) x h = fderiv ℝ g (f x) (fderiv ℝ f x h) := by
  sorry

























theorem theorem_400522_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (A : Set V) (x : V)
  (hA : A.Finite) (hx : x ∈ A) :
  let K := {v | ∃ (s : Finset V) (c : V → ℝ), ↑s ⊆ A ∧ (∀ i, 0 ≤ c i) ∧ v = ∑ i in s, c i • i}
  let Rx := {v | ∃ (t : ℝ), 0 ≤ t ∧ v = t • x}
  let Lx := {v | ∃ (t : ℝ), v = t • x}
  let P := convexHull ℝ (A \ {x})
  (Rx ⊆ K ∧ ∀ y z, y ∈ K → z ∈ K → y + z ∈ Rx → y ∈ Rx ∧ z ∈ Rx) ↔
  Disjoint Lx P := by
  sorry

theorem theorem_400304_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [Field K]
  (X Y : Matrix n n K)
  (hX : Invertible X)
  (hY : Invertible Y)
  (hXY : Invertible (X + Y)) :
  (X * (X + Y)⁻¹ * Y)⁻¹ = Y⁻¹ + X⁻¹ := by
  sorry





theorem theorem_400743_problem {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (S T : Set V) (h_eq : Submodule.span F S = Submodule.span F T)
  (h_ne_bot : Submodule.span F S ≠ ⊥) :
  ¬ Disjoint (Submodule.span F S) (Submodule.span F T) := by
  sorry







theorem theorem_401097_problem (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
  (inferInstance : TopologicalSpace X) = 
  TopologicalSpace.induced (fun x (f : X →L[ℝ] ℝ) ↦ f x) inferInstance ↔ 
  FiniteDimensional ℝ X := by
  sorry

theorem theorem_400171_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (W V : E)
  (h_indep : LinearIndependent ℝ ![W, V])
  (k : ℝ)
  (hk_pos : 0 < k)
  (hk : 1 / 2 ≤ k)
  (g : ℝ → ℝ)
  (hg : ∀ x, g x = ‖W - x • V‖ ^ 2)
  (f : ℝ → ℝ)
  (hf : ∀ x, f x = (g x) ^ k) :
  ConvexOn ℝ Set.univ f := by
  sorry

theorem theorem_401073_problem
  (K : Type*) [Field K]
  (D : Type*) [DivisionRing D]
  (n : ℕ)
  [Algebra K (Matrix (Fin n) (Fin n) D)]
  [FiniteDimensional K (Matrix (Fin n) (Fin n) D)]
  (r : Matrix (Fin n) (Fin n) D)
  (h_inj : Function.Injective (fun x ↦ r * x)) :
  ∃ s : Matrix (Fin n) (Fin n) D, r * s = 1 := by
  sorry













theorem theorem_399539_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  (h : ∃ v : V, v ≠ 0 ∧
    ∃ u w u' w' : V, u ≠ 0 ∧ w ≠ 0 ∧ u' ≠ 0 ∧ w' ≠ 0 ∧
    v = u + w ∧ v = u' + w' ∧ (u, w) ≠ (u', w')) :
  ∀ x : V, x ≠ 0 →
    ∃ u₁ w₁ u₂ w₂ : V, u₁ ≠ 0 ∧ w₁ ≠ 0 ∧ u₂ ≠ 0 ∧ w₂ ≠ 0 ∧
    x = u₁ + w₁ ∧ x = u₂ + w₂ ∧ (u₁, w₁) ≠ (u₂, w₂) := by
  sorry

theorem theorem_400662_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (F : WeakDual 𝕜 X →L[𝕜] 𝕜) :
  ∃ x : X, ∀ f : WeakDual 𝕜 X, F f = f x := by
  sorry





theorem theorem_400725_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]
  (T : V ≃L[𝕜] W)
  (U : Set V) (hU : IsOpen U)
  (g : V → W) (hg : DifferentiableOn 𝕜 g U)
  (a : V) (ha : a ∈ U) :
  fderiv 𝕜 (T.symm ∘ g) a = (T.symm : W →L[𝕜] V).comp (fderiv 𝕜 g a) := by
  sorry

theorem theorem_400808_problem
  {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (X : Set E) (hX : IsOpen X)
  (f : E → F) (hf : ContDiffOn ℝ 1 f X)
  (x y : E) (hx : x ∈ X) (hy : y ∈ X)
  (hseg : segment ℝ x y ⊆ X) :
  f y - f x = ∫ t in (0 : ℝ)..1, fderiv ℝ f (x + t • (y - x)) (y - x) := by
  sorry

theorem theorem_400675_problem
  {Ω : Type*}
  (X err₁ err₂ : Ω → ℝ)
  (β₀₁ β₁₁ β₀₂ β₁₂ : ℝ)
  (Y₁ Y₂ Y : Ω → ℝ)
  (hY₁ : Y₁ = fun ω => β₀₁ + β₁₁ * X ω + err₁ ω)
  (hY₂ : Y₂ = fun ω => β₀₂ + β₁₂ * X ω + err₂ ω)
  (hY : Y = Y₁ + Y₂)
  -- E represents the Conditional Expectation operator E[·|X]
  (E : (Ω → ℝ) → (Ω → ℝ))
  (h_linear : ∀ f g, E (f + g) = E f + E g)
  (h_affine : ∀ a b, E (fun ω => a + b * X ω) = fun ω => a + b * X ω)
  (h_err₁ : E err₁ = 0)
  (h_err₂ : E err₂ = 0)
  -- The fitted model L for Y
  (β₀ β₁ : ℝ)
  (h_model : E Y = fun ω => β₀ + β₁ * X ω)
  -- Assumption of identifiability (intercept is unique)
  (h_id : ∀ a b, (fun ω => a + b * X ω) = 0 → a = 0) :
  β₀ = β₀₁ + β₀₂ := by
  sorry

theorem theorem_400671_problem
  (N d : ℕ)
  (Θ : Fin N → Type)
  (θ : (i : Fin N) → Θ i)
  (f : (i : Fin N) → (Fin d → ℝ) → Θ i → ℝ)
  (M : Fin N → Fin d → ℝ)
  (p_marginal : (i : Fin N) → (Fin d → ℝ) → ℝ)
  (L : (Fin N → Fin d → ℝ) → ℝ)
  (h_dist : ∀ (i : Fin N) (v : Fin d → ℝ), p_marginal i v = f i v (θ i))
  (h_indep : ∀ (m : Fin N → Fin d → ℝ), L m = ∏ i, p_marginal i (m i)) :
  L M = ∏ i, f i (M i) (θ i) := by
  sorry







theorem theorem_400477_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (H₁ : Submodule ℝ H) [FiniteDimensional ℝ H₁]
  (H₂ : Submodule ℝ H) [FiniteDimensional ℝ H₂]
  (X₁ : H) (hX₁ : X₁ ∉ H₁)
  (Z : H) (hZ : Z = X₁ - (orthogonalProjection H₁ X₁ : H))
  (hH₂ : H₂ = Submodule.span ℝ {Z})
  (X_n_plus_1 : H) :
  (orthogonalProjection H₂ X_n_plus_1 : H) = (inner X_n_plus_1 Z / ‖Z‖^2) • Z := by
  sorry



theorem theorem_400751_problem
  (A₀ A₁ B₀ B₁ : ℝ)
  (T : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) :
  let P := fun (t : ℝ) ↦ ![A₀ + A₁ * t, B₀ + B₁ * t, t]
  let v_const := ![A₀, B₀, 0]
  let v_slope := ![A₁, B₁, 1]
  ∀ t : ℝ, T (P t) = T v_const + t • T v_slope := by
  sorry



