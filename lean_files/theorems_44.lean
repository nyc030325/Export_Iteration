import Mathlib
import Mathlib.Tactic

theorem theorem_235430_problem 
  (a1 a2 a3 b1 b2 b3 c1 c2 c3 d1 d2 d3 : ℝ)
  (k1 k2 k3 : ℝ)
  (hk1 : 0 < k1) (hk2 : 0 < k2) (hk3 : 0 < k3)
  (h_sum : k1 + k2 + k3 = 1)
  (x1 x2 x3 : ℝ)
  (h1 : a1 * x1 + b1 * x2 + c1 * x3 ≥ d1)
  (h2 : a2 * x1 + b2 * x2 + c2 * x3 ≥ d2)
  (h3 : a3 * x1 + b3 * x2 + c3 * x3 ≥ d3)
  (z : ℝ)
  (hz : z = k1 * (a1 * x1 + b1 * x2 + c1 * x3) + k2 * (a2 * x1 + b2 * x2 + c2 * x3) + k3 * (a3 * x1 + b3 * x2 + c3 * x3)) :
  z ≥ (k1 * d1 + k2 * d2 + k3 * d3) / (k1 + k2 + k3) := by
  sorry





theorem theorem_237066_problem
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  -- V is also an R-module, and scalar multiplication is compatible (RestrictScalars)
  [Module ℝ V] [IsScalarTower ℝ ℂ V]
  -- Let conj be a conjugate-linear involution on V (representing the "overline" notation)
  (conj : V ≃ₗ⋆[ℂ] V)
  (h_conj_inv : ∀ v, conj (conj v) = v)
  -- Let γ be a set of k vectors
  {k : ℕ} (γ : Fin k → V)
  -- The vectors are linearly independent over R
  (h_li_real : LinearIndependent ℝ γ) :
  -- Conclusion: The constructed set in V x V is linearly independent over C
  LinearIndependent ℂ (fun i ↦ (γ i, - conj (γ i))) := by
  sorry







theorem theorem_237195_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (f : X → ℝ) (x₀ : X)
  (h_conv : ConvexOn ℝ Set.univ f)
  (h_cont : Continuous f) :
  ∃ x_star : X →L[ℝ] ℝ, ∀ y : X, x_star (y - x₀) ≤ f y - f x₀ := by
  sorry

theorem theorem_237002_problem
  (A : Type*) [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A] :
  ∀ b : TensorProduct ℝ A (RatFunc ℝ), b ≠ 0 → IsUnit b := by
  sorry







theorem theorem_237505_problem
  {K : Type*} [Field K]
  {H : Type*} [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {I : Type*} [Fintype I] [DecidableEq I]
  (B : Basis I K (Module.Dual K H))
  (B' : Basis I K H)
  (h_dual : ∀ i j, B i (B' j) = if i = j then 1 else 0)
  (S : Set I)
  (roots : Set (Module.Dual K H))
  (h_span : roots ⊆ Submodule.span K (B '' S))
  (i : I) (hi : i ∉ S) :
  ∀ β ∈ roots, β (B' i) = 0 := by
  sorry







theorem theorem_237801_problem (X Y Z : ℕ)
  (h1 : X + Y = 2)
  (h2 : X + Z = 3) :
  (X, Y, Z) = (0, 2, 3) ∨ (X, Y, Z) = (1, 1, 2) ∨ (X, Y, Z) = (2, 0, 1) := by
  sorry

theorem theorem_238338_problem
  (n s : ℕ)
  (hsn : s ≤ n)
  (K : ℕ → ℕ → ℝ)
  (q : ℕ → ℝ)
  (hK : ∀ i j, i ≤ n - s → j ≤ n → K i j =
    if i ≤ j ∧ j ≤ i + s then (-1 : ℝ)^(j - i) * (s.choose (j - i)) else 0) :
  ∀ i, i ≤ n - s →
    ∑ j in Finset.range (n + 1), K i j * q j =
    ∑ k in Finset.range (s + 1), (-1 : ℝ)^k * (s.choose k) * q (i + k) := by
  sorry

theorem theorem_237386_problem (A B : ℂ)
  (h1 : (1 / 2 + Complex.I * Real.sqrt 3 / 2) * A + (1 / 2 - Complex.I * Real.sqrt 3 / 2) * B = -3)
  (h2 : A + B = 2) :
  A = 1 + 4 * Complex.I / (Real.sqrt 3 : ℂ) ∧ B = 1 - 4 * Complex.I / (Real.sqrt 3 : ℂ) := by
  sorry



theorem theorem_237728_problem
  {K : Type*} [Field K]
  {n m : ℕ}
  (A : Matrix (Fin n) (Fin n) K)
  (B : Matrix (Fin n) (Fin m) K)
  (C : Matrix (Fin m) (Fin n) K)
  (D : Matrix (Fin m) (Fin m) K)
  (hD : IsUnit D) :
  IsUnit (Matrix.fromBlocks A B C D) ↔ IsUnit (A - B * D⁻¹ * C) := by
  sorry









theorem theorem_237785_problem
  (a1 a2 a3 b1 b2 b3 : ℝ)
  (x1 x2 x3 : ℝ)
  (h_sys1 : a1 * x1 + a2 * x2 + a3 * x3 = 0)
  (h_sys2 : b1 * x1 + b2 * x2 + b3 * x3 = 0)
  (h_det13 : a1 * b3 - a3 * b1 ≠ 0)
  (h_det12 : a1 * b2 - a2 * b1 ≠ 0)
  (h_x3 : x3 ≠ 0) :
  x1 / x3 = (a2 * b3 - a3 * b2) / (a1 * b2 - a2 * b1) := by
  sorry











theorem theorem_238235_problem
  (F : Type*) [Field F]
  (G : Type*) [Group G]
  (V : Type*) [AddCommGroup V] [Module F V]
  (W : Type*) [AddCommGroup W] [Module F W]
  (ρ : G →* (V ≃ₗ[F] V))
  (ν : G →* (W ≃ₗ[F] W)) :
  let Hom_G : Set (V →ₗ[F] W) := {T | ∀ (g : G) (v : V), T (ρ g v) = ν g (T v)}
  ∃ (S : Submodule F (V →ₗ[F] W)), (S : Set (V →ₗ[F] W)) = Hom_G := by
  sorry







theorem theorem_238858_problem (F : Type*) [Field F] [Fintype F] :
  ∃ p d : ℕ, Nat.Prime p ∧ d > 0 ∧ Fintype.card F = p ^ d := by
  sorry



theorem theorem_238383_problem (a b s : ℝ)
  (h1 : s^2 - a^2 ≠ 0)
  (h2 : s - 2 * b ≠ 0)
  (h3 : a + 2 * b ≠ 0)
  (h4 : a - 2 * b ≠ 0)
  (h5 : a^2 - 4 * b^2 ≠ 0) :
  let A := (a + b) / (a + 2 * b)
  let B := (2 * a - 5 * b) / (a - 2 * b)
  let C := (4 * b^2 + 2 * a * b - a^2) / (a^2 - 4 * b^2)
  (2 * s^2 + (a - 6 * b) * s + a^2 - 4 * a * b) / ((s^2 - a^2) * (s - 2 * b)) =
  A / (s + a) + B / (s - a) + C / (s - 2 * b) := by
  sorry



theorem theorem_238880_problem
  (k : Type*) [Field k] [IsAlgClosed k]
  (h_unc : Cardinal.aleph0 < Cardinal.mk k)
  (K : Type*) [Field K] [Algebra k K]
  (h_dim : Module.rank k K ≤ Cardinal.aleph0) :
  Function.Surjective (algebraMap k K) := by
  sorry









theorem theorem_238906_problem
  {K V : Type*}
  [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Invertible (2 : K)]
  (ω : V →ₗ[K] V)
  (hω : ω ^ 2 = LinearMap.id)
  (V₀ V₁ : Submodule K V)
  (hV₀ : V₀ = LinearMap.ker (ω - LinearMap.id))
  (hV₁ : V₁ = LinearMap.ker (ω + LinearMap.id)) :
  IsCompl V₀ V₁ := by
  sorry







theorem theorem_238826_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (h_dim : FiniteDimensional 𝕜 E)
  (x : ℕ → E) (x₀ : E)
  (h_weak : ∀ f : E →L[𝕜] 𝕜, Filter.Tendsto (fun n ↦ f (x n)) Filter.atTop (nhds (f x₀))) :
  Filter.Tendsto x Filter.atTop (nhds x₀) := by
  sorry



theorem theorem_239324_problem
  (a₀ a₁ a₂ a₃ a₄ : ℝ)
  (ha₄ : a₄ ≠ 0)
  (L : (ℝ → ℝ) → (ℝ → ℝ) := fun f x ↦
    a₄ * iteratedDeriv 4 f x +
    a₃ * iteratedDeriv 3 f x +
    a₂ * iteratedDeriv 2 f x +
    a₁ * iteratedDeriv 1 f x +
    a₀ * f x)
  (h₁ : ∀ x, L Real.exp x = 0)
  (h₂ : ∀ x, L (fun x ↦ Real.exp (-x)) x = 0)
  (h₃ : ∀ x, L Real.sin x = 0)
  (h₄ : ∀ x, L Real.cos x = 0) :
  ∀ y : ℝ → ℝ, ContDiff ℝ 4 y →
    ((∀ x, L y x = 0) ↔
      ∃ c₁ c₂ c₃ c₄ : ℝ, ∀ x, y x = c₁ * Real.exp x + c₂ * Real.exp (-x) + c₃ * Real.sin x + c₄ * Real.cos x) := by
  sorry



theorem theorem_239385_problem
  (D : Set ℂ) (hD_open : IsOpen D) (hD_conn : IsConnected D)
  (f g : ℂ → ℂ)
  (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
  (h_nz_f : ∀ z ∈ D, f z ≠ 0)
  (h_nz_g : ∀ z ∈ D, g z ≠ 0)
  (h_eq : ∀ z ∈ D, deriv f z / f z = deriv g z / g z) :
  ∃ c : ℂ, ∀ z ∈ D, f z = c * g z := by
  sorry











theorem theorem_239315_problem
  (U : Set ℂ)
  (hU : U = {z : ℂ | 0 < z.re})
  (f : U → ℂ)
  (hf : ∀ z, f z = Complex.exp z) :
  ¬ Function.Injective f := by
  sorry

theorem theorem_239484_problem
  {X : Type*} [MetricSpace X] (x z : X) :
  sSup (Set.range (fun t ↦ |dist x t - dist z t|)) = dist x z := by
  sorry



theorem theorem_239295_problem
  (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  (V : Type*) [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
  CompleteSpace (NormedSpace.Dual 𝕜 V) := by
  sorry

theorem theorem_238717_problem
  (F : Type*) [Field F] [CharZero F]
  (U : Submodule F (Polynomial F))
  (h_inv_D : ∀ p ∈ U, Polynomial.derivative p ∈ U)
  (h_inv_S : ∀ p ∈ U, Polynomial.X * p ∈ U) :
  U = ⊥ ∨ U = ⊤ := by
  sorry



theorem theorem_239458_problem
  (n : ℕ)
  (A B C : Matrix (Fin n) (Fin n) ℝ)
  (hA : A.PosDef)
  (hB : B.PosDef)
  (hC : C.PosDef)
  (hBC : (B - C).PosSemidef) :
  Matrix.trace (A * (A + B⁻¹)⁻¹ * A) ≥ Matrix.trace (A * (A + C⁻¹)⁻¹ * A) := by
  sorry

theorem theorem_239143_problem (c₁ c₂ c₃ : ℝ)
  (h : ∀ t : ℝ, c₁ * Real.exp (-t) + c₂ * Real.exp t + c₃ = 0) :
  c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  sorry

theorem theorem_240084_problem :
  ∃ (X : Type) (_ : NormedAddCommGroup X) (_ : NormedSpace ℝ X),
    ¬ FiniteDimensional ℝ X ∧
    ∃ T : X →ₗ[ℝ] X, LinearMap.ker T = ⊥ ∧ ¬ Continuous T := by
  sorry



theorem theorem_240118_problem (R : Type*) [CommRing R] (w : R) :
  let f : R →ₗ[R] R × R := LinearMap.prod LinearMap.id 0
  let g : R × R →ₗ[R] R := LinearMap.coprod (LinearMap.lsmul R R w) LinearMap.id
  LinearMap.det (g.comp f) = w := by
  sorry



theorem theorem_240288_problem
  (n : ℕ)
  (x z : Fin n → ℝ)
  (nrm : (Fin n → ℝ) → ℝ)
  (dual_nrm : (Fin n → ℝ) → ℝ)
  (h_nrm_nonneg : ∀ v, 0 ≤ nrm v)
  (h_nrm_eq_zero : ∀ v, nrm v = 0 ↔ v = 0)
  (h_nrm_smul : ∀ (c : ℝ) v, nrm (c • v) = |c| * nrm v)
  (h_nrm_triangle : ∀ u v, nrm (u + v) ≤ nrm u + nrm v)
  (h_dual_nrm : ∀ u, dual_nrm u = sSup {r | ∃ v, nrm v ≤ 1 ∧ r = Matrix.dotProduct u v}) :
  |Matrix.dotProduct z x| ≤ nrm x * dual_nrm z := by
  sorry

theorem theorem_240062_problem (R A : Type*)
  [CommRing R] [Ring A] [Algebra R A]
  [Module.Finite R A] [IsNoetherianRing R] :
  IsNoetherianRing A := by
  sorry

theorem theorem_240544_problem
  {F : Type*} [Field F]
  {V W : Type*}
  [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
  {n m : ℕ}
  (B : Basis (Fin n) F V)
  (C : Basis (Fin m) F W)
  (T : V →ₗ[F] W) :
  ∃! M : Matrix (Fin m) (Fin n) F, ∀ v : V, Matrix.mulVec M (B.equivFun v) = C.equivFun (T v) := by
  sorry









theorem theorem_240857_problem
  (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (a u : EuclideanSpace ℝ (Fin n))
  (hf : ContDiff ℝ 2 f)
  (hu : ‖u‖ = 1)
  (g : ℝ → ℝ)
  (hg : ∀ t, g t = f (a + t • u)) :
  ∀ t, deriv (deriv g) t = iteratedFDeriv ℝ 2 f (a + t • u) ![u, u] := by
  sorry

theorem theorem_241047_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
  (h : Matrix.rank (A * A.transpose) < m) :
  Matrix.rank A < m := by
  sorry





theorem theorem_241007_problem
  (f : ℝ → ℝ × ℝ)
  (norm_infty : ℝ × ℝ → ℝ)
  (h_f : ∀ x : ℝ, f x = (x, |x|))
  (h_norm : ∀ p : ℝ × ℝ, norm_infty p = max (|p.1|) (|p.2|)) :
  ∀ x₁ x₂ : ℝ, norm_infty (f x₁ - f x₂) = |x₁ - x₂| := by
  sorry







theorem theorem_240919_problem
  {X W : Type*} [TopologicalSpace X] [TopologicalSpace W]
  (f : X × W → ℝ) (g : X → ℝ)
  (hf : Continuous f)
  (h_compact : ∀ (x : X) (c : ℝ), IsCompact {w : W | f (x, w) ≥ c})
  (hg : ∀ x, g x = sSup (Set.range (fun w ↦ f (x, w)))) :
  UpperSemicontinuous g := by
  sorry











theorem theorem_241443_problem
  {n m : ℕ}
  (F : (Fin n → ℝ) → (Fin m → ℝ))
  (p : Fin n → ℝ)
  (h_smooth : ContDiff ℝ ⊤ F)
  (h_M : F p = 0)
  (h_reg : ∀ x, F x = 0 → LinearMap.range (fderiv ℝ F x) = ⊤) :
  tangentConeAt ℝ {x | F x = 0} p = LinearMap.ker (fderiv ℝ F p) := by
  sorry



theorem theorem_241391_problem
  (n d : ℕ)
  (M : ℕ)
  (hM : M = n + 1)
  (T : Fin (n + d + 2) → ℝ)
  (hT : Monotone T)
  (b : Fin M → ℝ → ℝ)
  -- The problem states b are "B-spline basis functions", which implies linear independence.
  (h_indep : LinearIndependent ℝ b)
  (S : Set (ℝ → (Fin d → ℝ)))
  -- The problem states S is the "spline space" generated by b.
  -- We define S as the set of functions formed by linear combinations of b with vector coefficients.
  (hS : S = {x | ∃ c : Fin M → (Fin d → ℝ), x = fun t ↦ ∑ i, (b i t) • (c i)}) :
  -- The conclusion is the existence and uniqueness of the coefficients.
  ∀ x ∈ S, ∃! c : Fin M → (Fin d → ℝ), x = fun t ↦ ∑ i, (b i t) • (c i) := by
  sorry





theorem theorem_241404_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (x h : Fin n → ℝ) :
  let φ : (Fin n → ℝ) → ℝ := fun v ↦ Matrix.dotProduct (A.mulVec v) v
  fderiv ℝ φ x h = Matrix.dotProduct x ((A + A.transpose).mulVec h) := by
  sorry







