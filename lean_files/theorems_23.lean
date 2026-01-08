import Mathlib
import Mathlib.Tactic

theorem theorem_118903_problem :
  ¬ ∃ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) ∧
    ∀ x ∈ Set.Ioo 0 1, f x = Real.sin (1 / x) := by
  sorry





theorem theorem_119020_problem (n : ℕ) (x a_m : Fin n → ℝ) (z y_m : ℝ) :
  y_m ≥ max (Matrix.dotProduct a_m x) z ↔ y_m ≥ Matrix.dotProduct a_m x ∧ y_m ≥ z := by
  sorry



theorem theorem_119278_problem
  {X K : Type*} [RCLike K]
  (g : ℕ → X → K)
  (M : ℕ → ℝ)
  (h_nonneg : ∀ i, 0 ≤ M i)
  (h_bound : ∀ x i, ‖g i x‖ ≤ M i)
  (h_summable : Summable M) :
  ∃ f : X → K, TendstoUniformly (fun n x ↦ ∑ i in Finset.range n, g i x) f atTop := by
  sorry



theorem theorem_119022_problem (a : ℂ) :
  (∃ α β : ℂ, !![α, β; -star β, star α] = Matrix.diagonal (fun _ ↦ a)) ↔ a.im = 0 := by
  sorry















theorem theorem_119154_problem 
  (d C N : ℕ) 
  (hN : (N : ℝ) ≠ 0) 
  (hC : (C : ℝ) ≠ 0)
  (x : Fin C → Fin N → Fin d → ℝ) 
  (μ_i : Fin C → Fin d → ℝ) 
  (μ : Fin d → ℝ)
  (h_μ_i : ∀ i, μ_i i = (N : ℝ)⁻¹ • ∑ t : Fin N, x i t)
  (h_μ : μ = (C : ℝ)⁻¹ • ∑ i : Fin C, μ_i i) :
  ∑ i : Fin C, ∑ t : Fin N, Matrix.vecMulVec (x i t - μ_i i) (μ_i i - μ) = 0 := by
  sorry

theorem theorem_119974_problem (K : Set ℂ) (hK_ne : K.Nonempty) (hK_compact : IsCompact K) :
  ∃ T : lp (fun (_ : ℕ) => ℂ) 2 →L[ℂ] lp (fun (_ : ℕ) => ℂ) 2, spectrum ℂ T = K := by
  sorry





theorem theorem_119849_problem
  (n : ℕ)
  (A Q : Matrix (Fin n) (Fin n) ℝ)
  (hA : ∀ z ∈ spectrum ℂ (Matrix.toLin' (Matrix.map A (Complex.ofReal))), z.re < 0)
  (hQ : Q.PosDef) :
  ∃! P : Matrix (Fin n) (Fin n) ℝ, P.PosDef ∧ A.transpose * P + P * A = -Q := by
  sorry

theorem theorem_119859_problem
  {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]
  (L : V →ₗ[F] W)
  (h_dim : FiniteDimensional.finrank F V = FiniteDimensional.finrank F W)
  (h_ker : LinearMap.ker L = ⊥) :
  Function.Bijective L := by
  sorry





theorem theorem_119925_problem
  (n : ℕ)
  (R U T : Matrix (Fin n) (Fin n) ℝ)
  (hU : U * U.transpose = 1)
  (hT : ∀ i j, i > j → T i j = 0)
  (h_qr : R.transpose = U.transpose * T.transpose) :
  R * R.transpose = T * T.transpose := by
  sorry

theorem theorem_120116_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [Field K]
  (C : Matrix n n K)
  (h : Matrix.det (1 - C) = 0) :
  Module.End.HasEigenvalue (Matrix.toLin' C) 1 := by
  sorry











theorem theorem_120596_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  (v₁ v₂ : V)
  (h : LinearIndependent F ![v₁, v₂]) :
  TensorAlgebra.ι F v₁ * TensorAlgebra.ι F v₂ ≠ TensorAlgebra.ι F v₂ * TensorAlgebra.ι F v₁ := by
  sorry

theorem theorem_120339_problem (n : ℕ) (a : Fin n → ℝ) (b c : ℝ)
  (ha : a ≠ 0) (hbc : b < c) :
  interior {x : Fin n → ℝ | b ≤ Matrix.dotProduct a x ∧ Matrix.dotProduct a x ≤ c} =
  {x : Fin n → ℝ | b < Matrix.dotProduct a x ∧ Matrix.dotProduct a x < c} := by
  sorry







theorem theorem_120577_problem
  {n : ℕ}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (e : Basis (Fin n) ℝ E)
  (e_dual : Fin n → E)
  (h_dual : ∀ i j, ⟪e_dual i, e j⟫_ℝ = if i = j then 1 else 0)
  (f : E → ℝ)
  (hf : Differentiable ℝ f)
  (x : E) :
  gradient f x = ∑ i, (fderiv ℝ f x (e i)) • (e_dual i) := by
  sorry













theorem theorem_120833_problem (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ)
  (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
  Matrix.trace (A⁻¹ * M * A) = Matrix.trace M := by
  sorry

theorem theorem_121589_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [FiniteDimensional 𝕜 Y]
  (K : X →L[𝕜] Y) :
  IsCompactOperator K := by
  sorry

theorem theorem_120234_problem (A : Matrix (Fin 2) (Fin 2) ℤ)
  (h_uni : A.det = 1 ∨ A.det = -1) :
  ¬ (A ^ 8 = 1 ∧ ∀ k : ℕ, 1 ≤ k → k < 8 → A ^ k ≠ 1) := by
  sorry



theorem theorem_121234_problem
  {F S : Type*} [Field F] [AddCommGroup S] [Module F S]
  (A : Set S) (x : S)
  (hA_indep : AffineIndependent F (fun (a : A) => (a : S)))
  (hA_max : ∀ (B : Set S), A ⊆ B → AffineIndependent F (fun (b : B) => (b : S)) → A = B) :
  let xA := (fun a => a + x) '' A
  AffineIndependent F (fun (y : xA) => (y : S)) ∧
  ∀ (B : Set S), xA ⊆ B → AffineIndependent F (fun (b : B) => (b : S)) → xA = B := by
  sorry

theorem theorem_121432_problem
  {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  (φ : Representation K G V)
  (ψ : Representation K G W)
  (U : V →ₗ[K] W)
  (S : Set G)
  (hS : Subgroup.closure S = ⊤)
  (h_gen : ∀ s ∈ S, U.comp (φ s) = (ψ s).comp U) :
  ∀ g : G, U.comp (φ g) = (ψ g).comp U := by
  sorry

theorem theorem_121488_problem (t : ℝ) (Ω : Type*)
  (X : ℕ → ℝ → Ω → ℝ) (X_lim : ℝ → Ω → ℝ)
  (h_conv : ∀ ω, ∀ s ∈ Set.Icc 0 t, Filter.Tendsto (fun k => X k s ω) Filter.atTop (nhds (X_lim s ω))) :
  ∀ ω, Filter.liminf (fun k => ⨆ s ∈ Set.Icc 0 t, X k s ω) Filter.atTop ≥ ⨆ s ∈ Set.Icc 0 t, X_lim s ω := by
  sorry

theorem theorem_121838_problem
  (n : ℕ) (hn : 0 < n)
  (K : Type*) [Field K] [Algebra ℝ K]
  (h_scalar_mult_closed : ∀ (a : K) (v : Fin n → ℝ),
    ∃ (u : Fin n → ℝ), ∀ i, algebraMap ℝ K (u i) = a * algebraMap ℝ K (v i)) :
  Function.Surjective (algebraMap ℝ K) := by
  sorry

theorem theorem_121855_problem
  (n : ℕ)
  (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
  (h_unitary : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
    U ∈ Matrix.unitaryGroup (Fin n) ℂ → L (U * A * star U) = U * L A * star U)
  (h_adjoint : ∀ A : Matrix (Fin n) (Fin n) ℂ, L (star A) = star (L A)) :
  ∃ α : ℝ, ∀ A : Matrix (Fin n) (Fin n) ℂ, L A = (α : ℂ) • A := by
  sorry









theorem theorem_122033_problem
  (N d : ℕ)
  (x : Fin N → Fin d → ℝ)
  (t : Fin N → ℝ)
  (w : Fin d → ℝ)
  (b : ℝ)
  (C : ℝ)
  (ht : ∀ i, t i = 1 ∨ t i = -1)
  (hC : 0 < C) :
  IsLeast {val | ∃ ξ : Fin N → ℝ,
    (∀ i, t i * ((∑ j, w j * x i j) + b) ≥ 1 - ξ i ∧ ξ i ≥ 0) ∧
    val = (1 / 2 : ℝ) * (∑ j, w j ^ 2) + C * ∑ i, ξ i}
  ((1 / 2 : ℝ) * (∑ j, w j ^ 2) + C * ∑ i, max 0 (1 - t i * ((∑ j, w j * x i j) + b))) := by
  sorry





theorem theorem_121896_problem
  (X_1 X_2 X_3 e : ℝ)
  (b_0 b_1 b_2 b_3 b_4 : ℝ)
  (a : ℝ)
  (gamma_1 gamma_2 gamma_3 : ℝ)
  (h_X3 : X_3 = X_1 - X_2)
  (h_gamma1 : gamma_1 = b_1 - a)
  (h_gamma2 : gamma_2 = b_2 + a)
  (h_gamma3 : gamma_3 = b_3 + a) :
  b_0 + b_1 * X_1 + b_2 * X_2 + b_3 * X_3 + b_4 * X_1 * X_2 + e =
  b_0 + gamma_1 * X_1 + gamma_2 * X_2 + gamma_3 * X_3 + b_4 * X_1 * X_2 + e := by
  sorry











theorem theorem_122626_problem {V : Type*} [AddCommGroup V] [Module ℚ V] 
  (v : V) (h : v ≠ 0) : 
  ¬ IsOfFinAddOrder v := by
  sorry













theorem theorem_123236_problem
  (x : ℕ → ℝ)
  (a : ℕ → ℕ → ℝ)
  (hx : Summable (fun j ↦ |x j|))
  (ha : ∀ i, Summable (fun j ↦ |a i j|))
  (i : ℕ) :
  (∑' j, a i j * x j)^2 ≤ (∑' j, |a i j|)^2 * (∑' j, |x j|)^2 := by
  sorry



theorem theorem_124001_problem {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA : A.PosSemidef) (hB : B.IsSymm) :
  B = hA.sqrt ↔ B ^ 2 = A := by
  sorry







theorem theorem_123706_problem 
  (m n k : ℕ)
  (X : Matrix (Fin m) (Fin n) ℝ)
  (A : Matrix (Fin n) (Fin k) ℝ)
  (hA_bin : ∀ i j, A i j = 0 ∨ A i j = 1)
  (hA_row_sum : ∀ i, ∑ j, A i j = 1)
  (one_n : Matrix (Fin n) (Fin 1) ℝ)
  (h_one_n : one_n = fun _ _ => 1)
  (W : Matrix (Fin k) (Fin k) ℝ)
  (hW : W = Matrix.diagonal (fun j => (A.transpose * one_n) j 0))
  (hW_inv : Invertible W)
  (C : Matrix (Fin m) (Fin k) ℝ)
  (hC : C = X * A * W⁻¹)
  (D : Matrix (Fin m) (Fin n) ℝ)
  (hD : D = X - C * A.transpose) :
  (D.transpose * D).trace = ∑ j : Fin k, ∑ i : Fin n, A i j * (∑ r : Fin m, (X r i - C r j)^2) := by
  sorry

theorem theorem_124487_problem {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  (A : Matrix n n ℝ) (B : Matrix n m ℝ) (S : Matrix m m ℝ)
  (hA : A.PosDef) (hS : S.IsSymm) :
  (Matrix.fromBlocks A B B.transpose S).PosSemidef ↔
  (S - B.transpose * A⁻¹ * B).PosSemidef := by
  sorry









theorem theorem_125013_problem
  {F : Type*} [Field F]
  {n : ℕ}
  (A B : Matrix (Fin n) (Fin n) F)
  (h : FiniteDimensional.finrank F (LinearMap.ker (Matrix.toLin' B)) = A.rank) :
  A.rank + B.rank = n := by
  sorry











theorem theorem_125403_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (f g : V →ₗ[K] V)
  (h : ∀ v ∈ LinearMap.range f, f (g v) = v) :
  LinearMap.range (LinearMap.id - g.comp f) = LinearMap.ker f := by
  sorry

theorem theorem_125460_problem :
  let f : ℝ → ℝ := Real.exp
  let L : (ℝ → ℝ) → (ℝ → ℝ) := deriv
  let L_star : (ℝ → ℝ) → (ℝ → ℝ) := fun g x ↦ - (deriv g x)
  ∀ t, L_star (L f) t = - f t := by
  sorry





theorem theorem_125342_problem (f : ℂ → ℂ) (A : Set ℂ)
  (h_mobius : ∃ a b c d : ℂ, (a * d - b * c ≠ 0) ∧ (∀ z, c * z + d ≠ 0) ∧ (∀ z, f z = (a * z + b) / (c * z + d))) :
  f '' (frontier A) = frontier (f '' A) := by
  sorry



theorem theorem_125334_problem (ρ : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] ℂ) : False := by
  sorry

theorem theorem_125465_problem (x y : ℝ)
  (h1 : x + Real.sqrt 2 * y ≠ 0)
  (h2 : x - Real.sqrt 2 * y ≠ 0) :
  (x - y) / (x^2 - 2 * y^2) =
  1 / (x + Real.sqrt 2 * y) +
  (Real.sqrt 2 - 1) / (2 * Real.sqrt 2) *
  (1 / (x - Real.sqrt 2 * y) - 1 / (x + Real.sqrt 2 * y)) := by
  sorry





theorem theorem_125275_problem
  (X : Type*) [MetricSpace X] [CompactSpace X]
  (F : Set C(X, ℝ))
  (h_nonempty : F.Nonempty)
  (h_bounded : ∃ M > 0, ∀ f ∈ F, ∀ x : X, |f x| ≤ M)
  (h_equicontinuous : ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → ∀ f ∈ F, dist (f x) (f y) < ε) :
  TotallyBounded F := by
  sorry

