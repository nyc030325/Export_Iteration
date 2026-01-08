import Mathlib
import Mathlib.Tactic

theorem theorem_112947_problem (φ : ℝ → ℝ) (A B y : ℝ)
  (hA : Filter.Tendsto φ Filter.atTop (nhds A))
  (hB : Filter.Tendsto φ Filter.atBot (nhds B))
  (h_meas : Measurable φ)
  (h_int : ∀ t > 0, MeasureTheory.Integrable (fun x ↦ (1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (- (|x - y| ^ 2) / (4 * t)) * φ x)) :
  Filter.Tendsto (fun t ↦ ∫ x, (1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (- (|x - y| ^ 2) / (4 * t)) * φ x)
    Filter.atTop (nhds ((A + B) / 2)) := by
  sorry



theorem theorem_114146_problem
  (F : ℕ → ℝ → ℝ)
  (h_bound : ∃ M > 0, ∀ n x, x ∈ Set.Icc 0 1 → |F n x| ≤ M)
  (h_equi : ∀ ε > 0, ∃ δ > 0, ∀ n x y, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 → |x - y| < δ → |F n x - F n y| < ε) :
  ∃ (φ : ℕ → ℕ) (f : ℝ → ℝ), StrictMono φ ∧ TendstoUniformlyOn (fun n => F (φ n)) f Filter.atTop (Set.Icc 0 1) := by
  sorry









theorem theorem_114297_problem
  {F V W : Type*}
  [Field F]
  [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
  (T : V →ₗ[F] W) :
  Function.Injective T ↔ LinearMap.ker T = ⊥ := by
  sorry

theorem theorem_113595_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (x : ℕ → E)
  (h_cauchy : CauchySeq x)
  (A : E)
  (φ : ℕ → ℕ) (h_φ_mono : StrictMono φ)
  (h_subseq_to_A : Filter.Tendsto (x ∘ φ) Filter.atTop (nhds A)) :
  Filter.Tendsto x Filter.atTop (nhds A) := by
  sorry





















theorem theorem_114767_problem
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (c : Fin n → ℝ)
  (y : Fin m → ℝ)
  (x : Fin n → ℝ)
  (h_y : Matrix.vecMul y A = c)
  (h_x : Matrix.mulVec A x = b) :
  Matrix.dotProduct c x = Matrix.dotProduct y b := by
  sorry





theorem theorem_115050_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  {W : Type*} [AddCommGroup W] [Module K W]
  (T : V →ₗ[K] W)
  (W₁ W₂ : Submodule K W) :
  Submodule.comap T (W₁ ⊓ W₂) = Submodule.comap T W₁ ⊓ Submodule.comap T W₂ := by
  sorry



theorem theorem_115536_problem
  (f : ℂ → ℂ)
  (h_entire : Differentiable ℂ f)
  (a b : ℝ)
  (S : Set ℂ)
  (h_S : S = {z : ℂ | a ≤ z.re ∧ z.re ≤ b})
  (h_bounded : ∃ M : ℝ, ∀ z ∈ S, ‖f z‖ ≤ M)
  (T : ℝ)
  (h_T_pos : T > 0)
  (h_periodic : ∀ z : ℂ, f (z + ↑T) = f z) :
  ∃ c : ℂ, f = Function.const ℂ c := by
  sorry

theorem theorem_115677_problem
  (n m : ℕ)
  (A : Fin n → Matrix (Fin m) (Fin m) ℝ)
  (b : Fin m → ℝ)
  (c y : Fin n → ℝ)
  (hA : ∀ i, (A i).IsSymm)
  (hc : ∃ i, c i ≠ 0)
  (h_psd : (∑ i, c i • A i).PosSemidef)
  (h_ineq : 4 * (∑ i, c i * y i) < - ∑ i, c i * (Matrix.dotProduct b (Matrix.mulVec (A i) b))) :
  ¬ ∃ x : Fin m → ℝ, (∑ i, c i * (Matrix.dotProduct x (Matrix.mulVec (A i) (x + b)))) = ∑ i, c i * y i := by
  sorry









theorem theorem_115614_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (x₀ : V) (r : ℝ) (hr : 0 < r) :
  Metric.ball x₀ r = {x | ∃ z ∈ Metric.ball (0 : V) 1, x = x₀ + r • z} := by
  sorry

theorem theorem_115743_problem
  (n : ℕ) (hn : n > 0)
  (B C : Matrix (Fin 3) (Fin 3) ℝ)
  (hB : B = !![0, 1, 0; 0, 1/2, 1/2; 0, 1/2, 1/2])
  (hC : C = !![0, 1/2, 1/2; 0, 1/2, 1/2; 0, 1/2, 1/2])
  (A : Matrix (Fin 3) (Fin 3) ℝ)
  (hA : A = (1 / 2 : ℝ) • (1 + B)) :
  A ^ n = (1 / (2 : ℝ) ^ n) • (1 + (n : ℝ) • B + ((2 : ℝ) ^ n - n - 1) • C) := by
  sorry













theorem theorem_116101_problem
  (n p m : ℕ)
  (hn : n > 0) (hm : m > 0) (hp : p > 0)
  (C : Matrix (Fin n) (Fin p) ℝ)
  (h_consistent : ∃ (X : Matrix (Fin n) (Fin m) ℝ) (F : Matrix (Fin m) (Fin p) ℝ), X * F = C) :
  Set.Infinite {sol : Matrix (Fin n) (Fin m) ℝ × Matrix (Fin m) (Fin p) ℝ | sol.1 * sol.2 = C} := by
  sorry

theorem theorem_116121_problem :
  ∃ F : ℝ →ₗ[ℚ] ℝ, ∀ (a b : ℚ), F (a + (b : ℝ) * Real.sqrt 2) = 42 * (a : ℝ) + 666 * (b : ℝ) := by
  sorry

theorem theorem_116198_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : ∀ i j, 0 ≤ A i j) (m : ℕ) (hm : m > 0) :
  ∀ i j, 0 ≤ (A ^ m) i j := by
  sorry





theorem theorem_116631_problem
  (n : ℕ)
  (K : Set (Fin n → ℝ))
  (hK : IsCompact K)
  (f_seq : ℕ → (Fin n → ℝ) → ℂ)
  (f : (Fin n → ℝ) → ℂ)
  (hf_cont : ∀ k, ContinuousOn (f_seq k) K)
  (h_unif : TendstoUniformlyOn f_seq f atTop K)
  (g : ℂ → ℂ)
  (hg : Continuous g) :
  TendstoUniformlyOn (fun k ↦ g ∘ (f_seq k)) (g ∘ f) atTop K := by
  sorry

theorem theorem_116474_problem (n : ℕ) (hn : n ≠ 2)
  (e : Fin n → ℝ) (he : e = fun _ ↦ 1)
  (b : Fin n → ℝ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : A = Matrix.vecMulVec e e - 2 • (1 : Matrix (Fin n) (Fin n) ℝ))
  (x : Fin n → ℝ) (hx : Matrix.mulVec A x = b) :
  x = ((Matrix.dotProduct b e) / (2 * ((n : ℝ) - 2))) • e - (1 / 2 : ℝ) • b := by
  sorry

theorem theorem_116940_problem (A : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) :
  Matrix.dotProduct (Matrix.mulVec A u) v = Matrix.dotProduct u (Matrix.mulVec (Matrix.conjTranspose A) v) := by
  sorry

theorem theorem_116727_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  (β : V →ₗ[K] W →ₗ[K] K)
  (x z : V) (y w : W) :
  β (x + z) (y + w) = β x y + β x w + β z y + β z w := by
  sorry

theorem theorem_116461_problem {E : Type*} [NormedAddCommGroup E] :
  sInf (Set.range (fun (x : E × E) ↦ ‖x.1‖ + ‖x.2‖)) =
  sInf {val | ∃ (q p : E) (s t : ℝ), ‖q‖ ≤ t ∧ ‖p‖ ≤ s ∧ 0 ≤ s ∧ 0 ≤ t ∧ val = s + t} := by
  sorry



theorem theorem_117026_problem
  (k V W : Type*)
  [Field k]
  [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
  [Module.Finite k V] [Module.Finite k W] :
  Nonempty (TensorProduct k V W ≃ₗ[k] Module.Dual k (V →ₗ[k] W →ₗ[k] k)) := by
  sorry





theorem theorem_117005_problem
  {G V : Type*}
  [Group G]
  [AddCommGroup V]
  [Module ℂ V]
  [MulAction G V]
  [SMulCommClass G ℂ V]
  [DistribMulAction G V]
  (dual_action : G → (V →ₗ[ℂ] ℂ) → (V →ₗ[ℂ] ℂ))
  (h_def : ∀ (g : G) (θ : V →ₗ[ℂ] ℂ) (v : V), (dual_action g θ) v = θ (g⁻¹ • v)) :
  (∀ (θ : V →ₗ[ℂ] ℂ), dual_action 1 θ = θ) ∧
  (∀ (g h : G) (θ : V →ₗ[ℂ] ℂ), dual_action (g * h) θ = dual_action g (dual_action h θ)) := by
  sorry







theorem theorem_117417_problem
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (C : F → F)
  (hC : ∀ f : F, C f = (1 / 2 : ℝ) • f) :
  ∀ f g : F, ‖C f - C g‖ ≤ (1 / 2 : ℝ) * ‖f - g‖ := by
  sorry





theorem theorem_117638_problem (n : ℕ) (N : Matrix (Fin n) (Fin n) ℂ)
  (hN : N.trace = 0)
  (h_forall : ∀ m : Matrix (Fin n) (Fin n) ℂ, m.trace = 0 → ((m + m.conjTranspose) * N).trace = 0) :
  N = 0 := by
  sorry



theorem theorem_117709_problem 
  (K : Type*) [Field K] 
  (N : ℕ) 
  (n : Fin N → ℕ) 
  (hn : ∀ i, 0 < n i) : 
  ∃ (A : Subalgebra K (Matrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) K)), 
    (A : Set (Matrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) K)) = 
      { M | ∀ (i j : Σ k, Fin (n k)), i.1 ≠ j.1 → M i j = 0 } ∧ 
    Nonempty (A ≃ₐ[K] (Π i, Matrix (Fin (n i)) (Fin (n i)) K)) := by
  sorry

theorem theorem_117641_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (n m : ℕ) (hmn : m ≤ n)
  (e : Basis (Fin n) F V)
  (U : Submodule F V)
  (hU : U = Submodule.span F (e '' {i | (i : ℕ) < m})) :
  LinearIndependent F (fun (i : {j : Fin n // m ≤ (j : ℕ)}) ↦ e.dualBasis i) ∧
  Submodule.span F (Set.range (fun (i : {j : Fin n // m ≤ (j : ℕ)}) ↦ e.dualBasis i)) = U.dualAnnihilator := by
  sorry







theorem theorem_117945_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (K : Set X) (hK : IsCompact K) (hK_ne : K.Nonempty)
  (θ : ℝ) (hθ : 0 < θ) :
  ∃ s : Set X, s.Finite ∧ s ⊆ K ∧
    ∀ x ∈ K, Metric.infDist x (Submodule.span ℝ s) < θ := by
  sorry







theorem theorem_117905_problem :
  ∃ (n : ℕ) (N P₁ P₂ : Matrix (Fin n) (Fin n) ℝ),
    IsNilpotent N ∧
    P₁ ^ 2 = P₁ ∧
    P₂ ^ 2 = P₂ ∧
    N * P₁ = P₁ * N ∧ N * P₁ ≠ 0 ∧
    N * P₂ = P₂ * N ∧ N * P₂ ≠ 0 := by
  sorry



theorem theorem_118152_problem
  (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (S : Finset (Fin n × Fin n))
  (hS : S ⊂ Finset.univ) :
  ∑ i : Fin n, ∑ j : Fin n, |A i j|^2 ≥ ∑ x in S, |A x.1 x.2|^2 := by
  sorry

theorem theorem_118331_problem (n : ℕ) (H P R : Matrix (Fin n) (Fin n) ℝ)
  (hH : H.IsSymm)
  (hP : P.PosDef)
  (hR : R.PosDef) :
  (H * P * H.transpose + R).PosDef := by
  sorry

theorem theorem_118481_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (m : ℕ)
  (phi : Fin m → V)
  (alpha : Fin m → ℂ)
  (h_ortho : Orthonormal ℂ phi) :
  ‖∑ i, alpha i • phi i‖ ^ 2 = ∑ i, Complex.abs (alpha i) ^ 2 := by
  sorry

theorem theorem_118112_problem :
  ∃ (D : Set ℝ) (f : ℕ → ℝ → ℝ) (x : ℕ → ℝ),
    (∀ i, ContinuousOn (f i) D) ∧
    (∀ n, x n ∈ D) ∧
    Filter.liminf (fun n ↦ ⨆ i, f i (x n)) atTop ≠ ⨆ i, Filter.liminf (fun n ↦ f i (x n)) atTop := by
  sorry





theorem theorem_118087_problem (n : ℕ) (A B D : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
  (hA : A.IsHermitian) (hB : B.IsHermitian) :
  Complex.abs ((D * A * D * A * D * A * B) i i) ≤
  (Matrix.trace (A ^ 2)).re ^ ((3 : ℝ) / 2) *
  (Matrix.trace (B ^ 2)).re ^ ((1 : ℝ) / 2) *
  (Matrix.trace (D.conjTranspose * D)).re ^ ((3 : ℝ) / 2) := by
  sorry

















theorem theorem_118204_problem
  (n m : ℕ)
  (F : (Fin n → ℝ) → ℝ)
  (G : (Fin m → ℝ) → (Fin n → ℝ))
  (x : Fin m → ℝ)
  (hF : Differentiable ℝ F)
  (hG : Differentiable ℝ G) :
  fderiv ℝ (F ∘ G) x = (fderiv ℝ F (G x)).comp (fderiv ℝ G x) := by
  sorry

theorem theorem_118139_problem (m n : ℕ) (N : ℝ)
  (hmn : 2 ≤ min m n) (hN : 0 < N)
  (σA σB : ℕ → ℝ)
  (hσA : ∀ i, i < min m n → σA i = if i = 0 then 1/N else if i = 1 then N else 0)
  (hσB : ∀ i, i < min m n → σB i = if i = 0 then N else if i = 1 then 1/N else 0) :
  Real.sqrt (∑ i in Finset.range (min m n), (σA i)^2) = 
  Real.sqrt (∑ i in Finset.range (min m n), (σB i)^2) := by
  sorry

theorem theorem_118225_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [Field K] [DecidableEq K]
  (A : Matrix n n K)
  (x : Matrix n Unit K)
  (hA : Invertible A)
  (M : Matrix (Sum n Unit) (Sum n Unit) K)
  (hM : M = Matrix.fromBlocks (⅟A) x x.transpose 0) :
  (x.transpose * A * x) () () = - M.det * A.det := by
  sorry

theorem theorem_118699_problem (x lam : ℂ) :
  let f : ℂ → ℝ := Complex.normSq
  (fderiv ℝ f x) (lam * x) = 2 * lam.re * f x := by
  sorry



theorem theorem_118743_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (p v w : E)
  (r : ℝ)
  (hv : v ≠ 0)
  (hr : 0 < r)
  (C : Set E) (hC : C = Metric.closedBall w r)
  (q : E) (hq : q = p + (inner (w - p) v / ‖v‖ ^ 2) • v) :
  let proj := fun z ↦ p + (inner (z - p) v / ‖v‖ ^ 2) • v
  proj '' C = segment ℝ (q - (r / ‖v‖) • v) (q + (r / ‖v‖) • v) := by
  sorry





theorem theorem_118742_problem
  {X : Type*}
  (A B C : X → ℝ)
  (w_A w_B w_C : ℝ)
  (hw_A : w_A > 0)
  (hw_B : w_B > 0)
  (hw_C : w_C > 0)
  (x_star : X)
  (h_opt : ∀ x : X, w_A * A x - w_B * B x + w_C * C x ≤ w_A * A x_star - w_B * B x_star + w_C * C x_star) :
  ∀ y : X, (A y ≥ A x_star ∧ B y ≤ B x_star ∧ C y ≥ C x_star) →
  (A y = A x_star ∧ B y = B x_star ∧ C y = C x_star) := by
  sorry



theorem theorem_119366_problem
  (F : Type*) [Field F]
  (V : Type*) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (A : V ≃ₗ[F] V) :
  ∀ v : V, A v ∈ (Set.univ : Set V) ∧ A.symm v ∈ (Set.univ : Set V) := by
  sorry

theorem theorem_118224_problem
  (q₀ q₁ q₂ δ : ℝ)
  (hδ : δ = q₀ / 2 + q₁ / 3 + q₂ / 4)
  (α₀ α₁ α₂ : ℝ)
  (h1 : α₀ + α₁ / 2 + α₂ / 3 = 0)
  (h2 : α₀ / 2 + α₁ / 3 + α₂ / 4 = δ)
  (h3 : α₀ / 3 + α₁ / 4 + α₂ / 5 = 0) :
  α₀ = -36 * δ ∧ α₁ = 192 * δ ∧ α₂ = -180 * δ := by
  sorry

theorem theorem_118878_problem
  (a b : ℝ)
  (f g : ℝ → ℝ)
  (hf_smooth : ContDiff ℝ ⊤ f)
  (hg_smooth : ContDiff ℝ ⊤ g)
  (hf_boundary : f a = 0 ∧ f b = 0)
  (hg_boundary : g a = 0 ∧ g b = 0) :
  ∫ x in a..b, f x * deriv g x = ∫ x in a..b, -(deriv f x) * g x := by
  sorry

