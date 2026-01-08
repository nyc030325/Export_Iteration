import Mathlib
import Mathlib.Tactic

theorem theorem_634519_problem
  {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LinearOrder Y] [OrderTopology Y]
  (f : X → Y) (x : X)
  (h_upper : UpperSemicontinuousAt f x)
  (h_lower : LowerSemicontinuousAt f x) :
  ContinuousAt f x ↔
    (∀ (x_n : ℕ → X), Filter.Tendsto x_n Filter.atTop (nhds x) →
      Filter.Tendsto (f ∘ x_n) Filter.atTop (nhds (f x))) := by
  sorry

theorem theorem_635316_problem (x : ℝ) (n : ℕ) (h_irr : Irrational x) :
  ∃ q : ℚ, (q : ℝ) = (Int.floor (x * 10 ^ n) : ℝ) / 10 ^ n := by
  sorry



theorem theorem_635045_problem
  (S : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ → Prop)
  (h : ∀ t : ℤ, S (t, 5 * t, 7 * t - 2, t + 1, 5 * t - 2, 7 * t - 1)) :
  Set.Infinite { x | S x } := by
  sorry





theorem theorem_635087_problem
  (r : ℝ → EuclideanSpace ℝ (Fin 3))
  (h_diff : ContDiff ℝ 2 r)
  (h_reg : ∀ t, deriv r t ≠ 0)
  (s' : ℝ → ℝ)
  (hs' : s' = fun t ↦ ‖deriv r t‖)
  (T : ℝ → EuclideanSpace ℝ (Fin 3))
  (hT : T = fun t ↦ (s' t)⁻¹ • deriv r t)
  (t : ℝ) :
  crossProduct (deriv r t) (deriv (deriv r) t) =
  (s' t) ^ 2 • crossProduct (T t) (deriv T t) := by
  sorry

theorem theorem_634896_problem (x a b : ℝ)
  (ha : a = Real.sqrt 2 + 1)
  (hb : b = Real.sqrt 2 - 1)
  (h : a ^ x + b ^ x = (6 : ℝ) ^ (x / 2)) :
  x = 2 := by
  sorry

theorem theorem_635419_problem (p k : ℕ) (hp : Nat.Prime p) (hk : k > 0) :
  Nat.totient (p ^ k) = p ^ k - p ^ (k - 1) := by
  sorry

theorem theorem_635141_problem
  {R : Type*} [CommRing R]
  {V : Type*} [AddCommGroup V] [Module R V]
  (g : V → V → R)
  (nabla : V → V → V)
  (action : V → R → R)
  (cov_deriv_g : V → V → V → R := fun X Y Z ↦ action X (g Y Z) - g (nabla X Y) Z - g Y (nabla X Z)) :
  (∀ X Y Z : V, cov_deriv_g X Y Z = 0) ↔
  (∀ X Y Z : V, action X (g Y Z) = g (nabla X Y) Z + g Y (nabla X Z)) := by
  sorry





theorem theorem_635237_problem 
  (x_c y_c z_c a b c x y z : ℝ) 
  (alpha : ℝ) 
  (n : ℕ) 
  (h_alpha : 0 < alpha ∧ alpha < Real.pi / 2) 
  (h_axis : a^2 + b^2 + c^2 ≠ 0) 
  (h_point : (x - x_c)^2 + (y - y_c)^2 + (z - z_c)^2 ≠ 0) : 
  let dot_prod := a * (x - x_c) + b * (y - y_c) + c * (z - z_c)
  let axis_norm_sq := a^2 + b^2 + c^2
  let vec_norm_sq := (x - x_c)^2 + (y - y_c)^2 + (z - z_c)^2
  let geometric_cone_cond := (dot_prod ^ 2) / (axis_norm_sq * vec_norm_sq) = (Real.cos alpha)^2
  let algebraic_expr := (dot_prod / Real.sqrt axis_norm_sq)^2 - vec_norm_sq * (Real.cos alpha)^2
  geometric_cone_cond ↔ abs algebraic_expr = 0 := by
  sorry





theorem theorem_635455_problem (A B C D : Fin 3 → ℝ) :
  Matrix.dotProduct (crossProduct A B) (crossProduct C D) =
  (Matrix.dotProduct A C) * (Matrix.dotProduct B D) - (Matrix.dotProduct A D) * (Matrix.dotProduct B C) := by
  sorry



theorem theorem_635724_problem
  (f : ℝ × ℝ → ℝ)
  (U : Set (ℝ × ℝ))
  (hU : IsOpen U)
  (h_diff : ContDiffOn ℝ 2 f U) :
  ∀ x y, (x, y) ∈ U →
    deriv (fun x' ↦ deriv (fun y' ↦ f (x', y')) y) x =
    deriv (fun y' ↦ deriv (fun x' ↦ f (x', y')) x) y := by
  sorry

theorem theorem_635992_problem (a b : ℝ) (hab : a ≤ b) (f g : ℝ → ℝ)
  (hf : IntervalIntegrable (fun x => (f x)^2) volume a b)
  (hg : IntervalIntegrable (fun x => (g x)^2) volume a b)
  (inner_prod : ℝ := ∫ x in a..b, f x * g x)
  (are_orthogonal : Prop := inner_prod = 0) :
  are_orthogonal ↔ inner_prod = 0 := by
  sorry

theorem theorem_635736_problem 
  -- Abstract types representing the concepts in the problem
  {Language TM NDTM : Type}
  -- Predicates corresponding to "decides in poly time" and "accepts in poly time"
  (decides_poly_time : TM → Language → Prop)
  (accepts_poly_time : NDTM → Language → (ℕ → ℕ) → Prop)
  -- The Complexity Class NP
  (is_NP : Language → Prop)
  -- The formal definition of NP as provided/implied by the problem text
  (h_NP_def : ∀ L, is_NP L ↔ ∃ N : NDTM, ∃ p : Polynomial ℕ, accepts_poly_time N L p.eval)
  -- Given conditions: L is a language, M is a TM
  (L : Language) (M : TM)
  -- M decides L in polynomial time
  (h_decides : decides_poly_time M L)
  -- L is in the class NP
  (h_in_NP : is_NP L) :
  -- Conclusion: Exists NDTM N and polynomial p accepting L
  ∃ N : NDTM, ∃ p : Polynomial ℕ, accepts_poly_time N L p.eval := by
  sorry







theorem theorem_636392_problem {X Y : Type*} (f : X → Y) :
  Function.Injective f ↔ ∀ A : Set X, f '' Aᶜ ⊆ (f '' A)ᶜ := by
  sorry











theorem theorem_636382_problem
  (n : ℕ) (hn : 0 < n)
  (f₁ : ℝ → ℝ) (h₁ : ∀ x, f₁ x = x / (1 + x^4))
  (fₙ : ℝ → ℝ) (h₂ : ∀ x, fₙ x = f₁ (n * x)) :
  ∀ x y : ℝ, |fₙ x - fₙ y| ≤ n * |x - y| := by
  sorry



theorem theorem_635981_problem (p : ℕ) [Fact p.Prime] :
  Nonempty (AddAut ((ZMod p) × (ZMod p)) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := by
  sorry

theorem theorem_636047_problem (n : ℕ) (h : n > 1) : 
  ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n := by
  sorry



theorem theorem_635946_problem
  -- Context: Manifold M, Vector spaces V, W
  {M : Type*} [TopologicalSpace M]
  {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  -- Abstract types for differential forms
  (FormV : Type*) (FormW : Type*) (FormW_next : Type*)
  [AddCommGroup FormW_next]
  -- Operators
  (d : FormW → FormW_next) -- Exterior derivative
  (ρ : V → W) -- Representation
  (wedge_rho : FormV → FormW → FormW_next) -- Composition of wedge and rho
  -- Specific forms
  (ω : FormV)
  (φ : FormW)
  -- Definition of covariant derivative
  (d_omega : FormW → FormW_next)
  (h_d_omega_def : ∀ ψ, d_omega ψ = d ψ + wedge_rho ω ψ)
  -- Condition: d_omega is flat
  (is_flat : (FormW → FormW_next) → Prop)
  (h_flat : is_flat d_omega)
  -- Geometry: N and boundary
  (N : Set M) (boundaryN : Set M)
  (h_compact : IsCompact N)
  (is_oriented : Set M → Prop) (h_oriented : is_oriented N)
  -- Integrals
  (int_N : FormW_next → W)
  (int_boundaryN : FormW → W)
  : int_N (d_omega φ) = int_boundaryN φ := by
  sorry





theorem theorem_636574_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (G : Set E) (f : E → ℝ) (x y : E)
  (h_open : IsOpen G)
  (h_diff : DifferentiableOn ℝ f G)
  (hx : x ∈ G) (hy : y ∈ G)
  (h_seg : segment ℝ x y ⊆ G) :
  ∃ z ∈ segment ℝ x y, inner (gradient f z) (y - x) = f y - f x := by
  sorry

theorem theorem_636713_problem (a b : Ordinal) (h : a < b) :
  Cardinal.aleph a < Cardinal.aleph b := by
  sorry



theorem theorem_636231_problem (n : ℕ) (z : Fin n → ℂ) (ψ : ℝ)
  (hn : 0 < n)
  (hψ : ψ < Real.pi / 4)
  (hz : ∀ i, |(z i).arg| ≤ ψ) :
  let AM := (∑ i, z i) / (n : ℂ)
  let QM := Real.sqrt ((∑ i, Complex.abs (z i) ^ 2) / (n : ℝ))
  let A := Real.cos (2 * ψ)
  Complex.abs AM ^ 2 ≤ (1 / A) * QM ^ 2 := by
  sorry

theorem theorem_636556_problem
  (X : Type*) [MetricSpace X] [ConnectedSpace X]
  (p₀ : X)
  (S : Set ℝ)
  (hS : S = Set.range (fun q => dist p₀ q)) :
  IsConnected S ∧ 0 ∈ S := by
  sorry

theorem theorem_636754_problem (a b : ℝ) (h_le : a ≤ b) (f : ℝ → ℝ)
  (h_cont : ContinuousOn f (Set.Icc a b))
  (h_im : Set.MapsTo f (Set.Icc a b) (Set.Icc a b)) :
  ∃ x ∈ Set.Icc a b, f x = x := by
  sorry



theorem theorem_636891_problem (h L U : ℝ) (x y : ℝ → ℝ)
  (h_pos : h > 0) (L_pos : L > 0) (U_pos : U > 0)
  (hx : ∀ t, deriv x t = U)
  (hy : ∀ t, y t = h * (2 * (x t / L) ^ 3 + 3 * (x t / L) ^ 2)) :
  ∀ t, deriv (deriv y) t = (6 * h * U ^ 2 / L ^ 2) * ((2 / L) * x t + 1) := by
  sorry



theorem theorem_637246_problem {G : Type*} [Group G] [Fintype G] (n : ℕ)
  (hn : Fintype.card G = n) (g : G) (hg : g ≠ 1) :
  orderOf g ∣ n := by
  sorry

theorem theorem_636585_problem (f : ℝ → ℝ) (u_L u_R k : ℝ)
  (h_u : u_L > u_R)
  (h_k : u_R < k ∧ k < u_L)
  (h_kruzhkov : let s := (f u_L - f u_R) / (u_L - u_R)
                s * (|u_L - k| - |u_R - k|) ≤ Real.sign (u_L - k) * (f u_L - f k) - Real.sign (u_R - k) * (f u_R - f k)) :
  (f k - f u_R) / (k - u_R) ≤ (f u_L - f u_R) / (u_L - u_R) ∧
  (f u_L - f u_R) / (u_L - u_R) ≤ (f k - f u_L) / (k - u_L) := by
  sorry

theorem theorem_636985_problem (n : ℕ) (x y : Fin n → ℝ)
  (A M : Matrix (Fin n) (Fin n) ℝ)
  (hn : n ≥ 3)
  (hA : ∀ i j, A i j = 1)
  (hM : M = A + Matrix.vecMulVec x y) :
  M.det = 0 := by
  sorry

theorem theorem_636738_problem (P : Type*) [PartialOrder P]
  (h : ∀ C : Set P, IsChain (· ≤ ·) C → ∃ b : P, ∀ x ∈ C, x ≤ b) :
  ∃ m : P, ∀ x : P, m ≤ x → m = x := by
  sorry

theorem theorem_637112_problem (x : ℝ) :
  (Real.cos x : ℂ) = (1 / 2 : ℂ) * (Complex.exp (Complex.I * x) + Complex.exp (-Complex.I * x)) := by
  sorry



theorem theorem_636927_problem
  {X : Type*} [TopologicalSpace X]
  [TotallyDisconnectedSpace X] [CompactSpace X] [T2Space X]
  (A : Set X) (hA : IsClosed A)
  (U : Set X) (hU : IsOpen U)
  (hAU : A ⊆ U) :
  ∃ S : Set (Set X), S.Finite ∧ (∀ V ∈ S, IsClopen V) ∧ A ⊆ ⋃₀ S ∧ ⋃₀ S ⊆ U := by
  sorry

theorem theorem_636830_problem
  (R : Type*) [CommRing R]
  (D : Submonoid R)
  (h0 : (0 : R) ∉ D) :
  let D_hat := {a : R | ∃ c : R, a * c ∈ D}
  ∀ (a : R) (b : D), IsUnit (Localization.mk a b) ↔ a ∈ D_hat := by
  sorry



theorem theorem_637320_problem
  (n N : ℕ)
  [Nonempty (Fin N)]
  (c : Fin N → Fin n → ℝ) :
  sInf (Set.range (fun x => ⨆ i, Matrix.dotProduct (c i) x)) =
  sInf { t | ∃ x, ∀ i, Matrix.dotProduct (c i) x ≤ t } := by
  sorry



theorem theorem_637457_problem (n : ℕ) (hn : 1 < n) :
  ¬ ∃ (L : LinearOrder (Fin n → ℝ)),
    TopologicalSpace.generateFrom {s : Set (Fin n → ℝ) | ∃ a, s = {x | L.lt a x} ∨ s = {x | L.lt x a}} =
    (inferInstance : TopologicalSpace (Fin n → ℝ)) := by
  sorry







theorem theorem_637405_problem
  {n : ℕ}
  (U : Set (Fin n → ℝ))
  (u : (Fin n → ℝ) → ℝ)
  (hU_open : IsOpen U)
  (hU_conn : IsConnected U)
  (hU_cpct : IsCompact (closure U))
  (hU_ne : U.Nonempty)
  (hu_cont : ContinuousOn u (closure U))
  (h_smp : ∀ x₀ ∈ U, IsMaxOn u (closure U) x₀ → ∀ x ∈ U, u x = u x₀) :
  sSup (u '' (closure U)) = sSup (u '' (frontier U)) := by
  sorry

theorem theorem_637608_problem (f : ℕ → ℕ) (hf : ∀ n, f n = n.succ.succ) (n : ℕ) :
  Even n ↔ ∃ m : ℕ, n = f^[m] 0 := by
  sorry

theorem theorem_637650_problem (n k : ℕ) (hn : n ≥ 3) (hk1 : 1 ≤ k) (hk2 : k < n) :
  let G : SimpleGraph (ZMod n) := SimpleGraph.fromRel (fun u v => v = u + (k : ZMod n))
  G.Connected ↔ Nat.gcd k n = 1 := by
  sorry

theorem theorem_637781_problem {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y) (h_cont : Continuous f) (h_closed : IsClosedMap f) (A : Set X) :
  closure (f '' A) = f '' (closure A) := by
  sorry



theorem theorem_637858_problem
  (X : Type*) [MetricSpace X] [CompleteSpace X]
  (x : ℕ → X) (r : ℕ → ℝ)
  (h_pos : ∀ n, 0 < r n)
  (h_lim : Filter.Tendsto r Filter.atTop (nhds 0))
  (h_nested : ∀ n, Metric.closedBall (x (n + 1)) (r (n + 1)) ⊆ Metric.closedBall (x n) (r n)) :
  ∃! p, p ∈ ⋂ n, Metric.closedBall (x n) (r n) := by
  sorry

theorem theorem_637807_problem {K : Type*} [Field K] [CharP K 2]
  (p q : Polynomial K) (n : ℕ) (hn : n > 0)
  (h : p ^ (2 ^ n) = q) :
  p ∣ q := by
  sorry



theorem theorem_638291_problem (x : ℝ) (h : Real.sin x = x) : x = 0 := by
  sorry



theorem theorem_638010_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (X Y : Matrix n n ℝ)
  (hX : X.PosDef)
  (hY : Y.PosDef)
  (X_sqrt : Matrix n n ℝ) (hX_sqrt_sq : X_sqrt ^ 2 = X) (hX_sqrt_pd : X_sqrt.PosDef)
  (XY_sqrt : Matrix n n ℝ) (hXY_sqrt_sq : XY_sqrt ^ 2 = X * Y) (hXY_sqrt_pd : XY_sqrt.PosDef)
  (RHS_sqrt : Matrix n n ℝ) (hRHS_sqrt_sq : RHS_sqrt ^ 2 = X_sqrt * Y * X_sqrt) (hRHS_sqrt_pd : RHS_sqrt.PosDef) :
  X_sqrt⁻¹ * XY_sqrt * X_sqrt = RHS_sqrt := by
  sorry

theorem theorem_638088_problem (x : ℝ) (h : 0 < x) :
  HasDerivAt (fun y => y ^ (3 / 2 : ℝ) - y ^ (-(1 / 2 : ℝ)))
    ((3 / 2 : ℝ) * x ^ (1 / 2 : ℝ) + (1 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ))) x := by
  sorry



theorem theorem_638337_problem
  (K : Type*) [Field K]
  (Omega : Type*) [Ring Omega] [Algebra K Omega]
  (A B : Subalgebra K Omega)
  (h : Function.Injective (TensorProduct.lift (LinearMap.mul K Omega) ∘ₗ TensorProduct.map A.val.toLinearMap B.val.toLinearMap)) :
  A ⊓ B = ⊥ := by
  sorry

theorem theorem_637962_problem (g : ℝ → ℝ)
  (h : ∀ x, 0 < x →
    ∃ L, Filter.Tendsto (fun y => -Real.cos y / y) Filter.atTop (nhds L) ∧
    ∃ I, Filter.Tendsto (fun T => ∫ y in (1 / x)..T, Real.sin y / y) Filter.atTop (nhds I) ∧
    g x = (L - (-Real.cos (1 / x) / (1 / x))) - I) :
  Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  sorry









theorem theorem_638590_problem
  (N K : ℕ)
  (hN : 1 ≤ N)
  (hK : N ≤ K)
  (m : Fin K → ℤ)
  (hm_pos : ∀ i, 0 < m i)
  (hm_inj : Function.Injective m)
  (v : Fin K → (Fin N → ℝ))
  (hv : ∀ i j, v i j = (m i : ℝ) ^ (j : ℕ)) :
  ∀ (s : Finset (Fin K)), s.card = N →
    ∃ b : Basis s ℝ (Fin N → ℝ), ∀ i : s, b i = v i := by
  sorry



theorem theorem_638841_problem
  (R : Type*) [Ring R] [IsNoetherianRing R]
  (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
  (N : Submodule R M) :
  Module.Finite R N := by
  sorry



theorem theorem_638828_problem (a : ℕ → ℝ)
  (h_mono : Monotone a ∨ Antitone a)
  (h_lim : Filter.Tendsto a Filter.atTop (nhds 0)) :
  Summable a ↔ Summable (fun n ↦ (2 : ℝ) ^ n * a (2 ^ n)) := by
  sorry

theorem theorem_637984_problem (f : ℝ → ℝ)
  (h1 : ∀ x : ℚ, Irrational (f x))
  (h2 : ∀ x : ℝ, Irrational x → ∃ q : ℚ, f x = q) :
  ¬ Continuous f := by
  sorry

theorem theorem_638951_problem
  {X : Type*} [MeasurableSpace X]
  (f : ℕ → X → ℝ)
  (hf : ∀ i, Measurable (f i))
  (n m k : ℕ) :
  MeasurableSet {x | f n x - f m x < 1 / (k : ℝ)} := by
  sorry

theorem theorem_639173_problem
  {E F : Type*}
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  (g : E →ᵃ[ℝ] F)
  (h : F → ℝ)
  (h_convex : ConvexOn ℝ Set.univ h) :
  ConvexOn ℝ Set.univ (h ∘ g) := by
  sorry









theorem theorem_639394_problem (K A θ₁ θ₂ θ₃ : ℝ)
  (h_triangle : K * A + (Real.pi - θ₁) + (Real.pi - θ₂) + (Real.pi - θ₃) = 2 * Real.pi) :
  K * A = θ₁ + θ₂ + θ₃ - Real.pi := by
  sorry





theorem theorem_639579_problem {G : Type*} [CommGroup G] [Fintype G] (a b : G) :
  orderOf (a * b) ∣ Nat.lcm (orderOf a) (orderOf b) := by
  sorry

theorem theorem_639889_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
  (v y : Fin (n * n) → ℝ)
  (h_symm : A.IsSymm)
  (hv : ∀ (i j : Fin n), v (finProdFinEquiv (i, j)) = x i * x j)
  (hy : ∀ (i j : Fin n), y (finProdFinEquiv (i, j)) = A i j) :
  Matrix.dotProduct x (Matrix.mulVec A x) = Matrix.dotProduct v y := by
  sorry

theorem theorem_639481_problem (n : ℕ) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) :
  ∀ σ_opt : Equiv.Perm (Fin n),
  Monotone (t ∘ σ_opt) →
  ∀ σ : Equiv.Perm (Fin n),
    ∑ k : Fin n, (∑ i in Finset.filter (· ≤ k) Finset.univ, t (σ_opt i))^2 ≤
    ∑ k : Fin n, (∑ i in Finset.filter (· ≤ k) Finset.univ, t (σ i))^2 := by
  sorry

theorem theorem_639442_problem :
  ∃ A B : Set ℝ, ¬ (frontier A ∪ frontier B ⊆ frontier (A ∪ B)) := by
  sorry



