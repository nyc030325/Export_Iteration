import Mathlib
import Mathlib.Tactic





theorem theorem_483741_problem {K : Type*} [RCLike K] (a : ℕ → K)
  (h : Summable (fun n ↦ a (n + 1))) :
  ∑' n, a (n + 2) = -a 1 + ∑' n, a (n + 1) := by
  sorry

theorem theorem_483166_problem :
  ∫ p : ℝ × ℝ × ℝ in {p | p.1^2 + p.2.1^2 + p.2.2^2 ≤ p.1}, 1 / p.1 = π / 2 := by
  sorry

theorem theorem_483329_problem :
  let f : ℝ → ℂ := fun x => (x : ℂ) - (1 / 2 : ℂ)
  let h : ℝ → ℂ := fun x => f x / (Complex.abs (f x) : ℂ)
  ¬ ∃ g : ℝ → ℂ, ContinuousOn g (Set.Icc 0 1) ∧
    ∀ x ∈ Set.Icc 0 1, x ≠ 1 / 2 → g x = h x := by
  sorry





theorem theorem_483514_problem (n s : ℕ) (p : Fin n → ℝ)
  (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
  let sample_space : Finset (Fin s → Fin n) := Finset.univ
  let prob (ω : Fin s → Fin n) : ℝ := ∏ j, p (ω j)
  let X (i : Fin n) (ω : Fin s → Fin n) : ℝ := if i ∈ Set.range ω then 1 else 0
  let expected_value (Y : (Fin s → Fin n) → ℝ) : ℝ := ∑ ω in sample_space, prob ω * Y ω
  expected_value (fun ω => ∑ i, X i ω) = (n : ℝ) - ∑ i, (1 - p i) ^ s := by
  sorry







theorem theorem_484182_problem
  (f : ℝ × ℝ → ℝ)
  (h g : ℝ → ℝ)
  (hf : Differentiable ℝ f)
  (hh : Differentiable ℝ h)
  (hg : Differentiable ℝ g)
  (x : ℝ) :
  deriv (fun t => f (h t, g t)) x =
    deriv (fun u => f (u, g x)) (h x) * deriv h x +
    deriv (fun v => f (h x, v)) (g x) * deriv g x := by
  sorry







theorem theorem_484628_problem (f : ℝ → ℝ → ℝ) (c : ℝ)
  (h_supp : ∀ x y, f x y = if |x| + |y| ≤ 2 then c else 0)
  (h_norm : ∫ p : ℝ × ℝ, f p.1 p.2 = 1) :
  ∀ y, ∫ x, f x y =
    if -2 < y ∧ y ≤ 0 then (y + 2) / 4
    else if 0 < y ∧ y < 2 then (2 - y) / 4
    else 0 := by
  sorry



theorem theorem_484596_problem
  {M : Type*} [TopologicalSpace M]
  {n : ℕ}
  (U : Set M) (hU : IsOpen U)
  (I : Type*) (W : I → Set M)
  (hW_open : ∀ i, IsOpen (W i))
  (hW_sub : ∀ i, W i ⊆ U)
  (hW_cover : (⋃ i, W i) = U)
  -- y_i are regular charts; modeled as functions to R^n
  (y : I → M → (Fin n → ℝ))
  -- x is the chart mapping referred to in the conclusion
  (x : M → (Fin n → ℝ))
  (A : Set M) (hA : A ⊆ U) :
  x '' A = ⋃ i, x '' (A ∩ W i) := by
  sorry





theorem theorem_484896_problem (c1 c2 : ℝ → ℝ) (x : ℝ)
  (h_valid : Real.cos x ≠ 0)
  (h_eq : c1 x * (Real.cos (2 * x))^2 + c2 x * Real.cos (2 * x) * Real.sin (2 * x) -
          c2 x * Real.cos (2 * x) * Real.sin (2 * x) + c1 x * (Real.sin (2 * x))^2 =
          -Real.tan x * Real.sin (2 * x)) :
  c1 x = Real.cos (2 * x) - 1 := by
  sorry







theorem theorem_484684_problem
  (K : String → ℕ)
  (K_cond : String → String → ℕ)
  (m n : String)
  (hm : m = "0")
  (hn : n = "10")
  (hKm : K m = 2)
  (hKn : K n = 1)
  (hKnm : K_cond n m = 0)
  (hKmn : K_cond m n = 0) :
  ((K m : ℚ) + (K_cond n m : ℚ)) / ((K n : ℚ) + (K_cond m n : ℚ)) = 2 := by
  sorry







theorem theorem_485495_problem
  {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
  (νs : ℕ → ContinuousMap K ℝ →L[ℝ] ℝ)
  (ν : ContinuousMap K ℝ →L[ℝ] ℝ)
  (h : ∀ f : ContinuousMap K ℝ, ∃ c_f : ℝ, ∀ n, ‖νs n f - ν f‖ ≤ c_f * a n) :
  ∃ c > 0, ∀ n, ‖νs n - ν‖ ≤ c * a n := by
  sorry









theorem theorem_485534_problem (n : ℕ) (x : ℝ) (b k : ℕ → ℝ)
  (f : ℕ → ℝ)
  (h_def : ∀ i, f i = (x - b i) / (k i))
  (h_range : ∀ i ∈ Finset.Icc 1 n, 0 < f i ∧ f i ≤ 1) :
  ∏ i in Finset.Icc 1 n, f i = Real.exp (∑ i in Finset.Icc 1 n, Real.log (f i)) := by
  sorry

theorem theorem_484613_problem :
  ∫ x in (0 : ℝ)..(2 * Real.pi), Real.exp (Real.cos x) * Real.cos (Real.sin x) = 2 * Real.pi := by
  sorry







theorem theorem_484954_problem 
  (α : ℝ) (x y z : ℝ → ℝ)
  (h_smooth_x : ContDiff ℝ 6 x)
  (h_smooth_y : ContDiff ℝ 6 y)
  (h_smooth_z : ContDiff ℝ 6 z)
  (hα : α ≠ 0)
  (h1 : ∀ t, iteratedDeriv 2 x t = α * (y t + (x t - 2 * (x t)^3) / 7))
  (h2 : ∀ t, iteratedDeriv 2 y t = x t - y t + z t)
  (h3 : ∀ t, iteratedDeriv 2 z t = (1/100 : ℝ) * y t) :
  ∀ t, 
    700 * iteratedDeriv 6 x t + 
    600 * α * (x t)^2 * iteratedDeriv 4 x t - 
    100 * (α - 7) * iteratedDeriv 4 x t + 
    4800 * α * x t * iteratedDeriv 1 x t * iteratedDeriv 3 x t + 
    3600 * α * x t * (iteratedDeriv 2 x t)^2 + 
    7200 * α * (iteratedDeriv 1 x t)^2 * iteratedDeriv 2 x t + 
    600 * α * (x t)^2 * iteratedDeriv 2 x t - 
    (800 * α + 7) * iteratedDeriv 2 x t + 
    1200 * α * x t * (iteratedDeriv 1 x t)^2 - 
    2 * α * (x t)^3 + 
    α * x t = 0 := by
  sorry



theorem theorem_485256_problem (z a ρ c : ℝ)
  (hz : z ≠ 0) (ha : a ≠ 0) (hρ : ρ ≠ 0) (hc : c ≠ 0) (hc_pos : c > 0)
  (h_eq : (z + a + Real.sqrt (ρ^2 + (z + a)^2)) / (z - a + Real.sqrt (ρ^2 + (z - a)^2)) = c) :
  ((ρ * (1 - c^2)) / (2 * Real.sqrt c * (1 + c)))^2 + ((z * (1 - c)) / (1 + c))^2 = 1 := by
  sorry

theorem theorem_485786_problem
  (n : ℕ)
  (L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ → ℝ)
  (C : (Fin n → ℝ) → ℝ → ℝ)
  (k : ℝ)
  (lam : ℝ)
  (q v : Fin n → ℝ)
  (t : ℝ)
  (hL_q : DifferentiableAt ℝ (fun x => L x v t) q)
  (hL_v : DifferentiableAt ℝ (fun y => L q y t) v)
  (hC_q : DifferentiableAt ℝ (fun x => C x t) q) :
  let L_original := fun (x y : Fin n → ℝ) => L x y t - lam * C x t
  let L_modified := fun (x y : Fin n → ℝ) => L x y t - lam * (C x t + k)
  (fderiv ℝ (fun x => L_original x v) q = fderiv ℝ (fun x => L_modified x v) q) ∧
  (fderiv ℝ (fun y => L_original q y) v = fderiv ℝ (fun y => L_modified q y) v) := by
  sorry

theorem theorem_485852_problem :
  Summable (fun n : ℕ => if 2 ≤ n then 1 / ((n : ℝ) ^ 3 * Real.log n) else 0) := by
  sorry

theorem theorem_485859_problem
  -- Algebraic structures representing Homology
  (HQ : Type*) [AddCommGroup HQ] [Module ℚ HQ]
  (HZ : Type*) [AddCommGroup HZ]
  (i : HZ →+ HQ) -- Natural map from integer to rational homology
  (inter : HQ → HQ → ℚ) -- Intersection pairing
  -- Properties of the intersection pairing (Bilinearity)
  (h_lin_left : ∀ a b c, inter (a + b) c = inter a c + inter b c)
  (h_lin_right : ∀ a b c, inter a (b + c) = inter a b + inter a c)
  -- Property: Intersection of integer classes is an integer
  (h_int : ∀ a b : HZ, ∃ k : ℤ, inter (i a) (i b) = k)
  -- Definition of Disjointness property for cycles
  (are_disjoint : HZ → HZ → Prop)
  (h_disjoint_ortho : ∀ a b, are_disjoint a b → inter (i a) (i b) = 0 ∧ inter (i b) (i a) = 0)
  -- The specific class [f(S)]
  (S_class : HQ)
  -- Condition: The self-intersection number is not an integer
  (h_val_not_int : ¬ ∃ k : ℤ, inter S_class S_class = k) :
  -- Conclusion: No decomposition into disjoint integer cycles exists
  ¬ ∃ α β : HZ, i α + i β = S_class ∧ are_disjoint α β := by
  sorry



theorem theorem_486031_problem
  (f g : ℝ → ℝ)
  (hf : ∀ x ∈ Set.Icc 0 2, f x = (3/4 : ℝ) * (2 * x - x^2))
  (hg : ∀ x ∈ Set.Icc 0 2, g x = (1/2 : ℝ)) :
  sSup ((fun x ↦ f x / g x) '' Set.Icc 0 2) = 3/2 := by
  sorry











theorem theorem_486263_problem (T : Set ℕ)
  (h1 : 0 ∈ T)
  (h2 : ∀ n : ℕ, n ∈ T → n + 1 ∈ T) :
  T = Set.univ := by
  sorry



theorem theorem_485746_problem (x : ℝ → ℝ)
  (h_pos : ∀ y > 0, x y > 0)
  (h_diff : DifferentiableOn ℝ x (Set.Ioi 0))
  (h_de : ∀ y > 0, y * Real.log (x y * y) * deriv x y + x y = 0) :
  ∃ C : ℝ, ∀ y > 0, x y * (Real.log (x y * y) - 1) = C := by
  sorry

theorem theorem_486569_problem (n d : ℕ) (p : Fin (n + 1) → Fin d → ℝ)
  (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
  (∑ k : Fin (n + 1), ((n.choose (k : ℕ) : ℝ) * t ^ (k : ℕ) * (1 - t) ^ (n - (k : ℕ))) • p k) ∈
    convexHull ℝ (Set.range p) := by
  sorry

theorem theorem_486396_problem {R G : Type*} [Ring R] [Group G] :
  let ε : MonoidAlgebra R G → R := fun x ↦ x.sum (fun _ r ↦ r)
  (∀ x y : MonoidAlgebra R G, ε (x + y) = ε x + ε y) ∧
  (∀ x y : MonoidAlgebra R G, ε (x * y) = ε x * ε y) ∧
  (ε 1 = 1) := by
  sorry

theorem theorem_486146_problem
  (U : Set ℂ) (f : ℂ → ℂ) (z : ℂ)
  (h_open : IsOpen U)
  (h_conn : IsConnected U)
  (hf : DifferentiableOn ℂ f U)
  (hz : z ∈ U)
  (h_not_const : ¬ ∀ (x y : ℂ), x ∈ U → y ∈ U → f x = f y) :
  ¬ IsLocalMax (fun w => Complex.abs (f w)) z := by
  sorry



theorem theorem_486071_problem (f : ℤ → ℤ)
  (h0 : f 0 = 0)
  (h1 : f 1 = 1)
  (h_rec : ∀ n : ℤ, f (n + 2) = f (n + 1) + f n) :
  ∀ n : ℤ, f (n + 1) * f (n + 2) - f (n - 1) * f n = f (2 * n + 1) := by
  sorry

theorem theorem_486723_problem
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] (h_dim : FiniteDimensional.finrank ℝ V = 2)
  (dN : V →ₗ[ℝ] V)
  (κ₁ κ₂ : ℝ)
  (h_principal_curvatures : ∃ v₁ v₂ : V, Orthonormal ℝ ![v₁, v₂] ∧ dN v₁ = κ₁ • v₁ ∧ dN v₂ = κ₂ • v₂)
  (K : ℝ)
  (h_K_def : K = κ₁ * κ₂) :
  K = LinearMap.det dN := by
  sorry

theorem theorem_486676_problem {F V : Type*} [Field F] [AddCommGroup V] [Module F V] :
  ∃! z : V, ∀ v : V, v + z = v := by
  sorry



theorem theorem_486411_problem
  {α : Type*} [MetricSpace α]
  (f g : α → ℝ)
  (h1 : ∀ x, g x = (f x)^2)
  (h2 : ∀ x, 0 ≤ f x)
  (h3 : UniformContinuous g) :
  UniformContinuous f := by
  sorry





theorem theorem_487110_problem (X : Type*) (T : TopologicalSpace X) (A : Set X) :
  T.IsOpen A ↔ (A ⊆ Set.univ ∧ T.IsOpen A) := by
  sorry











theorem theorem_487537_problem (x y z : ℕ)
  (hx : x > 0) (hy : y > 0) (hz : z > 0)
  (h : x.factorial * y.factorial = x.factorial + y.factorial + z.factorial) :
  x = 3 ∧ y = 3 ∧ z = 4 := by
  sorry

theorem theorem_487309_problem (n : ℕ) (ϕ : Multiplicative (ZMod n) →* ℂˣ) :
  Set.range ϕ ⊆ {z : ℂˣ | z ^ n = 1} := by
  sorry

theorem theorem_487470_problem (ϕ : SchwartzMap ℝ ℂ) :
  ∫ x : ℝ, ∫ k : ℝ, ϕ k * Complex.exp (I * k * x) = 2 * (π : ℂ) * ϕ 0 := by
  sorry



theorem theorem_487399_problem
  (m : ℕ)
  (a : ℤ → ℝ)
  (u : ℤ → ℝ)
  (hu : ∀ k, u k = if k ≥ 0 then 1 else 0)
  (h_series : ∀ n : ℕ, ((n : ℝ)^2 - (m : ℝ)^2) * a n + u ((n : ℤ) - 2) * a ((n : ℤ) - 2) = 0)
  (n : ℕ)
  (hn : n ≠ m) :
  a n = - (u ((n : ℤ) - 2) * a ((n : ℤ) - 2)) / ((n : ℝ)^2 - (m : ℝ)^2) := by
  sorry









theorem theorem_488187_problem (P Q R : Prop) : (P → Q) ∨ (Q → R) := by
  sorry

theorem theorem_487879_problem
  (p q E : ℝ → ℝ)
  (P Q : ℝ → ℝ)
  (hP : ∀ x, HasDerivAt P (p x) x)
  (hQ : ∀ x, HasDerivAt Q (q x * Real.exp (P x)) x)
  (hE_diff : Differentiable ℝ E)
  (hODE : ∀ x, deriv E x + p x * E x = q x) :
  ∃ C : ℝ, ∀ x, E x = Real.exp (-P x) * (Q x + C) := by
  sorry

theorem theorem_487511_problem (x : ℝ) (h1 : x ≠ 0) (h2 : |x| < 3) :
  HasDerivAt (fun x => - (Real.sqrt (9 - x^2)) ^ 3 / (27 * x^3))
    (Real.sqrt (9 - x^2) / x^4) x := by
  sorry



theorem theorem_488550_problem :
  ∃ (z : ℂ), IsAlgebraic ℚ z ∧
  ∃ (q : IntermediateField.adjoin ℚ {z}),
    (q : ℂ) ∈ Set.range (algebraMap ℝ ℂ) ∧
    (q : ℂ) ∉ Set.range (algebraMap ℚ ℂ) := by
  sorry

theorem theorem_488022_problem (f g : Polynomial ℝ)
  (hf_monic : f.Monic) (hg_monic : g.Monic)
  (hf_irr : Irreducible f) (hg_irr : Irreducible g)
  (h_distinct : f ≠ g) :
  EuclideanDomain.gcd f g = 1 := by
  sorry

theorem theorem_488223_problem
  (N : ℕ)
  (p : ℝ)
  (x : EuclideanSpace ℝ (Fin N))
  (hx : x ≠ 0) :
  gradient (fun (y : EuclideanSpace ℝ (Fin N)) ↦ (∑ i, (y i) ^ 2) ^ (p / 2)) x =
  (p * (∑ i, (x i) ^ 2) ^ (p / 2 - 1)) • x := by
  sorry



theorem theorem_488498_problem (α β : ℂ)
  (h1 : (α + β).im = 0)
  (h2 : (α * β).im = 0)
  (h3 : α ≠ β) :
  ∀ m : ℕ, ((α^m - β^m) / (α - β)).im = 0 := by
  sorry

theorem theorem_488048_problem
  (f : ℝ → ℝ)
  (θ : ℝ)
  (hθ₁ : 0 ≤ θ)
  (hθ₂ : θ < 1)
  (h_contr : ∀ x y, |f x - f y| ≤ θ * |x - y|)
  (x : ℝ) :
  Summable (fun n : ℕ ↦ f^[n + 1] x) := by
  sorry









theorem theorem_488533_problem
  (G : ℝ → ℝ)
  (ρ γ : ℝ)
  (n : ℤ)
  (hρ_pos : 0 < ρ)
  (hρ_ne_one : ρ ≠ 1)
  (hγ_pos : 0 < γ)
  (h_rec : ∀ z, 0 < z → G (ρ * z) = G z / (γ * z ^ n)) :
  ∃ Θ : ℝ → ℝ, (∀ x, Θ (x + 1) = Θ x) ∧
    ∀ z, 0 < z →
      G z = Θ (Real.logb ρ z) * γ ^ (-Real.logb ρ z) *
            ρ ^ (-(n : ℝ) * Real.logb ρ z * (Real.logb ρ z - 1) / 2) := by
  sorry

theorem theorem_488511_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
  let B := A.map Complex.re
  let C := A.map Complex.im
  let A_tilde := Matrix.fromBlocks B (-C) C B
  Matrix.det A_tilde = Complex.abs (Matrix.det A) ^ 2 := by
  sorry







theorem theorem_489197_problem
  -- We define abstract types to represent the mathematical objects involved
  {Graph : Type*}
  {Matroid : Type*}
  {Polynomial : Type*}
  -- We define the functions mapping graphs to their associated structures
  (cycleMatroid : Graph → Matroid)
  (cocycleMatroid : Graph → Matroid)
  (tuttePolynomial : Graph → Polynomial)
  -- We define the isomorphism relation between matroids
  (isomorphic : Matroid → Matroid → Prop)
  -- The input graphs
  (G1 G2 : Graph)
  -- The conditions given in the problem
  (h1 : isomorphic (cycleMatroid G1) (cycleMatroid G2))
  (h2 : isomorphic (cocycleMatroid G1) (cocycleMatroid G2)) :
  -- The conclusion to be proven
  tuttePolynomial G1 = tuttePolynomial G2 := by
  sorry

