import Mathlib
import Mathlib.Tactic

theorem theorem_622272_problem
  (Φ φ : ℝ → ℝ)
  (c u : ℝ)
  (h_mono : StrictMono Φ)
  (h_diff : Differentiable ℝ Φ)
  (h_deriv : ∀ x, deriv Φ x = φ x)
  (h_pos : ∀ x, 0 < φ x)
  (h_bij : Function.Bijective Φ)
  (hc : 0 < c) :
  deriv (fun t ↦ Function.invFun Φ (c * t)) u = c / φ (Function.invFun Φ (c * u)) := by
  sorry

theorem theorem_622298_problem 
  -- Define abstract types for Spectra and Graded Groups
  (Spectrum : Type*) 
  (GradedGroup : Type*) [AddCommGroup GradedGroup]
  -- Define abstract operators corresponding to the problem conditions
  (homology : Spectrum → Spectrum → GradedGroup) -- E_*(F)
  (homotopy : Spectrum → GradedGroup)            -- π_* E
  (tensor : GradedGroup → GradedGroup → GradedGroup) -- A ⊗ B
  (rationalize : GradedGroup → GradedGroup)      -- A ⊗ ℚ
  -- The objects
  (E F : Spectrum) :
  -- The conclusion: The two theories agree
  rationalize (homology E F) = rationalize (tensor (homotopy E) (homotopy F)) := by
  sorry













theorem theorem_622850_problem (n : ℕ) :
  ∑ k in Finset.range (n + 1), ((n : ℤ) - 2 * k)^2 * ((Nat.choose n k) : ℤ) = (n : ℤ) * 2^n := by
  sorry

theorem theorem_623013_problem
  (n : ℕ)
  (p : Fin n → ℕ)
  (v : Fin n → ℕ)
  (V_req : ℕ) :
  { c : ℕ | ∃ s : Finset (Fin n), ∑ i in s, v i ≥ V_req ∧ c = ∑ i in s, (p i / 2 + 1) } =
  { c : ℕ | ∃ x : Fin n → ℕ, (∀ i, x i = 0 ∨ x i = 1) ∧ ∑ i, x i * v i ≥ V_req ∧
    c = ∑ i, x i * (p i / 2 + 1) } := by
  sorry







theorem theorem_623104_problem (a b m n x : ℝ)
  (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
  deriv (fun x => (a + b * x ^ m) ^ n) x = n * m * b * x ^ (m - 1) * (a + b * x ^ m) ^ (n - 1) := by
  sorry







theorem theorem_623461_problem
  (c d : ℕ → ℝ)
  (t : ℝ)
  (ht : t ≠ 0)
  (h : ∀ n : ℕ, 3 * (n + 1) * c (n + 1) * t ^ n + 2 * c n * t ^ n - d n * t ^ n = 0) :
  ∀ n : ℕ, c (n + 1) = (d n - 2 * c n) / (3 * (n + 1)) := by
  sorry

theorem theorem_623415_problem
  (a : ℕ → ℝ)
  (h : ∀ n, a n = 1 / 2 + ((-1 : ℝ) ^ n * n) / (n + 1)) :
  sSup (Set.range a) = 3 / 2 := by
  sorry

theorem theorem_623532_problem
  {X : Type*} [MetricSpace X]
  (x₁ x₂ : X) (r₁ r₂ : ℝ)
  (hr1 : 0 < r₁) (hr2 : 0 < r₂)
  (h_subset : Metric.ball x₁ r₁ ⊆ Metric.ball x₂ r₂)
  (y : ℕ → X)
  (h_lim1 : Filter.Tendsto (fun n ↦ dist x₁ (y n)) Filter.atTop (nhds r₁))
  (h_lt : ∀ n, dist x₁ (y n) < r₁)
  (h_lim2 : Filter.Tendsto (fun n ↦ dist x₂ (y n)) Filter.atTop (nhds (r₁ + dist x₂ x₁))) :
  dist x₂ x₁ ≤ r₂ - r₁ := by
  sorry





theorem theorem_624179_problem {G : Type*} [Group G] (g : G) (m : ℕ)
  (hm : m > 0) (hg : orderOf g > 0) :
  m * orderOf (g ^ m) = Nat.lcm m (orderOf g) := by
  sorry



theorem theorem_623910_problem (k : ℕ) (a : Fin k → ℝ) (s t : ℕ → ℝ)
  (hs : ∀ n, s (n + k) = ∑ i : Fin k, a i * s (n + i))
  (ht : ∀ n, t (n + k) = ∑ i : Fin k, a i * t (n + i))
  (h_init : ∀ i : Fin k, s i = t i) :
  ∀ i < 2 * k, s i = t i := by
  sorry



theorem theorem_624432_problem (x : ℝ) (f : ℝ → ℝ) (h : ∀ x, f x = x^2) :
  HasDerivAt f (2 * x) x := by
  sorry

theorem theorem_623987_problem {E F : Type*} (f : E → F → Prop) :
  (∀ (y : F) (x₁ x₂ : E), f x₁ y → f x₂ y → x₁ = x₂) ↔
  (let f_inv := fun (y : F) (x : E) ↦ f x y
   ∀ (y : F) (x₁ x₂ : E), f_inv y x₁ → f_inv y x₂ → x₁ = x₂) := by
  sorry



theorem theorem_623566_problem (f : ℝ → ℝ)
  (h : ∀ x, f x = if x ≥ 0 
    then (3 * Real.pi / 2) * (Real.arctan x - Real.pi / 4)^2 + Real.pi^3 / 32
    else - ((3 * Real.pi / 2) * (Real.arctan x + Real.pi / 4)^2) - Real.pi^3 / 32) :
  Set.range f = Set.Ioc (-Real.pi^3 / 8) (-Real.pi^3 / 32) ∪ 
                Set.Icc (Real.pi^3 / 32) (Real.pi^3 / 8) := by
  sorry

theorem theorem_624480_problem (A B : Type) (f : A → B) :
  ∃! F : List A → List B,
    F [] = [] ∧
    ∀ (x : A) (y : List A), F (x :: y) = f x :: F y := by
  sorry

theorem theorem_625046_problem (a b m n : ℤ) 
  (h1 : n ∣ a) 
  (h2 : n ∣ m) 
  (h3 : ¬ n ∣ b) : 
  ¬ ∃ x : ℤ, a * x^2 ≡ b [ZMOD m] := by
  sorry



theorem theorem_624614_problem (m : ℝ) (a b c : ℝ)
  (h : ∀ x : ℝ, a * x^2 + b * x + c = x^2 + 2 * (m * x - (m - 4))^2 - 6) :
  b^2 - 4 * a * c = (4 * m * (m - 4))^2 - 4 * (1 + 2 * m^2) * (2 * m^2 - 16 * m + 26) := by
  sorry





theorem theorem_625153_problem (A B C x y : ℝ)
  (h : A * x + B * y = C * x * y) :
  (C * x - B) * (C * y - A) = A * B := by
  sorry











theorem theorem_624717_problem
  (xn : ℕ → ℝ)
  (h_pos : ∀ n, 0 < xn n)
  (h_lim : Filter.Tendsto xn Filter.atTop Filter.atTop) :
  TendstoUniformlyOn
    (fun n x => (x - xn n)^2 * Real.exp (-x) / (1 + (x - xn n)^2))
    (fun x => Real.exp (-x))
    Filter.atTop
    (Set.Ici 0) := by
  sorry

















theorem theorem_626289_problem
  {n : Type*} [DecidableEq n] [Fintype n]
  {R : Type*} [CommRing R]
  (A : Matrix n n R) (lam : R) (k : ℕ)
  (N : Matrix n n R)
  (hN : N = A - lam • (1 : Matrix n n R))
  (hN_sq : N ^ 2 = 0) :
  A ^ k = (lam ^ k) • (1 : Matrix n n R) + ((k : R) * lam ^ (k - 1)) • (A - lam • (1 : Matrix n n R)) := by
  sorry















theorem theorem_626175_problem (n : ℕ) (μ : List ℕ)
  (h_pos : 0 < n)
  (h_part : μ.sum = n)
  (h_sorted : μ.Sorted (· ≥ ·)) :
  let cells : Finset (ℕ × ℕ) :=
    (Finset.range μ.length).biUnion (fun i =>
      (Finset.range (μ.getD i 0)).image (fun j => (i, j)))
  let hook (c : ℕ × ℕ) : ℕ :=
    1 + (cells.filter (fun x => x.1 = c.1 ∧ x.2 > c.2)).card +
        (cells.filter (fun x => x.1 > c.1 ∧ x.2 = c.2)).card
  let fillings := { f : ℕ × ℕ → ℕ |
    (∀ c ∉ cells, f c = 0) ∧
    Set.BijOn f cells { k | 1 ≤ k ∧ k ≤ n } ∧
    (∀ c₁ c₂, c₁ ∈ cells → c₂ ∈ cells → c₁.1 = c₂.1 → c₁.2 < c₂.2 → f c₁ < f c₂) ∧
    (∀ c₁ c₂, c₁ ∈ cells → c₂ ∈ cells → c₁.2 = c₂.2 → c₁.1 < c₂.1 → f c₁ < f c₂) }
  Set.ncard fillings * ∏ c ∈ cells, hook c = n.factorial := by
  sorry

theorem theorem_626221_problem (c v_t v_f : ℝ) 
  (h_c : c = 0 ∨ c = 1) : 
  (c = 1 → c * v_t + (1 - c) * v_f = v_t) ∧ 
  (c = 0 → c * v_t + (1 - c) * v_f = v_f) := by
  sorry

theorem theorem_625830_problem
  (n : ℕ)
  (E : Type*)
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  (v : Basis (Fin n) ℝ E)
  (hv : Orthonormal ℝ v)
  (x : E)
  (hx : x ≠ 0) :
  ∃ c : ℝ, c > 0 ∧ ∃ j : Fin n, |inner x (v j)| ≥ c * ‖x‖ := by
  sorry





theorem theorem_626065_problem
  (n : ℕ)
  (hn : n ≥ 2)
  (R : Type*) [CommRing R]
  (x : Fin n → R) :
  (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i : Fin n, x (σ i) ^ (i : ℕ)) =
  Matrix.det (Matrix.of (fun i j => x j ^ (i : ℕ))) := by
  sorry



theorem theorem_626597_problem (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] :
  CompleteSpace (BoundedContinuousFunction (Set.Ici (0 : ℝ)) X) := by
  sorry







theorem theorem_626960_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (U : Submodule ℝ V)
  {k : ℕ}
  (u : Basis (Fin k) ℝ U)
  (h_ortho : Pairwise (fun i j => ⟪(u i : V), (u j : V)⟫_ℝ = 0))
  (x : V) :
  (orthogonalProjection U x : V) = ∑ i : Fin k, (⟪x, (u i : V)⟫_ℝ / ⟪(u i : V), (u i : V)⟫_ℝ) • (u i : V) := by
  sorry

theorem theorem_626885_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (z_T : E →L[ℝ] ℝ)
  (dual_norm : ℝ)
  (h_def : dual_norm = sSup {y | ∃ x : E, ‖x‖ ≤ 1 ∧ y = ‖z_T x‖}) :
  dual_norm = ‖z_T‖ := by
  sorry



theorem theorem_627037_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  (K : Submodule 𝕜 E) [CompleteSpace K]
  (g : E)
  (u : E)
  (hu : u = (orthogonalProjection K g : E)) :
  ‖u‖ ≤ ‖g‖ := by
  sorry

theorem theorem_626984_problem (N : ℕ) (x : ℝ)
  (h : ∀ k : ℤ, x ≠ 2 * (k : ℝ) * Real.pi) :
  ∑ n in Finset.Icc (-(N : ℤ)) (N : ℤ), Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) =
  ((Real.sin (((N : ℝ) + 1 / 2) * x) / Real.sin (x / 2)) : ℂ) := by
  sorry

theorem theorem_627313_problem (α : ℚ) (h : IsIntegral ℤ α) : 
  ∃ z : ℤ, (z : ℚ) = α := by
  sorry







theorem theorem_627462_problem
  {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : Y → X) (hp : IsCoveringMap p)
  (y₁ y₂ : Y) (h_distinct : y₁ ≠ y₂) (h_eq : p y₁ = p y₂) :
  ∃ V₁ V₂ : Set Y, IsOpen V₁ ∧ IsOpen V₂ ∧ y₁ ∈ V₁ ∧ y₂ ∈ V₂ ∧ Disjoint V₁ V₂ := by
  sorry

theorem theorem_626400_problem :
  ∃ (X : Type) (_ : TopologicalSpace X) (A : Set X),
    IsConnected (frontier A) ∧ ¬ IsConnected (interior A) := by
  sorry





theorem theorem_627597_problem
  (R : Type*) [CommRing R]
  (g h : ℕ) (r : ℤ) (ω : R)
  (IsRegular IsTotallyNonRegular : Ideal R → Prop)
  (J M : Ideal R)
  (hJ : J = Ideal.span { (g : R), (r : R) + ω })
  (hM : M = Ideal.span { (h : R), (r : R) + ω })
  (h_gcd : Nat.gcd g h = 1)
  (hJ_reg : IsRegular J)
  (hM_nreg : IsTotallyNonRegular M)
  (I : Ideal R)
  (hI : I = J * M) :
  ∀ (J' M' : Ideal R),
    IsRegular J' → IsTotallyNonRegular M' → I = J' * M' →
    J = J' ∧ M = M' := by
  sorry











theorem theorem_628499_problem {X : Type*} [MetricSpace X] (y : ℕ → X) (L : X)
  (h_even : Filter.Tendsto (fun n => y (2 * n)) Filter.atTop (nhds L))
  (h_odd : Filter.Tendsto (fun n => y (2 * n + 1)) Filter.atTop (nhds L)) :
  Filter.Tendsto y Filter.atTop (nhds L) := by
  sorry



theorem theorem_628427_problem
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : E → F) (x : E)
  (h_diff : DifferentiableAt ℝ f x) :
  ∃! L : E →L[ℝ] F, HasFDerivAt f L x := by
  sorry

theorem theorem_627509_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [TopologicalSpace F]
  (K : Set E) (D : Set F)
  (hK_conv : Convex ℝ K)
  (hK_bound : Bornology.IsBounded K)
  (hK_closed : IsClosed K)
  (hK_nonempty : K.Nonempty)
  (h : K ≃ₜ D)
  (T : K → K)
  (hT_cont : Continuous T)
  (hT_compact : IsCompact (closure (Set.range T))) :
  ∃ x₀ : K, T x₀ = x₀ := by
  sorry









theorem theorem_628858_problem (n k : ℕ) :
  ∑ i in Finset.Icc ⌈(n : ℚ) / 2⌉₊ n, ⌈(n : ℚ) / 2⌉₊ ^ k =
  (n - ⌈(n : ℚ) / 2⌉₊ + 1) * ⌈(n : ℚ) / 2⌉₊ ^ k := by
  sorry





