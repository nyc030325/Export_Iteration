import Mathlib
import Mathlib.Tactic

theorem theorem_858807_problem
  (R : Type*) [CommRing R] [IsDomain R]
  (h1 : ∀ x : R, x ≠ 0 → ∃ (s : Multiset R), (∀ p ∈ s, Prime p) ∧ s.prod = x)
  (h2 : ∀ p : R, Prime p → (Ideal.span {p}).IsMaximal) :
  IsPrincipalIdealRing R := by
  sorry





theorem theorem_859202_problem
  (n m p : ℕ)
  (f : (Fin n → ℝ) → (Fin m → ℝ))
  (g : (Fin m → ℝ) → (Fin p → ℝ))
  (x : Fin n → ℝ)
  (hf : DifferentiableAt ℝ f x)
  (hg : DifferentiableAt ℝ g (f x)) :
  fderiv ℝ (g ∘ f) x = (fderiv ℝ g (f x)).comp (fderiv ℝ f x) := by
  sorry



theorem theorem_859306_problem
  (f : ℕ → ℝ → ℝ)
  (h_def : ∀ n x, f n x = Set.indicator (Set.Icc ((2 : ℝ) ^ (-(n : ℤ) - 1)) ((2 : ℝ) ^ (-(n : ℤ)))) (fun y => 1 / Real.sqrt y) x)
  (x : ℝ)
  (hx : 0 < x) :
  Filter.Tendsto (fun n => f n x) Filter.atTop (nhds 0) := by
  sorry



theorem theorem_859105_problem 
  (Theory : Type) 
  (ZFC NBG : Theory) 
  (HasFiniteClassComprehension : Theory → Prop) 
  (FinitelyAxiomatizableWithin : Theory → Theory → Prop) : 
  HasFiniteClassComprehension NBG → FinitelyAxiomatizableWithin ZFC NBG := by
  sorry





theorem theorem_858964_problem (n : ℕ) (h_neq_1 : n ≠ 1) (h_pos : 0 < n) :
  let B : ℕ → ℚ := fun i ↦ if i = 1 then -1/2 else bernoulli i
  B n = - ∑ k in Finset.range n, (Nat.choose n k : ℚ) * B k / (n + 1 - k) := by
  sorry



theorem theorem_859539_problem (X : Type*) [Infinite X] :
  ∃ a : ℕ → X, Function.Injective a := by
  sorry

theorem theorem_859629_problem (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y) :
  Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := by
  sorry







theorem theorem_860033_problem
  (V : ℝ → EuclideanSpace ℝ (Fin 3))
  (h_smooth : ContDiff ℝ ⊤ V) :
  deriv (fun t => crossProduct (V t) (deriv V t)) = 
  fun t => crossProduct (V t) (deriv (deriv V) t) := by
  sorry





theorem theorem_858990_problem
  {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  (a b c : R) (n : ℕ)
  (h_coprime : IsCoprime a b)
  (hn : n > 0)
  (h1 : a ∣ c ^ n)
  (h2 : b ∣ c ^ n) :
  a * b ∣ c := by
  sorry







theorem theorem_860203_problem (R : Type*) [Ring R] 
  (S : Set R) (hS : S = {a | ∃ b : R, b * a = 1}) 
  (x : R) (hxS : x ∈ S) (hx_no_rinv : ∀ z : R, x * z ≠ 1) :
  ¬ ∃ (G : Group S), ∀ (a b : S), G.mul a b = a.val * b.val := by
  sorry



theorem theorem_860163_problem 
  {X : Type*}
  (x : X)
  (σ_sq : ℕ → X → ℝ)
  (smoothness_and_likelihood_conditions : (ℕ → X → ℝ) → Prop)
  (h_assumptions : smoothness_and_likelihood_conditions σ_sq) :
  ∃ C > 0, ∀ᶠ (n : ℕ) in at_top, σ_sq n x ≤ C / Real.log (n : ℝ) := by
  sorry

theorem theorem_860243_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (h_inf : ¬ FiniteDimensional 𝕜 H) :
  ¬ IsCompactOperator (ContinuousLinearMap.id 𝕜 H) := by
  sorry



theorem theorem_860018_problem (n R P V T : ℝ)
  (hn : n ≠ 0) (hR : R ≠ 0) (hP : P ≠ 0) (hV : V ≠ 0)
  (h_gas : P * V = n * R * T) :
  (deriv (fun v => (n * R * T) / v) V) *
  (deriv (fun t => (n * R * t) / P) T) *
  (deriv (fun p => (p * V) / (n * R)) P) = -1 := by
  sorry







theorem theorem_860697_problem :
  ∃ (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ) (D : Matrix (Fin m) (Fin m) ℝ),
    Matrix.det (Matrix.fromBlocks A B C D) ≠ 0 ∧ Matrix.det A = 0 := by
  sorry











theorem theorem_860800_problem (x y r : ℝ) (hr : r > 0) :
  ((x - 0) ^ 2 + (y - 0) ^ 2 = r ^ 2 + 1 ^ 2 ∧
   (x - 1) ^ 2 + (y - 0) ^ 2 = r ^ 2 + 2 ^ 2) ↔
  ∃ t : ℝ, t ≠ 0 ∧ x = -1 ∧ y = -1 / (2 * t) ∧ r = 1 / (2 * |t|) := by
  sorry

theorem theorem_860967_problem (n : ℕ) (C : ℝ) (x : Fin n → ℝ)
  (h_pos : 0 < n)
  (h_sym : ∀ i j : Fin n, x i = x j)
  (h_eq : ∀ i : Fin n, x i + ∑ j, x j = C) :
  ∀ i : Fin n, x i = C / (n + 1) := by
  sorry



theorem theorem_860242_problem (x : ℕ → ℝ)
  (h : ∀ n : ℕ, 1 ≤ n → x (n + 2) = 2 * x (n + 1) + (2 : ℝ)^n * (x 2 - 2 * x 1)) :
  ∃ A B : ℝ, ∀ n : ℕ, 1 ≤ n → x n = (A + B * (n : ℝ)) * (2 : ℝ)^n := by
  sorry

theorem theorem_860960_problem (K : Type*) [Field K] [IsAlgClosed K]
  (n : ℕ) (f : MvPolynomial (Fin n) K)
  (h : ∀ x : Fin n → K, MvPolynomial.eval x f = 0) :
  f = 0 := by
  sorry



theorem theorem_861579_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (g : V → ℝ)
  (A B C : V)
  (S : Set V)
  (hS_A : A ∈ S)
  (hS_B : B ∈ S)
  (hS_C : C ∈ S)
  (hC : C = (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B)
  (hgA : g A = 1)
  (hgB : g B = 1)
  (hgC : g C > 1) :
  ¬ ConvexOn ℝ S g := by
  sorry

theorem theorem_861289_problem
  (Ω : Type*)
  (C : Type*)
  [MeasurableSpace Ω]
  (P : MeasureTheory.Measure Ω)
  [MeasureTheory.IsProbabilityMeasure P]
  (Y : C → Ω → ℝ)
  (hY : ∀ γ, Measurable (Y γ))
  (F_Y : MeasurableSpace Ω)
  (h_FY : F_Y = ⨆ γ, MeasurableSpace.comap (Y γ) (borel ℝ)) :
  ∀ (F : Set Ω), @MeasurableSet Ω F_Y F →
  ∀ (ω₁ ω₂ : Ω), (∀ γ, Y γ ω₁ = Y γ ω₂) → (ω₁ ∈ F ↔ ω₂ ∈ F) := by
  sorry

theorem theorem_860951_problem (x : ℝ) (hx : 0 < x ∧ x < (1 : ℝ) / 4) :
  ∃ a b c : ℝ, (1 - Real.sqrt (1 - 4 * x)) / (2 * x) = a - b * Real.sqrt c := by
  sorry



theorem theorem_862161_problem (n : ℕ) (a b A B : ℤ)
  (hn : 0 < n)
  (h_gcd : Int.gcd b n = 1)
  (hA : A ≡ a [ZMOD n])
  (hB : B ≡ b [ZMOD n]) :
  (A : ZMod n) * (B : ZMod n)⁻¹ = (a : ZMod n) * (b : ZMod n)⁻¹ := by
  sorry





theorem theorem_861251_problem
  (n : ℕ) (hn : n > 1)
  (S : Type*) [Fintype S] [DecidableEq S]
  (f_neg f_zero f_pos : S → Fin (n + 1) → ℝ)
  (p : ℝ)
  (q : S → ℝ)
  (h_int_sum : ∀ (s : S) (i : Fin (n + 1)), 0 < i ∧ i < n → f_neg s i + f_zero s i + f_pos s i = 1)
  (h_q_sum : ∑ t, q t = 1) :
  let transition_prob : (Fin (n + 1) × S) → (Fin (n + 1) × S) → ℝ :=
    fun (state_i, s) (state_j, t) =>
      if h0 : state_i = 0 then
        if state_j = 0 ∧ t = s then 1 - p
        else if state_j = 1 then p * q t
        else 0
      else if hn : state_i = n then
        if state_j = n ∧ t = s then 1 - p
        else if state_j = n - 1 then p * q t
        else 0
      else
        if t = s then
          if state_j = state_i - 1 then f_neg s state_i
          else if state_j = state_i then f_zero s state_i
          else if state_j = state_i + 1 then f_pos s state_i
          else 0
        else 0
  ∀ x, ∑ y, transition_prob x y = 1 := by
  sorry

theorem theorem_861804_problem (X : Type*) (φ : X ≃ ℕ) : Countable (Finset X) := by
  sorry

theorem theorem_861498_problem (n : ℕ) (u : (Fin n → ℝ) → (Fin n → ℝ))
  (h_smooth : ContDiff ℝ 1 u) (x : Fin n → ℝ) :
  let div_tensor := fun i => ∑ j, fderiv ℝ (fun y => u y i * u y j) x (Pi.single j 1)
  let convective := fun i => ∑ j, u x j * fderiv ℝ (fun y => u y i) x (Pi.single j 1)
  let div_u := ∑ j, fderiv ℝ (fun y => u y j) x (Pi.single j 1)
  div_tensor = fun i => convective i + u x i * div_u := by
  sorry





theorem theorem_861981_problem
  (g : Set.Icc (0 : ℝ) 1 → ℝ)
  (hg : Continuous g)
  (X : Set (Set.Icc (0 : ℝ) 1))
  (hX : X = {x | g x = 0}) :
  IsClosed X := by
  sorry



theorem theorem_861491_problem (a : ℕ → ℝ)
  (h_rec : ∀ n, n ≥ 2 → a n = ((n : ℝ) + 1) / ((n : ℝ) - 1) * ∑ k in Finset.Icc 1 (n - 1), a k) :
  ∀ n, a n = (2 : ℝ) ^ n * ((n : ℝ) + 1) * a 0 := by
  sorry

theorem theorem_861876_problem 
  {A : Type*} 
  {X : A → Type*} [∀ a, TopologicalSpace (X a)] 
  {cX : A → Type*} [∀ a, TopologicalSpace (cX a)] 
  (i : ∀ a, X a → cX a) 
  (h_comp : ∀ a, CompactSpace (cX a)) 
  (h_emb : ∀ a, Embedding (i a)) 
  (h_dense : ∀ a, DenseRange (i a)) : 
  CompactSpace (∀ a, cX a) ∧ 
  Embedding (fun (x : ∀ a, X a) => fun a => i a (x a)) ∧ 
  DenseRange (fun (x : ∀ a, X a) => fun a => i a (x a)) := by
  sorry







theorem theorem_862377_problem
  (Sentence Formula : Type)
  (code : Sentence → ℕ)
  (subst : Formula → ℕ → Sentence)
  (is_true : Sentence → Prop)
  (neg : Formula → Formula)
  (h_neg : ∀ (φ : Formula) (n : ℕ), is_true (subst (neg φ) n) ↔ ¬ is_true (subst φ n))
  (h_diag : ∀ (φ : Formula), ∃ (G : Sentence), is_true G ↔ is_true (subst φ (code G))) :
  ¬ ∃ (T : Formula), ∀ (p : Sentence), is_true (subst T (code p)) ↔ is_true p := by
  sorry

theorem theorem_862352_problem {X : Type*} [TopologicalSpace X] (x : X) (N : Set X) :
  N ∈ nhds x ↔ ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ N := by
  sorry





theorem theorem_862791_problem
  {X E : Type*} [TopologicalSpace X] [MetricSpace E]
  (f : X → ℝ) (h : X → E)
  (α : E) (l : ℝ)
  (hf : Continuous f) (hh : Continuous h) :
  (∀ ε > 0, ∃ δ > 0, ∀ x : X, dist (h x) α < δ → dist (f x) l < ε) ↔
  (∀ ε > 0, ∃ δ > 0, h ⁻¹' (Metric.ball α δ) ⊆ f ⁻¹' (Metric.ball l ε)) := by
  sorry



theorem theorem_863253_problem (p : ℝ) (hp : 0 < p) :
  Summable (fun n : ℕ => if 2 ≤ n then 1 / ((n : ℝ) * (Real.log n) ^ p) else 0) ↔ 1 < p := by
  sorry



theorem theorem_863364_problem
  {k : Type*} [NontriviallyNormedField k]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace k X] [CompleteSpace X]
  {τ : Type*} [AddSemigroup τ]
  (T : τ → (X →L[k] X))
  (h_semi : ∀ t s : τ, T (t + s) = T t * T s) :
  ∀ A B : X →L[k] X, A ∈ Set.range T → B ∈ Set.range T → A * B ∈ Set.range T := by
  sorry









theorem theorem_863085_problem (p q m n : ℕ)
  (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
  (F1 : Type*) [Field F1] [Fintype F1] (h1 : Fintype.card F1 = p ^ m)
  (F2 : Type*) [Field F2] [Fintype F2] (h2 : Fintype.card F2 = q ^ n) :
  IsEmpty (F1 →+* F2) := by
  sorry

theorem theorem_863180_problem (x θ : ℝ) :
  (∑' n : ℕ, x ^ n / (n.factorial : ℝ) * Real.sin (n * θ)) = 
  Real.exp (x * Real.cos θ) * Real.sin (x * Real.sin θ) := by
  sorry







theorem theorem_863392_problem 
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (r A B : V) (b₁ b₂ : ℝ) 
  (h₁ : 0 < b₁) (h₂ : 0 < b₂) :
  Real.exp (-b₁ * ‖r - A‖^2) * Real.exp (-b₂ * ‖r - B‖^2) = 
  Real.exp (-(b₁ + b₂) * ‖r - (b₁ + b₂)⁻¹ • (b₁ • A + b₂ • B)‖^2) * 
  Real.exp (-(b₁ * b₂ * ‖A - B‖^2) / (b₁ + b₂)) := by
  sorry

theorem theorem_863711_problem (f : ℝ → ℝ)
  (hf : ContinuousOn f (Set.Icc 0 1)) :
  ∫ x in (0 : ℝ)..(1 : ℝ), x ^ (-(1 / 2 : ℝ)) * f x = ∫ s in (0 : ℝ)..(1 : ℝ), 2 * f (s ^ 2) := by
  sorry











theorem theorem_864095_problem
  (DefinableOrdinal : Ordinal → Prop)
  (DefinableSet : Set Ordinal → Prop)
  (O : Ordinal)
  (h_sup : ∀ S, DefinableSet S → DefinableOrdinal (sSup S))
  (h_succ : ∀ α, DefinableOrdinal α → DefinableOrdinal (α + 1))
  (h_O_def : DefinableOrdinal O)
  (h_O_max : ∀ α, DefinableOrdinal α → α ≤ O) :
  ∀ S, DefinableSet S → O ∉ S := by
  sorry



theorem theorem_864197_problem
  (a₁ a₂ w₁ w₂ x y : ℝ)
  (ha₁ : 0 < a₁)
  (ha₂ : 0 < a₂) :
  ((x - w₁) / a₁) ^ 2 + ((y - w₂) / a₂) ^ 2 = 1 / 4 ↔
  ∃ θ ∈ Set.Icc 0 (2 * Real.pi),
    x = w₁ + (a₁ / 2) * Real.cos θ ∧
    y = w₂ + (a₂ / 2) * Real.sin θ := by
  sorry

theorem theorem_864286_problem (n : ℕ) (g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
  (h : ∀ (x1 x2 y1 y2 : Fin n → ℝ) (s : ℝ), 0 ≤ s → s ≤ 1 →
    g (s • x1 + (1 - s) • x2, s • y1 + (1 - s) • y2) ≤ s * g (x1, y1) + (1 - s) * g (x2, y2)) :
  ConvexOn ℝ Set.univ g := by
  sorry



theorem theorem_864592_problem
  {Ω : Type*} [AddCommGroup Ω]
  (d_A : Ω →+ Ω)
  (F_A : Ω →+ Ω)
  (IsEllipticComplex : (Ω →+ Ω) → Prop)
  (h_elliptic_implies_complex : ∀ d, IsEllipticComplex d → d.comp d = 0)
  (h_da_sq_eq_fa : d_A.comp d_A = F_A)
  (h_fa_nonzero : F_A ≠ 0) :
  ¬ IsEllipticComplex d_A := by
  sorry

theorem theorem_864703_problem (θ : ℝ) :
  Real.cos (3 * θ) = 4 * (Real.cos θ)^3 - 3 * Real.cos θ := by
  sorry

theorem theorem_864607_problem (a b : ℝ) (h : ℝ → ℝ) (f : ℝ → ℝ) (x : ℝ)
  (hab : a ≤ b)
  (h_cont : ContinuousOn h (Set.Icc a b))
  (hf : ∀ y, f y = ∫ t in a..y, h t)
  (hx : x ∈ Set.Icc a b) :
  HasDerivWithinAt f (h x) (Set.Icc a b) x := by
  sorry



theorem theorem_864838_problem (b : ℕ → ℝ)
  (h_nonneg : ∀ n, 0 ≤ b n)
  (h_eventually_decreasing : ∃ N, ∀ n ≥ N, b (n + 1) ≤ b n)
  (h_limit : Filter.Tendsto b Filter.atTop (nhds 0)) :
  Summable (fun n ↦ (-1 : ℝ)^n * b n) := by
  sorry



