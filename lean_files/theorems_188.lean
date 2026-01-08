import Mathlib
import Mathlib.Tactic





theorem theorem_1039734_problem 
  (Knot : Type)
  (crossing_number : Knot → ℕ)
  (alexander_polynomial : Knot → Polynomial ℤ)
  (D : ℕ → ℕ)
  (hD : ∀ n, D n = Set.ncard (alexander_polynomial '' {k | crossing_number k = n})) :
  ∀ n : ℕ, 1 ≤ n → D n ≤ D (n + 1) := by
  sorry



theorem theorem_1040565_problem (m n a b : ℝ)
  (hm : 0 < m) (hn : 0 < n) (ha : 0 < a) (hb : 0 < b)
  (h : m^2 * n^2 > a^2 / m^(-2 : ℤ) + b^2 / n^(-2 : ℤ)) :
  m^2 + n^2 > (a + b)^2 := by
  sorry



theorem theorem_1041281_problem 
  (a b x₀ : ℝ) 
  (c : ℕ → ℝ) 
  (f : ℝ → ℝ) 
  (h_cont : ContinuousOn f (Set.Icc a b))
  (h_unif : TendstoUniformlyOn (fun N x ↦ ∑ n in Finset.range (N + 1), c n * (x - x₀) ^ n) f Filter.atTop (Set.Icc a b))
  (h_summable : Summable (fun n ↦ c n * ∫ x in a..b, (x - x₀) ^ n)) : 
  ∫ x in a..b, f x = ∑' n, c n * ∫ x in a..b, (x - x₀) ^ n := by
  sorry



theorem theorem_1041619_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (A B : Matrix n n ℝ)
  (hA : A.PosDef)
  (hB : B.PosDef) :
  ∀ (x : ℂ), x ∈ ((A * B).charpoly.map (algebraMap ℝ ℂ)).roots → 0 < x.re := by
  sorry





theorem theorem_1041018_problem
  (p n : ℕ)
  (t : ℤ)
  (hp : Nat.Prime p)
  (hodd : Odd p)
  (hn : n > 0)
  (h : t ^ p ≡ 1 [ZMOD (p ^ (n + 1))]) :
  t ≡ 1 [ZMOD (p ^ n)] := by
  sorry















theorem theorem_1041707_problem (v : ℝ) (l : ℝ → ℝ) (f : ℝ → ℝ)
  (hl : Differentiable ℝ l)
  (hf : Differentiable ℝ f)
  (h : ∀ t, deriv l t = v) :
  ∀ t, deriv (f ∘ l) t = v * deriv f (l t) := by
  sorry

theorem theorem_1041620_problem
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (h : (n = 1 ∧ A ≠ 0) ∨ n > 1) :
  ∃ X : Matrix (Fin n) (Fin n) ℝ, (A * X * A.transpose).diag = 0 := by
  sorry

theorem theorem_1041443_problem (x : ℝ) (h : x > 0) (C : ℝ) :
  HasDerivAt (fun t => t^2 / 2 - 2 * t ^ ((3 : ℝ) / 2) / 3 + C) 
  ((x^2 - x) / (x + Real.sqrt x)) x := by
  sorry



theorem theorem_1041572_problem (n m : ℕ) (h_nm : n ≥ m) :
  let A : Matrix (Fin n) (Fin n) ℚ := Matrix.diagonal (fun i => if (i : ℕ) < m then 1 else 0)
  A.rank = m := by
  sorry



theorem theorem_1042225_problem
  (k m : ℕ)
  (n : ℕ → ℕ)
  (c : ℕ → ℝ)
  (f : ℕ → ℝ)
  (x : Fin m → ℕ)
  (h_n_mono : Monotone n)
  (h_f : ∀ (i : ℕ) (val : ℕ), 1 ≤ i ∧ i ≤ k → n (i - 1) < val ∧ val ≤ n i → f val = c i)
  (shipping_cost : Fin m → ℝ)
  (h_cost_def : ∀ j, shipping_cost j = f (x j)) :
  ∑ j : Fin m, shipping_cost j = ∑ j : Fin m, f (x j) := by
  sorry



theorem theorem_1041894_problem (r₀ : ℝ) (P : ℝ → ℕ → ℝ) (f : ℕ → ℝ)
  (hP_nonneg : ∀ r > r₀, ∀ n, 0 ≤ P r n)
  (h_bound : ∀ r > r₀, ∀ n, P r n ≤ f n)
  (h_lim : Filter.Tendsto f Filter.atTop (nhds 0)) :
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ r > r₀, P r n < ε := by
  sorry



theorem theorem_1042057_problem
  (H : AddSubgroup (ℤ × ℤ × ℤ))
  (hH : ∀ x : ℤ × ℤ × ℤ, x ∈ H ↔ x.2.2 = 0)
  (φ : H →+ ℤ)
  (hφ : ∀ (m n : ℤ) (h : (m, n, 0) ∈ H), φ ⟨(m, n, 0), h⟩ = m)
  (T : AddSubgroup H)
  (hT : T = AddMonoidHom.ker φ) :
  Nonempty (H ⧸ T ≃+ ℤ) := by
  sorry

theorem theorem_1043103_problem
  (a b : ℕ → ℝ)
  (ha : ∀ n, a n = 1 + Real.log 5 / n)
  (hb : ∀ n, b n = n) :
  Filter.Tendsto (fun n ↦ (a n) ^ (b n)) Filter.atTop (nhds 5) := by
  sorry

theorem theorem_1041908_problem
  (X : Type*) [TopologicalSpace X]
  (X_seq : ℕ → Set X)
  (h_seq_closed : ∀ i, IsClosed (X_seq i))
  (A B : Set X)
  (hA : IsClosed A)
  (hB : IsClosed B)
  (hAB : IsClosed (A ∪ B))
  (f₀ : C(↥(A ∪ B), unitInterval)) :
  ∃ f : C(X, unitInterval),
    (∀ x : ↥(A ∪ B), f x = f₀ x) ∧
    (∀ i, Continuous ((f : X → unitInterval) ∘ (Subtype.val : ↥(X_seq i) → X))) := by
  sorry

theorem theorem_1042969_problem
  (F : Type*) [Field F]
  (U₁ U₂ : Type*) [AddCommGroup U₁] [Module F U₁] [AddCommGroup U₂] [Module F U₂]
  (i₁ : U₁ →ₗ[F] U₁ × U₂ := LinearMap.inl F U₁ U₂)
  (i₂ : U₂ →ₗ[F] U₁ × U₂ := LinearMap.inr F U₁ U₂)
  (T : Module.Dual F (U₁ × U₂) → (Module.Dual F U₁) × (Module.Dual F U₂))
  (hT : ∀ f, T f = (LinearMap.comp f i₁, LinearMap.comp f i₂)) :
  ∃ E : (Module.Dual F (U₁ × U₂)) ≃ₗ[F] (Module.Dual F U₁) × (Module.Dual F U₂), E.toFun = T := by
  sorry





theorem theorem_1042570_problem
  {R : Type*} [CommRing R]
  {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation R Γ)
  (f₁ f₂ g : R)
  (hg_unit : IsUnit g)
  (hg_val : v g = 1)
  (h_trans : f₁ = f₂ * g) :
  v f₁ = v f₂ := by
  sorry

theorem theorem_1042032_problem :
  ∃ (k : ℝ), k > 0 ∧
  ∃ (x₀ : ℝ), ∀ x ≥ x₀,
  ∃ (p p' : ℕ),
    Nat.Prime p ∧ Nat.Prime p' ∧
    p < p' ∧ (∀ q, Nat.Prime q → p < q → p' ≤ q) ∧
    (p : ℝ) ≥ x ∧
    (p' : ℝ) - p ≤ Real.exp (-0.75) * (Real.log x) ^ k := by
  sorry









theorem theorem_1043042_problem
  (E B F : Type*)
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
  (proj : E → B)
  (hB_comp : CompactSpace B)
  (hB_t2 : T2Space B)
  (hF_comp : CompactSpace F)
  (h_cont : Continuous proj)
  (h_local_trivial : ∀ b : B, ∃ U : Set B, IsOpen U ∧ b ∈ U ∧
    ∃ (φ : proj ⁻¹' U ≃ₜ U × F), ∀ x : proj ⁻¹' U, (φ x).1.val = proj x.val) :
  CompactSpace E := by
  sorry











theorem theorem_1043662_problem (k : ℕ) (hk : k > 0) :
  (k.factorial : ℝ) / (k : ℝ) ^ k > Real.exp (-(k : ℝ)) := by
  sorry

theorem theorem_1043430_problem (n f s d : ℕ)
  (h_s : s ≤ f)
  (h_d : d ≤ n) :
  let Arrow := Σ (S : { S : Finset (Fin n) // S.card = d }), ({ x // x ∉ S.val } → Fin (f - s))
  Fintype.card Arrow = Nat.choose n d * (f - s) ^ (n - d) := by
  sorry



theorem theorem_1043752_problem
  (R : Type*) [Ring R]
  (M : Type*) [AddCommGroup M] [Module R M]
  (I : Type*) [Nonempty I]
  (Ms : I → Submodule R M)
  (h : ∀ i j, ∃ k, (Ms i : Set M) ∪ (Ms j : Set M) ⊆ (Ms k : Set M)) :
  ∃ N : Submodule R M, (N : Set M) = ⋃ i, (Ms i : Set M) := by
  sorry







theorem theorem_1044118_problem (k : ℝ) (z : ℂ) (hk : 0 < k) :
  ((Real.sqrt k : ℂ) * z + 0) / (0 + (1 / Real.sqrt k : ℂ)) = (k : ℂ) * z := by
  sorry

theorem theorem_1044361_problem
  (li Ei : ℝ → ℝ)
  (x : ℝ)
  (hx_pos : 0 < x)
  (hx_ne_one : x ≠ 1)
  (h_li : ∀ t, 0 < t → t ≠ 1 → HasDerivAt li (1 / Real.log t) t)
  (h_Ei : ∀ z, z ≠ 0 → HasDerivAt Ei (Real.exp z / z) z) :
  HasDerivAt (fun t => t * li t - Ei (2 * Real.log t)) (li x) x := by
  sorry













theorem theorem_1042641_problem
  (m : ℕ)
  (S : Type*) [Fintype S] [DecidableEq S]
  (S₁ : Finset S) :
  (Fintype.card {f : S₁ → Fin m → Bool // ∀ x, Monotone (f x)} : ℝ) /
  (Fintype.card (S₁ → Fin m → Bool) : ℝ) =
  ((m + 1 : ℝ) / (2 : ℝ) ^ m) ^ S₁.card := by
  sorry







theorem theorem_1044464_problem
  (G : Type*) [Group G]
  (Unstable : Prop)
  (φ : G → G → Prop)
  (h : ∃ (a : ℕ → G) (p : G),
    (∀ (s : Finset ℕ), ∀ i ∈ s, φ p (a i)) ∧
    ¬ (∀ i, φ p (a i))) :
  Unstable := by
  sorry

theorem theorem_1044705_problem
  (a b : ℕ → ℝ)
  (x₀ : ℝ)
  (I : Set ℝ)
  (hx₀ : x₀ ≠ 0)
  (hI_open : IsOpen I)
  (hx₀_in : x₀ ∈ I)
  (ha_conv : ∀ x ∈ I, Summable (fun n ↦ a (n + 1) * x ^ (n + 1)))
  (hb_conv : ∀ x ∈ I, Summable (fun n ↦ b (n + 1) * x ^ (n + 1)))
  (h_eq : ∀ x ∈ I, (∑' n, a (n + 1) * x ^ (n + 1)) = (∑' n, b (n + 1) * x ^ (n + 1))) :
  ∀ n, a (n + 1) = b (n + 1) := by
  sorry

theorem theorem_1045078_problem (f : ℝ → ℝ) (L P : ℝ)
  (h_period : ∀ x : ℝ, f (x + L) = f x)
  (h_rel : L = P / 2) :
  ∀ x : ℝ, f (x + P) = f x := by
  sorry



theorem theorem_1044508_problem (x : ℝ) (h : -1 < x ∧ x < 1) :
  deriv (fun x => 1 / 4 * (-2 * x / (x^2 - 1) - Real.log (1 - x) + Real.log (x + 1))) x = 
  1 / (x^2 - 1)^2 := by
  sorry





theorem theorem_1045245_problem
  {E : Type*}
  (f : ℕ → E → ℝ)
  (u : ℕ → ℝ)
  (h_nonneg : ∀ n, 0 ≤ u n)
  (h_bound : ∀ n x, |f n x| ≤ u n)
  (h_sum : Summable u) :
  TendstoUniformly (fun N x ↦ ∑ n in Finset.range N, f n x) (fun x ↦ ∑' n, f n x) atTop := by
  sorry

theorem theorem_1045575_problem (p : ℕ) (hp : p > 0) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p)
  (a : ℤ) (ha : ζ ^ a ≠ 1) :
  (ζ ^ (a * p) - 1) / (ζ ^ a - 1) = 0 := by
  sorry

theorem theorem_1045533_problem 
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (ψ : H)
  (L M : H →L[ℂ] H)
  (pl : ℝ := ‖L ψ‖^2)
  (pm : ℝ := ‖M ψ‖^2)
  (plm : ℝ := ‖M (L ψ)‖^2)
  (h_nonzero : pl ≠ 0)
  (h_indep : plm / pl = pm) :
  plm = pl * pm := by
  sorry

theorem theorem_1045968_problem
  (X Y : Type*) [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
  (f : X × Y → ℝ) :
  (⨅ p : X × Y, f p) = ⨅ x : X, ⨅ y : Y, f (x, y) := by
  sorry





theorem theorem_1046151_problem (δ : ℝ) (hδ : 0 < δ) :
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ≥ δ, |Real.arctan ((n : ℝ) * x) - Real.pi / 2| < ε := by
  sorry

theorem theorem_1046433_problem
  (X : Type*)
  (C D : Set (Set X))
  (h : ∀ s ∈ C, @MeasurableSet X (MeasurableSpace.generateFrom D) s) :
  MeasurableSpace.generateFrom C ≤ MeasurableSpace.generateFrom D := by
  sorry







theorem theorem_1046436_problem
  (I P : Type*)
  [Fintype I] [Fintype P]
  [DecidableEq I] [DecidableEq P]
  (d : I → ℕ)
  (a : I → P → ℕ)
  (x : P → ℕ)
  (r : I → ℕ)
  (h : ∀ i, (∑ p, a i p * x p) + r i = d i) :
  (∑ i, r i) + (∑ i, ∑ p, a i p * x p) = ∑ i, d i := by
  sorry

theorem theorem_1046061_problem
  (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  (n : ℕ) (F : Fin n → Set X)
  (h_closed : ∀ i, IsClosed (F i))
  (h_union_compact : IsCompact (⋃ i, F i)) :
  ∀ i, IsCompact (F i) := by
  sorry

theorem theorem_1045735_problem 
  (f : ℂ → ℂ) (γ : ℝ → ℂ) (F : ℂ → ℂ) (n : ℤ)
  -- L represents the "local contributions from f(z)"
  (L : ℂ)
  (hL : L = F (γ (2 * π)) - F (γ 0))
  -- S represents the cumulative jump (sum of discontinuities F(t+) - F(t-))
  (S : ℂ)
  -- Hypothesis: n positive crossings implies the sum of jumps is -n(2πi)
  -- (Standard branch cut: value drops by 2πi when crossing positive real axis from below)
  (hS : S = - n * (2 * π * I))
  -- Hypothesis: The integral equals the total change minus the sum of jumps
  -- (Generalized Fundamental Theorem of Calculus for piecewise analytic functions)
  (h_ftc : ∫ t in (0:ℝ)..(2 * π), f (γ t) * (deriv γ t) = L - S) :
  ∫ t in (0:ℝ)..(2 * π), f (γ t) * (deriv γ t) = L + n * (2 * π * I) := by
  sorry

theorem theorem_1046497_problem (M : Type*) [MetricSpace M] :
  CompactSpace M ↔
  (∀ (ι : Type*) (U : ι → Set M), (∀ i, IsOpen (U i)) → (Set.univ ⊆ ⋃ i, U i) →
    ∃ s : Finset ι, Set.univ ⊆ ⋃ i ∈ s, U i) := by
  sorry

theorem theorem_1046796_problem (f : ℝ → ℝ → ℝ)
  (h_diff_y : ∀ x, Differentiable ℝ (fun y ↦ f x y))
  (h_diff_yx : ∀ y, Differentiable ℝ (fun x ↦ deriv (fun y ↦ f x y) y))
  (h_pde : ∀ x y, deriv (fun x ↦ deriv (fun y ↦ f x y) y) x = 1) :
  ∃ G h : ℝ → ℝ, ∀ x y, f x y = x * y + G y + h x := by
  sorry





theorem theorem_1045642_problem (ξ : ℝ) :
  ∫ x : ℝ, Complex.exp (-2 * ↑π * I * ↑x * ↑ξ) / Complex.cosh (↑π * ↑x) =
  1 / Complex.cosh (↑π * ↑ξ) := by
  sorry





theorem theorem_1047146_problem (x : ℝ) : ∃ n : ℕ, (n : ℝ) > x := by
  sorry



theorem theorem_1046409_problem
  (A : Type*) [Ring A]
  (n : ℕ)
  (a : Fin n → Ideal A)
  (h_mutual_disjointness : ∀ i j : Fin n, i ≠ j → a i ⊓ a j = ⊥)
  (h_sum_covers : iSup a = ⊤) :
  DirectSum.IsInternal a := by
  sorry



theorem theorem_1047456_problem {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y) (K : Set X)
  (h_cont : Continuous f)
  (h_comp : IsCompact K) :
  IsCompact (f '' K) := by
  sorry

theorem theorem_1047293_problem
  (U : Set ℝ) (hU : IsOpen U)
  (f : ℝ → (Fin 3 → ℝ))
  (hf : ContDiffOn ℝ ⊤ f U)
  (t : ℝ) (ht : t ∈ U)
  (v : ℝ) :
  (fderiv ℝ f t) v = v • (deriv f t) := by
  sorry

