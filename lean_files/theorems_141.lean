import Mathlib
import Mathlib.Tactic





theorem theorem_765530_problem
  (p q : ℝ)
  (e0 e1 e2 : ℝ)
  (hp_pos : 0 < p)
  (hp_lt_one : p < 1)
  (hq : q = 1 - p)
  (h_e0 : e0 = 1 + p * e1 + q * e0)
  (h_e1 : e1 = 1 + p * e2 + q * e0)
  (h_e2 : e2 = 1 + q * e0) :
  e0 = (1 + p + p^2) / (1 - q * (1 + p + p^2)) := by
  sorry





theorem theorem_766238_problem (p : ℝ) (S : ℝ) (eta : ℝ → ℝ)
  (hp : 0 < p)
  (hS : S = ∑' k : ℕ+, ((-1 : ℝ) ^ (k : ℕ)) / (((k : ℕ) : ℝ) ^ (1 / p)))
  (heta : ∀ s : ℝ, eta s = ∑' n : ℕ+, ((-1 : ℝ) ^ ((n : ℕ) - 1)) / (((n : ℕ) : ℝ) ^ s)) :
  S = - eta (1 / p) := by
  sorry





theorem theorem_766502_problem
  (K : Type*)
  (P : K → ℝ → K → ℝ → K → ℝ → K → ℝ → ℝ)
  (k1 k4 : K)
  (t1 t4 : ℝ)
  (h_ord : t1 < t4)
  (h_supp : ∀ k2 k3 t2 t3, ¬ (t1 < t2 ∧ t2 < t3 ∧ t3 < t4) → P k1 t1 k2 t2 k3 t3 k4 t4 = 0) :
  (∑' (k2 : K) (k3 : K), ∫ t3, ∫ t2, P k1 t1 k2 t2 k3 t3 k4 t4) =
  (∑' (k2 : K) (k3 : K), ∫ t3 in t1..t4, ∫ t2 in t1..t3, P k1 t1 k2 t2 k3 t3 k4 t4) := by
  sorry





theorem theorem_766291_problem (n : ℕ) :
  ∫ θ in (0 : ℝ)..(2 * Real.pi), (1 - Real.sin θ ^ 2) ^ n =
  ∑ k in Finset.range (n + 1), (Nat.choose n k : ℝ) * (-1) ^ k *
    ((Nat.factorial (2 * k) : ℝ) * Real.pi) /
    ((Nat.factorial k : ℝ) ^ 2 * (2 : ℝ) ^ ((2 * k : ℤ) - 1)) := by
  sorry



theorem theorem_766215_problem
  (f : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ)
  (hU : IsOpen U)
  (hz₀ : z₀ ∈ U)
  (hf : DifferentiableOn ℂ f U) :
  ∃ R > 0, Metric.ball z₀ R ⊆ U ∧
  ∀ z ∈ Metric.ball z₀ R, HasSum (fun n : ℕ => (iteratedDeriv n f z₀) / (n.factorial : ℂ) * (z - z₀) ^ n) (f z) := by
  sorry





theorem theorem_766277_problem 
  {α : Type} 
  (mem : α → α → Prop) 
  (h_reg : ∀ x : α, ¬ mem x x) 
  (P : α → Prop) 
  (S_P : α) 
  (h_SP : ∀ x : α, mem x S_P ↔ P x) : 
  ¬ P S_P := by
  sorry

theorem theorem_766196_problem (n : ℕ)
  (T : (Fin n → ℝ) ≃ₜ (Fin n → ℝ))
  (E : Set (Fin n → ℝ))
  (hE : @MeasurableSet (Fin n → ℝ) (borel (Fin n → ℝ)) E) :
  @MeasurableSet (Fin n → ℝ) (borel (Fin n → ℝ)) (T '' E) := by
  sorry



theorem theorem_766916_problem (x : ℤ → ℂ) (ω : ℝ)
  (h_roc : Summable (fun n => x n * (Complex.exp (Complex.I * (ω : ℂ))) ^ (-n))) :
  ∑' n, x n * Complex.exp (-Complex.I * (ω : ℂ) * (n : ℂ)) = 
  ∑' n, x n * (Complex.exp (Complex.I * (ω : ℂ))) ^ (-n) := by
  sorry



















theorem theorem_766931_problem
  (a b : ℝ)
  (f : ℝ → ℝ → ℝ)
  (hab : a ≤ b)
  (hf : Continuous (Function.uncurry f)) :
  ∫ x₁ in a..b, ∫ t in a..x₁, f t x₁ = ∫ t in a..b, ∫ x₁ in t..b, f t x₁ := by
  sorry



theorem theorem_767736_problem {X : Type*} [TopologicalSpace X] (E : Set X) :
  ¬ IsPreconnected (Set.univ : Set E) ↔
  ∃ (U V : Set E), U.Nonempty ∧ V.Nonempty ∧ IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = Set.univ := by
  sorry







theorem theorem_767214_problem (α β : ℝ) (hαβ : α ≤ β)
  (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
  (h_equicontinuous : ∀ ε > 0, ∃ δ > 0, ∀ n : ℕ, ∀ x ∈ Set.Icc α β, ∀ y ∈ Set.Icc α β,
    |x - y| < δ → |fn n x - fn n y| < ε)
  (h_pointwise : ∀ x ∈ Set.Icc α β, Filter.Tendsto (fun n ↦ fn n x) Filter.atTop (nhds (f x))) :
  TendstoUniformlyOn fn f Filter.atTop (Set.Icc α β) := by
  sorry







theorem theorem_767567_problem (x : ℝ → ℝ) (t dt : ℝ)
  (h : DifferentiableAt ℝ x t) :
  fderiv ℝ x t dt = deriv x t * dt := by
  sorry









theorem theorem_766007_problem (m k u t D : ℤ)
  (hm : m ≠ 0) (hk : k ≠ 0) (hu : u ≠ 0)
  (hD : D / 4 ≡ 0 [ZMOD 4])
  (heq : m * k = u^2 - (D / 4) * t^2)
  (hodd : Odd (m * k)) :
  m * k ≡ 1 [ZMOD 16] ∨ m * k ≡ 9 [ZMOD 16] := by
  sorry



theorem theorem_767366_problem 
  (S : ℕ → Set ℝ)
  (h1 : S 1 = {2})
  (h_rec : ∀ n, 1 < n → S n = ⋃ k ∈ Finset.Icc 1 (n - 1), 
    {z | ∃ x ∈ S k, ∃ y ∈ S (n - k), 
      z = x + y ∨ z = x - y ∨ z = x * y ∨ (y ≠ 0 ∧ z = x / y)}) :
  ∃ K : ℝ, K > 0 ∧ Filter.Tendsto (fun n ↦ ((S n).ncard : ℝ) ^ (1 / n : ℝ)) Filter.atTop (nhds K) := by
  sorry



theorem theorem_768410_problem (p q : ℕ) 
  (hp : Nat.Prime p) (hq : Nat.Prime q) (h_distinct : p ≠ q) :
  ¬ ∃ k : ℕ, p^2 + p * q = k^2 := by
  sorry

theorem theorem_768277_problem
  {S : Type*} [Fintype S] [DecidableEq S]
  (P : Matrix S S ℝ)
  (y : S)
  (x : S)
  -- Condition: P is a transition matrix (entries are probabilities)
  (hP_nonneg : ∀ i j, 0 ≤ P i j)
  (hP_sum : ∀ i, ∑ j, P i j = 1)
  -- Definition: Q(x,z) = P(x,z)1_B(z) where B = S \ {y}
  (Q : Matrix S S ℝ)
  (hQ : ∀ i j, Q i j = P i j * if j ≠ y then 1 else 0)
  -- Definition: ρ_xy is the hitting probability.
  -- We formalize the "hitting probability" via its decomposition into first hitting times
  -- as described in the standard derivation of this formula.
  (first_hit_prob : ℕ → S → ℝ)
  (h_hit_0 : ∀ u, first_hit_prob 0 u = P u y)
  (h_hit_succ : ∀ n u, first_hit_prob (n + 1) u = ∑ z, Q u z * first_hit_prob n z)
  (ρ_xy : ℝ)
  (hρ : ρ_xy = ∑' n, first_hit_prob n x) :
  -- Question: Prove the formula for ρ_xy
  ρ_xy = ∑' n, (Q ^ n * P) x y := by
  sorry

theorem theorem_767888_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (x y : H)
  (h_eq : ‖x‖ = ‖y‖)
  (h_pos : 0 < ‖x‖) :
  ∃ u : H →L[ℂ] H, u ∈ unitary (H →L[ℂ] H) ∧ (star u) x = y := by
  sorry

theorem theorem_768465_problem (S : Set ℝ) :
  Dense S ↔ ∀ a b : ℝ, a < b → ∃ x ∈ S, x ∈ Set.Ioo a b := by
  sorry

theorem theorem_768101_problem (x₀ y₀ z₀ v₁ v₂ v₃ : ℝ)
  (h_surface : x₀^2 + y₀^2 - z₀^2 = -1)
  (h_tangent : 2 * x₀ * v₁ + 2 * y₀ * v₂ - 2 * z₀ * v₃ = 0)
  (h_nonzero : v₁ ≠ 0 ∨ v₂ ≠ 0 ∨ v₃ ≠ 0) :
  v₁^2 + v₂^2 - v₃^2 > 0 := by
  sorry

theorem theorem_768448_problem (a : ℕ → ℝ) (L : ℝ)
  (h : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε) :
  Filter.Tendsto a Filter.atTop (nhds L) := by
  sorry

theorem theorem_768574_problem
  {Index : Type*} [Fintype Index]
  {Term : Type*}
  (occurrences : Term → Index → ℕ)
  (is_well_defined : Term → Prop)
  -- Condition from the problem text: In a well-defined summation,
  -- an index appears at most twice.
  (h_rule : ∀ (t : Term), is_well_defined t → ∀ (i : Index), occurrences t i ≤ 2)
  -- Specific instance hypothesis: An index appears more than twice
  (t : Term) (i : Index) (h_gt : occurrences t i > 2) :
  -- Conclusion: The summation is not well-defined
  ¬ is_well_defined t := by
  sorry

theorem theorem_768338_problem (f : ℝ → ℝ)
  (h1 : ∀ x y : ℝ, f (y + f x) = f x * f (y * f x))
  (h2 : ∀ x : ℝ, f x ≠ 0) :
  ∀ x : ℝ, f x = 1 := by
  sorry



theorem theorem_767934_problem (a : ℕ → ℕ → ℝ)
  (h1 : ∀ i, Summable (fun j ↦ ‖a i j‖))
  (h2 : ∃ b : ℕ → ℝ, (∀ i j, ‖a i j‖ ≤ b i) ∧ Summable b)
  (h3 : ∀ j, Summable (fun i ↦ a i j)) :
  (∑' i, ∑' j, a i j) = (∑' j, ∑' i, a i j) := by
  sorry

theorem theorem_768643_problem {X : Type*} [TopologicalSpace X] (A : Set X) :
  IsCompact A ↔
  (∀ (ι : Type*) (u : ι → Set X), (∀ i, IsOpen (u i)) → A ⊆ ⋃ i, u i →
    ∃ s : Finset ι, A ⊆ ⋃ i ∈ s, u i) := by
  sorry





theorem theorem_768690_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (u v : X) :
  ‖u + v‖^2 ≤ 2 * ‖u‖^2 + 2 * ‖v‖^2 := by
  sorry

theorem theorem_768501_problem (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosure ℚ K] :
  ¬ Countable (AlgEquiv ℚ K K) := by
  sorry



theorem theorem_768746_problem 
  (k₁ k₂ k₃ k₄ : ℝ)
  (c₁ c₂ c₃ c₄ : EuclideanSpace ℝ (Fin 2))
  (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃) (hk₄ : 0 < k₄)
  (h₁₂ : dist c₁ c₂ = 1 / k₁ + 1 / k₂)
  (h₁₃ : dist c₁ c₃ = 1 / k₁ + 1 / k₃)
  (h₂₃ : dist c₂ c₃ = 1 / k₂ + 1 / k₃)
  (h₄₁ : dist c₄ c₁ = 1 / k₄ + 1 / k₁)
  (h₄₂ : dist c₄ c₂ = 1 / k₄ + 1 / k₂)
  (h₄₃ : dist c₄ c₃ = 1 / k₄ + 1 / k₃) :
  (k₁ + k₂ + k₃ + k₄)^2 = 2 * (k₁^2 + k₂^2 + k₃^2 + k₄^2) := by
  sorry

theorem theorem_768853_problem.{u} (S : Type u) [LinearOrder S] [IsWellOrder S LT.lt]
  (P : S → Prop) (T : Set S) (hT : T = { x | P x }) :
  ∃ A : Set Ordinal.{u}, ∀ α, α ∈ A ↔ ∃ x : S, Ordinal.typein LT.lt x = α := by
  sorry

theorem theorem_769096_problem (n : ℕ) (hn : n ≥ 2)
  (a : ℕ → ℂ)
  (h_roots : (Finset.Icc 1 n).val.map a = (X ^ n - 1 : Polynomial ℂ).roots)
  (h_one : a 1 = 1) :
  ∏ i in Finset.Icc 2 n, (1 - a i) = n := by
  sorry



theorem theorem_769067_problem
  {X : Type*} [MetricSpace X]
  (A : Set X)
  (hA : IsConnected A) :
  IsConnected (closure A) := by
  sorry

theorem theorem_769492_problem 
  (c : ℕ → ℂ) 
  (t ε : ℝ) 
  (ht : 0 < t) 
  (hε : 0 < ε) 
  (h_bound : ∃ N, ∀ n ≥ N, Complex.abs (c n) ≤ (t + ε) ^ n) 
  (z : ℂ) 
  (hz : Complex.abs z < 1 / (t + ε)) : 
  Summable (fun n ↦ Complex.abs (c n * z ^ n)) := by
  sorry



theorem theorem_769498_problem (a : ℕ → ℝ)
  (h : ∀ k, a k = Real.sqrt (k + 1) / 2 ^ k) :
  Summable a := by
  sorry

theorem theorem_769579_problem {α : Type u} (r : α → α → Prop) [IsWellOrder α r]
  (h_singleton : Cardinal.mk α = 1) :
  Ordinal.type r = 1 := by
  sorry



theorem theorem_769257_problem :
  TendstoUniformlyOn
    (fun (N : ℕ) (x : ℝ) => ∑ n in Finset.range N, (x * (1 - x)) ^ n)
    (fun (x : ℝ) => ∑' n : ℕ, (x * (1 - x)) ^ n)
    Filter.atTop
    (Set.Ioo 0 1) := by
  sorry

theorem theorem_768579_problem (G H : Type*) [Group G] [Group H]
  (K : Subgroup G) (φ : G →* H) :
  ∀ g ∈ MonoidHom.ker φ, (fun k => g * k) '' (K : Set G) = (fun k => k * g) '' (K : Set G) := by
  sorry





theorem theorem_769287_problem (n : ℕ) (d : ℕ) (k : Fin d → ℕ)
  (hd : d ≥ 1)
  (h_sum : ∑ i, k i = n) :
  n.factorial / (∏ i, (k i).factorial) ≥ 1 := by
  sorry









theorem theorem_769683_problem (a b z : ℂ)
  (h1 : a ≠ z) (h2 : b ≠ z)
  (h3 : b - a ≠ 0)
  (h4 : Complex.abs (z - a) < Complex.abs (b - a)) :
  1 / (z - b) = - (1 / (b - a)) * ∑' n : ℕ, ((z - a) / (b - a)) ^ n := by
  sorry



theorem theorem_770434_problem (n : ℕ) (S : Type*) [Fintype S]
  (h_card : Fintype.card S = n)
  (h : {k : ℕ // 1 ≤ k ∧ k ≤ n} → S)
  (h_bij : Function.Bijective h)
  (hn : 1 ≤ n)
  (H : ℕ → S)
  (hH_le : ∀ k, (hk : 1 ≤ k ∧ k ≤ n) → H k = h ⟨k, hk⟩)
  (hH_gt : ∀ k, n < k → H k = h ⟨1, ⟨le_refl 1, hn⟩⟩) :
  Function.Surjective H := by
  sorry





theorem theorem_770198_problem
  (Div : Type*) [AddCommGroup Div]
  (K : Div)
  (l s : Div → ℤ)
  (inter : Div → Div → ℤ)
  (pa : ℤ)
  (chi : Div → ℚ)
  (h_serre_def : ∀ D : Div, chi D = (l D : ℚ) - (s D : ℚ) + (l (K - D) : ℚ))
  (h_hrr : ∀ D : Div, chi D = 1 + (pa : ℚ) + (1 / 2 : ℚ) * (inter D (D - K) : ℚ))
  (D : Div) :
  (l D : ℚ) - (s D : ℚ) + (l (K - D) : ℚ) = (1 / 2 : ℚ) * (inter D (D - K) : ℚ) + 1 + (pa : ℚ) := by
  sorry

theorem theorem_770675_problem {X : Type*} [MetricSpace X] (A : Set X) (hA : IsOpen A) :
  ∀ a ∈ A, ∃ ε > 0, Metric.ball a ε ⊆ A := by
  sorry





theorem theorem_770692_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {n : ℕ} (U : Fin n → Submodule F V)
  (h_span : iSup U = ⊤) :
  DirectSum.IsInternal U ↔ ∀ i, U i ⊓ (⨆ (j) (_ : j ≠ i), U j) = ⊥ := by
  sorry









theorem theorem_771476_problem (n : ℕ) (hn : n ≥ 1) :
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 1]
  let v_init : Matrix (Fin 2) (Fin 1) ℤ := !![0; 1]
  let v_n : Matrix (Fin 2) (Fin 1) ℤ := !![((Nat.fib (n - 1)) : ℤ); ((Nat.fib n) : ℤ)]
  v_n = A ^ (n - 1) * v_init := by
  sorry





