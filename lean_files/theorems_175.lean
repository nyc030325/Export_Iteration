import Mathlib
import Mathlib.Tactic

theorem theorem_960115_problem (n m : ℕ) (hn : n > 0) :
  ∫ x in Set.Icc (0 : ℝ) 1, x ^ m * (1 - x) ^ (n - 1) =
  ((n - 1).factorial * m.factorial : ℝ) / (m + n).factorial := by
  sorry

theorem theorem_959981_problem (f : ℕ → ℕ → ℕ) (x : ℕ) :
  f x x ∈ (Set.univ : Set ℕ) := by
  sorry

theorem theorem_960040_problem (n k : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
  Fintype.card (Sym (Fin n) k) = Nat.choose (n + k - 1) k := by
  sorry





theorem theorem_960129_problem (n : ℕ) (hn : n > 0)
  (seq : ℕ → ℕ)
  (h_seq_binary : ∀ k < n, seq k ∈ ({0, 1} : Set ℕ))
  (h_seq_leading : seq 0 = 1)
  (i : ℕ)
  (h_i : i = ∑ k in Finset.range n, seq k * 10^(n - 1 - k))
  (X : Set ℕ)
  (h_X : X = { x | (∃ a : ℕ, x = i / 10^a) ∧ x ≠ 0 }) :
  X = { x | ∃ k < n, x = i / 10^k } := by
  sorry

theorem theorem_960391_problem (n : ℕ) (hn : 2 ≤ n) :
  ∃ (a : ℕ → ℝ → ℂ),
    (∀ k, Continuous (a k)) ∧
    (∀ t, a n t ≠ 0) ∧
    ¬ ∃ (r : Fin n → ℝ → ℂ),
      (∀ i, Continuous (r i)) ∧
      ∀ (t : ℝ) (z : ℂ),
        (∑ k in Finset.range (n + 1), a k t * z ^ k) =
        a n t * ∏ i, (z - r i t) := by
  sorry





theorem theorem_961185_problem {G : Type*} [Group G] (x : G) (a b : ℤ) :
  x ^ (a + b) = x ^ a * x ^ b := by
  sorry







theorem theorem_960917_problem
  (X : Type*) [TopologicalSpace X]
  (n : ℕ)
  (D : Type*) [TopologicalSpace D]
  (S : Set (Fin n → X))
  (hS : IsClosed S)
  (Φ : D → (Fin n → X))
  (hΦ : Continuous Φ) :
  IsClosed (Φ ⁻¹' S) := by
  sorry





theorem theorem_961720_problem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (p : Module.End K V)
  (h₁ : p ^ 2 = p)
  (h₂ : IsUnit (1 - p)) :
  p = 0 := by
  sorry



theorem theorem_961297_problem (f g : ℝ → ℝ)
  (hf : Filter.Tendsto f Filter.atTop Filter.atTop)
  (hg : Filter.Tendsto g Filter.atTop Filter.atTop) :
  Filter.Tendsto (fun x ↦ f x * g x) Filter.atTop Filter.atTop := by
  sorry

theorem theorem_960986_problem (k : ℕ) (y : ℝ) (h : |y| < 1) :
  ∑' n : ℕ, (Nat.choose n k : ℝ) * y ^ n = y ^ k / (1 - y) ^ (k + 1) := by
  sorry

theorem theorem_961602_problem
  {k : Type*} [Field k]
  {V : Type*} [AddCommGroup V] [Module k V]
  {W : Type*} [AddCommGroup W] [Module k W]
  (φ : V →ₗ[k] W)
  (f : W →ₗ[k] k) :
  IsLinearMap k (f ∘ φ) := by
  sorry

theorem theorem_961528_problem (G : Type*) [Group G] (G₁ : Subgroup G) (h : G₁.Normal) :
  (G₁ : Set G) ∪ Set.univ = Set.univ := by
  sorry

theorem theorem_961272_problem
  (p : ℕ) (hp : p.Prime)
  (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = p)
  (g : G) (hg : Subgroup.zpowers g = ⊤)
  (k : ℤ) :
  orderOf (g ^ k) = p / p.gcd k.natAbs := by
  sorry













theorem theorem_961570_problem (S : ℕ → ℝ)
  (hS : ∀ n, S n = ∑ k in Finset.Icc 1 n, (k : ℝ)^2) :
  Asymptotics.IsEquivalent Filter.atTop S (fun n => (1 / 3 : ℝ) * (n : ℝ)^3) := by
  sorry

theorem theorem_961831_problem (m b : ℝ) :
  (∃ T : ℝ, T ≠ 0 ∧ ∀ x : ℝ, ∃ k1 k2 : ℤ,
    x + T = x + (k1 : ℝ) ∧ m * (x + T) + b = m * x + b + (k2 : ℝ)) ↔
  ∃ q : ℚ, m = q := by
  sorry

theorem theorem_961793_problem {α : Type} (x y : Set α) 
  (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  sorry



theorem theorem_961630_problem (x y z : ℕ) (h : (x, y, z) ≠ (0, 0, 0)) :
  ∃! p : ℕ × ℕ × ℕ × ℕ,
    let n := p.1
    let a := p.2.1
    let b := p.2.2.1
    let c := p.2.2.2
    n > 0 ∧ Nat.gcd a (Nat.gcd b c) = 1 ∧
    x = n * a ∧ y = n * b ∧ z = n * c := by
  sorry

theorem theorem_961849_problem
  (Y : Type*) [TopologicalSpace Y]
  (f : Set.Ioo (0 : ℝ) 1 → Y)
  (g : Set.Ioo (1 : ℝ) 2 → Y)
  (h : (Set.Ioo (0 : ℝ) 1 ∪ Set.Ioo (1 : ℝ) 2 : Set ℝ) → Y)
  (hf : Continuous f)
  (hg : Continuous g)
  (h_eq_f : ∀ x : Set.Ioo (0 : ℝ) 1, h ⟨x.1, Or.inl x.2⟩ = f x)
  (h_eq_g : ∀ x : Set.Ioo (1 : ℝ) 2, h ⟨x.1, Or.inr x.2⟩ = g x) :
  Continuous h := by
  sorry











theorem theorem_962296_problem 
  -- Setup: Local chart context with vector spaces E (coords) and F (tensor components)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- T represents the tensor field components as a function of coordinates
  (T : E → F)
  (hT : ContDiff ℝ ⊤ T) -- Smoothness condition
  -- Γ represents the connection coefficients (Christoffel symbols) acting on a point, direction, and tensor value
  (Γ : E → E →L[ℝ] F →L[ℝ] F)
  -- ∇ represents the covariant derivative operator
  (nabla : (E → F) → E → (E →L[ℝ] F))
  -- Definition: The covariant derivative is the partial derivative plus the connection term
  (h_nabla_def : ∀ (A : E → F) (x : E) (v : E), nabla A x v = fderiv ℝ A x v + (Γ x v) (A x))
  -- Condition: The connection is flat (Christoffel symbols vanish)
  (h_flat : ∀ x, Γ x = 0) :
  -- Conclusion: The components of the new tensor field (covariant derivative) are just the partial derivatives
  ∀ x, nabla T x = fderiv ℝ T x := by
  sorry

theorem theorem_962256_problem
  {α : Type*} [LinearOrder α] [IsWellOrder α (· < ·)]
  (φ : α → Prop)
  (h : ∀ x, (∀ y, y < x → φ y) → φ x) :
  ∀ x, φ x := by
  sorry







theorem theorem_962527_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  (a b : ℝ) (f : ℝ → V)
  (hf : ContDiffOn ℝ 1 f (Set.Icc a b)) :
  ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, |h| < δ → h ≠ 0 →
    ∀ t ∈ Set.Icc a b, t + h ∈ Set.Icc a b →
      ‖(h⁻¹ • (f (t + h) - f t)) - deriv f t‖ < ε := by
  sorry

theorem theorem_962044_problem
  (R T M : Type*) [Ring R] [Ring T] [AddCommGroup M]
  [Module Rᵐᵒᵖ M] [Module T M] [SMulCommClass T Rᵐᵒᵖ M]
  (k : ℕ)
  (S : Fin k → Submodule Rᵐᵒᵖ M)
  (h_simple : ∀ i, IsSimpleModule Rᵐᵒᵖ (S i))
  (h_iso : ∀ i j, Nonempty ((S i) ≃ₗ[Rᵐᵒᵖ] (S j))) :
  ∃ U : Submodule T M, (U : Set M) = (⨆ i, S i).carrier ∧ IsSimpleModule T U := by
  sorry



theorem theorem_962230_problem (a b c : ℕ → ℝ)
  (h : PowerSeries.mk (fun n => c n / (n.factorial : ℝ)) =
       PowerSeries.mk (fun n => a n / (n.factorial : ℝ)) *
       PowerSeries.mk (fun n => b n / (n.factorial : ℝ))) :
  ∀ n, c n = ∑ k in Finset.range (n + 1), (n.choose k : ℝ) * a k * b (n - k) := by
  sorry



theorem theorem_962977_problem :
  ¬ ∃ y : ℝ, y > 0 ∧ ∀ a b d : ℝ, a > 0 → b > 0 → d > 0 → a / (b + d) ≥ y * (a / b) := by
  sorry

theorem theorem_963119_problem
  {K : Type*} [Field K]
  {n : ℕ}
  (A B : Matrix (Fin n) (Fin n) K)
  (h : A * B = 0) :
  A.rank + B.rank ≤ n := by
  sorry















theorem theorem_963842_problem (f : ℝ → ℝ) (h : ∀ x, f x = Real.exp (- (x ^ 2))) :
  deriv f = fun x => -2 * x * Real.exp (- (x ^ 2)) := by
  sorry

theorem theorem_963375_problem
  {R : Type*} [CommRing R]
  {V : Type*} [AddCommGroup V] [Module R V] [LieRing V]
  (k : ℕ)
  (X : Fin k → V)
  (D : Submodule R V)
  (hD : D = Submodule.span R (Set.range X))
  (IsIntegrable : Submodule R V → Prop) :
  IsIntegrable D ↔ ∀ i j, ⁅X i, X j⁆ ∈ D := by
  sorry



theorem theorem_963633_problem
  {K : Type*} [LinearOrderedField K]
  (S : Set K)
  (hS : S = { n : K | ∃ m : ℕ, n = m })
  (h_cond : ∃ x : K, x ∉ S ∧ ∀ n ∈ S, x > n) :
  ¬ ∃ u : K, IsLUB S u := by
  sorry







theorem theorem_963846_problem : Cardinal.mk ℝ = Cardinal.mk (Set ℚ) := by
  sorry

















theorem theorem_964634_problem (T U : Matrix (Fin 2) (Fin 2) ℝ)
  (hT : T = !![0, 1; 1, 0])
  (hU : U = !![1, 0; 0, -1]) :
  T * U = -(U * T) := by
  sorry

theorem theorem_964671_problem (p : ℝ) :
  ¬ Summable (fun n : ℕ => (Real.log ((n : ℝ) + 1) / Real.log ((n : ℝ) + 1)) ^ p) := by
  sorry



theorem theorem_965011_problem (a b : ℝ) (f : ℝ → ℝ)
  (h_ab : a < b)
  (h_mono : Monotone f)
  (h_range : Set.range f ⊆ Set.Icc 0 1)
  (h_supp_lo : ∀ x < a, f x = 0)
  (h_supp_hi : ∀ x > b, f x = 1) :
  let is_flat_region := fun c d ↦ Set.Icc c d ⊆ Set.Icc a b ∧ c < d ∧ ∀ x ∈ Set.Icc c d, f x = f c
  let is_maximal_flat_region := fun c d ↦ is_flat_region c d ∧ 
    ∀ c' d', is_flat_region c' d' → Set.Icc c d ⊆ Set.Icc c' d' → c = c' ∧ d = d'
  { s : Set ℝ | ∃ c d, s = Set.Icc c d ∧ is_maximal_flat_region c d }.Countable := by
  sorry

theorem theorem_965004_problem
  (h : ℝ → ℝ)
  (H : ℝ → ℝ)
  (hH : ∀ x, H x = if x ≥ 0 then 1 else 0)
  (a b : ℝ)
  (hab : a ≤ b)
  (f : ℝ → ℝ)
  (hf : ∀ x, f x = H (x - a) * H (b - x) * h x) :
  ∀ x, f x = if x ∈ Set.Icc a b then h x else 0 := by
  sorry





theorem theorem_965182_problem (P Q : Prop) (f : P → Q) : P → Q := by
  sorry

theorem theorem_965650_problem
  (n : ℕ) (hn : 0 < n)
  (X : Type*) [TopologicalSpace X]
  (f : ℂ → X) (hf : Continuous f)
  (p : (Fin n → ℂ) → ℂ) (hp : p = fun z => z ⟨0, hn⟩)
  (f_hat : (Fin n → ℂ) → X) (hf_hat : f_hat = fun z => f (p z)) :
  Continuous f_hat := by
  sorry

theorem theorem_965508_problem
  {M : Type*}
  (dcl : Set M → Set M)
  (Cb : M → M → Set M → Set M)
  (a b : M)
  (C : Set M)
  (h : a ∈ dcl (C ∪ {b})) :
  a ∈ dcl (Cb a b C ∪ {b}) := by
  sorry





theorem theorem_965300_problem (n : ℕ) (hn : 0 < n) (X : Fin n → Type*)
  (h : ∀ i, Nonempty (X i ≃ ℕ)) :
  Nonempty (((i : Fin n) → X i) ≃ ℕ) := by
  sorry



theorem theorem_965894_problem
  {M : Type*} [MetricSpace M]
  {K : Type*} [Group K] [MulAction K M] [IsometricSMul K M]
  (p : M)
  (r : ℝ) (hr : 0 < r)
  -- K is the isotropy subgroup at p
  (h_iso : ∀ k : K, k • p = p)
  -- K acts transitively on the distance shells within the geodesic ball
  (h_trans : ∀ q₁ q₂ : M, dist p q₁ < r → dist p q₂ < r → dist p q₁ = dist p q₂ → ∃ k : K, k • q₁ = q₂)
  (f : M → ℝ)
  -- f is invariant under the action of K
  (h_inv : ∀ (k : K) (q : M), f (k • q) = f q) :
  -- f depends only on the distance from p (radial function)
  ∃ g : ℝ → ℝ, ∀ q : M, dist p q < r → f q = g (dist p q) := by
  sorry



theorem theorem_965753_problem
  (A : Type*) [CommRing A] [IsDomain A]
  (p : Ideal A) [p.IsPrime] :
  Nonempty (FractionRing (Localization.AtPrime p) ≃+* FractionRing A) := by
  sorry









theorem theorem_966696_problem
  {n : ℕ} {M : Type*} [TopologicalSpace M] [ConnectedSpace M]
  (u : M → ℝ) (R : M → ℝ) (Δ : (M → ℝ) → (M → ℝ))
  (h_n : n > 2)
  (h_eq : ∀ x, -((4 * (n - 1 : ℝ)) / (n - 2 : ℝ)) * Δ u x + R x * u x = 0)
  (h_R : ∀ x, 0 ≤ R x)
  (h_lim : Filter.Tendsto u (Filter.cocompact M) (nhds 1))
  (h_not_const : ¬ ∃ c, u = Function.const M c) :
  ∀ x, 0 < u x ∧ u x < 1 := by
  sorry

theorem theorem_966255_problem
  {R : Type*} [CommRing R]
  (r : ℕ) (hr : 1 < r)
  (x : ℕ → R)
  (h_distinct : ∀ i ∈ Finset.Icc 1 r, ∀ j ∈ Finset.Icc 1 r, i ≠ j → x i ≠ x j) :
  (∑ i in Finset.Icc 1 r, (-1 : R)^(i - 1) *
    (∏ k in Finset.Icc 1 r, ∏ l in Finset.Icc 1 r,
      if k < l ∧ k ≠ i ∧ l ≠ i then (x k - x l) else 1)) = 0 := by
  sorry





