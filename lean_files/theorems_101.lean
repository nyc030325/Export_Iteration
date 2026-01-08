import Mathlib
import Mathlib.Tactic

theorem theorem_543681_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (b : OrthonormalBasis (Fin 2) ℝ V)
  (T : V →ₗ[ℝ] V)
  (h : LinearMap.toMatrix b.toBasis b.toBasis T = !![2, 1; 1, 2]) :
  LinearMap.IsSymmetric T := by
  sorry

theorem theorem_544378_problem {V : Type*} [Fintype V] (n : ℕ)
  (T : SimpleGraph V) [DecidableRel T.Adj]
  (h_card : Fintype.card V = n)
  (h_n : n ≥ 1)
  (h_tree : T.IsTree) :
  T.edgeFinset.card = n - 1 := by
  sorry

theorem theorem_544292_problem (a x : ℝ) (h1 : 0 < a) (h2 : a ≠ 1) :
  HasDerivAt (fun t => Real.arctan (a ^ t) / Real.log a) (a ^ x / (1 + a ^ (2 * x))) x := by
  sorry

theorem theorem_543975_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  (S : Set (X →L[𝕜] X))
  (h : Dense S) :
  closure S = Set.univ := by
  sorry

theorem theorem_543751_problem
  (n : ℕ)
  (a b : Fin n → ℝ)
  (D : Set (Fin n → ℝ))
  (hD_compact : IsCompact D)
  (hD_nonempty : D.Nonempty)
  (f : (Fin n → ℝ) → ℝ)
  (hf : ∀ x, f x = - Matrix.dotProduct (Matrix.mulVec (Matrix.diagonal x) (a + b)) (Matrix.mulVec (Matrix.diagonal x) (a + b))) :
  ∃ x_star ∈ D, ∀ x ∈ D, f x_star ≤ f x := by
  sorry

theorem theorem_543403_problem (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
  ¬ ∃ (Y : Type*) (hY₁ : NormedAddCommGroup Y) (hY₂ : NormedSpace ℝ Y) (hY₃ : CompleteSpace Y),
    Nonempty (C(X, ℝ) ≃L[ℝ] NormedSpace.Dual ℝ Y) := by
  sorry





theorem theorem_543969_problem (α : ℝ) (A B C : Matrix (Fin 2) (Fin 2) ℝ)
  (hA : A = !![0, α; 1, 0])
  (hB : B = !![-(1/2), 0; 0, 1/2])
  (hC : C = !![0, -α; 1, 0]) :
  B * C - C * B = A := by
  sorry







theorem theorem_543917_problem
  (m n k : ℕ)
  (A : Matrix (Fin m) (Fin n) ℕ)
  (b : Fin m → ℕ)
  (hA : ∀ i j, A i j ≤ 1)
  (hb : ∀ i, b i ≤ 1) :
  ∀ x : Fin n → ℕ,
    (
      -- Definition of Minimum Tiling:
      -- 1. S is entirely covered (Ax ≥ b)
      (∀ i, (Matrix.mulVec A x) i ≥ b i) ∧
      -- 2. Variables are within defined bounds
      (∀ j, x j ≤ k) ∧
      -- 3. Minimizes the total number of polyominoes used
      (∀ y : Fin n → ℕ, (∀ i, (Matrix.mulVec A y) i ≥ b i) → (∀ j, y j ≤ k) → ∑ j, x j ≤ ∑ j, y j)
    ) ↔
    (
      -- Formulation as Integer Programming Problem:
      -- Subject to Ax ≥ b
      (∀ i, (Matrix.mulVec A x) i ≥ b i) ∧
      -- Subject to x_i ∈ {0, ..., k}
      (∀ j, x j ≤ k) ∧
      -- Minimize ∑ x_i
      (∀ y : Fin n → ℕ, (∀ i, (Matrix.mulVec A y) i ≥ b i) ∧ (∀ j, y j ≤ k) → ∑ j, x j ≤ ∑ j, y j)
    ) := by
  sorry



theorem theorem_544105_problem (j : ℕ) (hj : 2 ≤ j ∧ j ≤ 11) :
  let balls : ℕ → ℕ := λ k => 12 - k
  let total_balls : ℕ := 66
  let prob_worst_team_second_given_j_first : ℚ := (balls 1 : ℚ) / (total_balls - balls j)
  prob_worst_team_second_given_j_first = 11 / (54 + (j : ℚ)) := by
  sorry

theorem theorem_544272_problem (a b : ℝ) (f : ℝ → ℝ)
  (hab : a ≤ b)
  (hf : ContDiffOn ℝ 1 f (Set.Icc a b)) :
  let x : ℝ → ℝ := fun θ ↦ f θ * Real.cos θ
  let y : ℝ → ℝ := fun θ ↦ f θ * Real.sin θ
  ∫ θ in a..b, Real.sqrt ((deriv x θ)^2 + (deriv y θ)^2) = 
  ∫ θ in a..b, Real.sqrt ((deriv f θ)^2 + (f θ)^2) := by
  sorry







theorem theorem_544748_problem
  (Ω : Type*)
  (W : ℕ → Ω → ℝ)
  (hW : ∀ ω k, W k ω < W (k + 1) ω)
  (k : ℕ) (hk : k ≠ 0)
  (t : ℝ) (ht : t ≠ 0) :
  {ω | W (k + 1) ω ≤ t} ⊆ {ω | W k ω < t} := by
  sorry

theorem theorem_544944_problem (P Q : Prop) (h1 : Q → P) (h2 : Q) : P := by
  sorry





theorem theorem_544996_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : ℕ} (hn : 0 < n)
  (v : Fin n → V)
  (h_indep : LinearIndependent K v) :
  let u := Fin.cons (v ⟨0, hn⟩) v
  ¬ LinearIndependent K u := by
  sorry



theorem theorem_544234_problem (m n : ℕ)
  (H : AddSubgroup (ZMod (m * n)))
  (hH : H = AddSubgroup.closure { (n : ZMod (m * n)) }) :
  Nonempty ((ZMod (m * n) ⧸ H) ≃+ ZMod n) := by
  sorry





theorem theorem_545241_problem (G : Type*) [Group G] (x₁ x₂ x₃ : G)
  (h1 : x₂ * x₁ * x₂⁻¹ = x₁ ^ 2)
  (h2 : x₃ * x₂ * x₃⁻¹ = x₂ ^ 2)
  (h3 : x₁ * x₃ * x₁⁻¹ = x₃ ^ 2) :
  x₁ = 1 ∧ x₂ = 1 ∧ x₃ = 1 := by
  sorry

theorem theorem_545448_problem 
  (K L M : Type*) [Field K] [Field L] [Field M]
  (i : K →+* L) (j : K →+* M) (φ : L →+* M)
  (h_compat : ∀ k, φ (i k) = j k) :
  ∀ (k : K) (l : L), φ (i k * l) = j k * φ l := by
  sorry



theorem theorem_545328_problem {α : Type*} (k n : ℕ) (S : Fin k → Language α) :
  (∑ i : Fin k, S i) ^ n = ∑ p : Fin n → Fin k, (List.ofFn (S ∘ p)).prod := by
  sorry

theorem theorem_545346_problem
  {Formula : Type*}
  (derives : Set Formula → Formula → Prop)
  (valid : Formula → Prop)
  (equiv : Formula → Formula → Formula)
  (Γ : Set Formula)
  (ψ φ : Formula)
  (h1 : derives Γ ψ)
  (h2 : valid (equiv ψ φ)) :
  derives Γ φ := by
  sorry

theorem theorem_545613_problem (n : ℕ) (h : n ≥ 1) :
  let walks := {f : Fin (2 * n + 1) → ℤ | f 0 = 0 ∧ ∀ i : Fin (2 * n), |f i.succ - f i.castSucc| = 1}
  let valid_walks := {f ∈ walks | f (Fin.last (2 * n)) = 0 ∧ ∀ k : Fin (2 * n + 1), k ≠ 0 → k ≠ Fin.last (2 * n) → f k ≠ 0}
  (valid_walks.ncard : ℝ) / (2 ^ (2 * n) : ℝ) = (Nat.choose (2 * n) n : ℝ) / ((2 ^ (2 * n) : ℝ) * (2 * n - 1 : ℝ)) := by
  sorry





theorem theorem_545911_problem (n : ℕ)
  (lam : Fin n → ℝ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : A.IsSymm)
  (t₁ t₂ : ℝ)
  (h_denom : ∀ i j, lam i + lam j ≠ 0)
  (I_mat : Matrix (Fin n) (Fin n) ℝ)
  (hI : ∀ i j, I_mat i j = A i j * ∫ t in t₁..t₂, Real.exp ((lam i + lam j) * t)) :
  ∀ i j, I_mat i j = A i j * ((Real.exp ((lam i + lam j) * t₂) - Real.exp ((lam i + lam j) * t₁)) / (lam i + lam j)) := by
  sorry

theorem theorem_545648_problem (G : Type*) [Group G] :
  ∃ φ : G →* Equiv.Perm G, Function.Injective φ ∧ ∀ (g x : G), φ g x = g * x := by
  sorry

theorem theorem_546155_problem (z : ℂ) (hz : z ≠ 1)
  (h : (z + 1) ^ 100 = (z - 1) ^ 100) :
  ∃ k : ℤ, (z + 1) / (z - 1) = Complex.exp ((2 * ↑Real.pi * ↑k * Complex.I) / 100) := by
  sorry



theorem theorem_546322_problem (f : ℝ → ℝ)
  (h_cont : Continuous f)
  (h_lim_neg : Filter.Tendsto f Filter.atBot Filter.atBot)
  (h_lim_pos : Filter.Tendsto f Filter.atTop Filter.atTop) :
  ∃ c : ℝ, f c = 0 := by
  sorry

theorem theorem_546134_problem (m k : ℕ) (p : ℕ → ℕ)
  (hm : m > 1)
  -- p represents the sequence of primes greater than m
  (hp_prime : ∀ n, (p n).Prime)
  (hp_gt : ∀ n, m < p n)
  (hp_mono : StrictMono p)
  (hp_surj : ∀ q, q.Prime → m < q → ∃ n, p n = q) :
  ∑ i in Finset.range k, Real.log (p i) =
    (k : ℝ) * Real.log m + ((k : ℝ) ^ 2 / (2 * (m : ℝ))) * Real.log m := by
  sorry

theorem theorem_546639_problem
  {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (f : X → Y) (g : Y → Z)
  (hf : Continuous f) (hg : Continuous g) :
  Continuous (g ∘ f) := by
  sorry

theorem theorem_546280_problem
  (K : Type*) [NormedField K] [CompleteSpace K]
  (X : Type*) [TopologicalSpace X]
  -- We represent the sheaf and the compatibility condition as abstract types/predicates
  -- to capture the exact conditions without needing the specific sheaf implementation details.
  (Sheaf : Type*)
  (is_standard_pullback : Sheaf → (n : ℕ) → (U : Set X) → (V : Set (Fin n → K)) → (U → V) → Prop)
  (h_main : ∃ F : Sheaf, ∀ x : X, ∃ (n : ℕ) (U : Set X) (V : Set (Fin n → K)) (h : U → V),
    x ∈ U ∧ IsOpen U ∧ IsOpen V ∧ IsLocalHomeomorph h ∧ is_standard_pullback F n U V h) :
  -- Conclusion: X is a topological manifold (locally homeomorphic to K^n)
  ∀ x : X, ∃ (n : ℕ) (U : Set X) (V : Set (Fin n → K)),
    x ∈ U ∧ IsOpen U ∧ IsOpen V ∧ Nonempty (U ≃ₜ V) := by
  sorry





theorem theorem_546648_problem
  {X : Type*} [MetricSpace X]
  (f : X → ℝ)
  (h1 : Continuous f)
  (h2 : ∀ (x : ℕ → X) (a : X), Filter.Tendsto x Filter.atTop (nhds a) →
    Filter.Tendsto (f ∘ x) Filter.atTop (nhds (f a))) :
  UniformContinuous f ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → |f x - f y| < ε := by
  sorry

theorem theorem_545779_problem
  {G H : Type*} [Group G] [Group H]
  (θ : G → H)
  (h_ab : ∀ a b : G, a * b = b * a)
  (h_cond : ∀ a b : G, θ a * θ b = θ (a * b)) :
  ∀ a b : G, θ (a * b) = θ a * θ b := by
  sorry

theorem theorem_546448_problem
  (n : ℕ)
  (X : Matrix (Fin n) (Fin n) ℝ)
  (v : Matrix (Fin n) (Fin 1) ℝ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hX : X.IsSymm) :
  let M := Matrix.fromBlocks X v v.transpose (!![1] : Matrix (Fin 1) (Fin 1) ℝ)
  (M.PosSemidef ∧ X.PosSemidef) ↔ (X - v * v.transpose).PosSemidef := by
  sorry



theorem theorem_545993_problem (m : ℕ) (hm : m ≥ 3) :
  let S := Finset.Icc 1 m
  let outcomes := (S ×ˢ S ×ˢ S).filter (fun x => x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ x.2.1 ≠ x.2.2)
  let favorable := outcomes.filter (fun x => 
    (x.1 + x.2.1 + x.2.2 : ℚ) < (3 : ℚ) * (max x.1 (max x.2.1 x.2.2)) / 2)
  (favorable.card : ℚ) / outcomes.card = 
    (3 : ℚ) / (m ^ 2 * (m - 1)) * 
    ∑ i in Finset.Ico 1 (m / 2), 
      ∑ j in (Finset.Ico 1 (m / 2 - i)).filter (· ≠ i), 
        ((m : ℚ) - 2 * i - 2 * j) := by
  sorry

theorem theorem_546405_problem
  (f : ℕ → ℕ × ℕ)
  (hf : Function.Bijective f)
  (a b : ℕ) :
  ∃ t : ℕ, a + t * b = (f t).1 + t * (f t).2 := by
  sorry







theorem theorem_546437_problem (y : ℝ → ℝ)
  (h_analytic : AnalyticOn ℝ y Set.univ)
  (h_init : y 0 = 1)
  (h_derivs : ∀ n : ℕ, 1 ≤ n → iteratedDeriv n y 0 = 0) :
  ∀ x, y x = 1 := by
  sorry





theorem theorem_547551_problem (a b c x : ℝ)
  (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
  a * x^2 + b * x + c = a * (x + b / (2 * a))^2 - (b^2 - 4 * a * c) / (4 * a) := by
  sorry

theorem theorem_547599_problem : ¬ ∃ (U : ZFSet), ∀ (x : ZFSet), x ∈ U := by
  sorry

theorem theorem_547960_problem (p : ℕ) [Fact p.Prime] :
  Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  sorry

theorem theorem_547875_problem
  {X : Type*} [MetricSpace X] [CompleteSpace X]
  (U : ℕ → Set X)
  (h_open : ∀ n, IsOpen (U n))
  (h_dense : ∀ n, Dense (U n)) :
  Dense (⋂ n, U n) := by
  sorry







theorem theorem_547703_problem {α : Type*} (A B : α → Prop)
  (f : ∀ x, A x → B x) (g : ∀ x, A x) :
  ∀ x, B x := by
  sorry













theorem theorem_548138_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (N a_dag : H →L[ℂ] H)
  (psi : ℕ → H)
  (h_eigen : ∀ ν : ℕ, N (psi ν) = (ν : ℂ) • psi ν)
  (h_comm : N * a_dag - a_dag * N = a_dag) :
  ∀ ν : ℕ, N (a_dag (psi ν)) = ((ν : ℂ) + 1) • (a_dag (psi ν)) := by
  sorry



theorem theorem_547391_problem
  {U : Type*} [LinearOrder U] [IsWellOrder U (· < ·)]
  (L : Set (Set U)) :
  ∃! (r : (⋃₀ L) → (⋃₀ L) → Prop),
    IsStrictTotalOrder (⋃₀ L) r ∧
    ∀ (x y : ⋃₀ L), r x y ↔ (x : U) < (y : U) := by
  sorry



theorem theorem_548150_problem (a x : ℝ) (ha : a > 0) :
  HasDerivAt (fun x => 1 / (2 * a^3) * Real.arctan (x / a) + x / (2 * a^2 * (x^2 + a^2)))
    (1 / (x^2 + a^2)^2) x := by
  sorry



theorem theorem_548458_problem (a b : ℝ) (ha : a > 0) (hb : b > 0)
  (t₁ t₂ : ℝ)
  (h_range₁ : 0 ≤ t₁ ∧ t₁ < 2 * Real.pi)
  (h_range₂ : 0 ≤ t₂ ∧ t₂ < 2 * Real.pi)
  (h_distinct : t₁ ≠ t₂)
  (h_parallel : (-a * Real.sin t₁) * (b * Real.cos t₂) = (b * Real.cos t₁) * (-a * Real.sin t₂)) :
  |t₁ - t₂| = Real.pi := by
  sorry





theorem theorem_548235_problem (y : ℝ → ℝ) :
  (ContDiff ℝ 2 y ∧ ∀ x, deriv (deriv y) x - 4 * deriv y x + 5 * y x = Real.exp (-x)) ↔
  (∃ c₁ c₂ : ℝ, ∀ x, y x = (c₁ * Real.cos x + c₂ * Real.sin x) * Real.exp (2 * x) + Real.exp (-x) / 10) := by
  sorry



theorem theorem_548013_problem (n : ℕ) (h : n ≥ 3) :
  ∃ C : ℕ, (6 ∣ n → C = 3) ∧
           (2 ∣ n ∧ ¬ 6 ∣ n → C = 4) ∧
           (¬ 2 ∣ n → C = 6) := by
  sorry

theorem theorem_548860_problem (y : ℝ → ℝ)
  (h : ∀ x, deriv (deriv y) x - 4 * deriv y x + 5 * y x = 4 * Real.exp (2 * x) * Real.cos x) :
  ∃ C₁ C₂ : ℝ, ∀ x, y x = C₁ * Real.exp (2 * x) * Real.cos x + C₂ * Real.exp (2 * x) * Real.sin x + 2 * x * Real.exp (2 * x) * Real.sin x := by
  sorry



theorem theorem_548626_problem 
  {Formula : Type*}
  (derives : Set Formula → Formula → Prop)
  (imp : Formula → Formula → Formula)
  (A : Set Formula)
  (φ χ : Formula)
  (h : derives (insert φ A) χ) :
  derives A (imp φ χ) := by
  sorry























theorem theorem_549555_problem (t : ℕ) (h : t > 0) :
  ∑ b in Finset.Ico 1 t, (Nat.choose t b) * 2^(t - b) = 3^t - 2^t - 1 := by
  sorry



