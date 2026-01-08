import Mathlib
import Mathlib.Tactic



theorem theorem_837465_problem (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (S : Set X)
  (h_discrete : DiscreteTopology S)
  (h_closed : IsClosed S) :
  S.Finite := by
  sorry







theorem theorem_837673_problem (n : ℕ) (a b x : ℝ) (f : ℝ → ℝ)
  (hab : a < b)
  (hf : ContDiffOn ℝ (n + 1) f (Set.Icc a b))
  (hx : x ∈ Set.Ioc a b) :
  ∃ c ∈ Set.Ioo a x,
    f x - (∑ k in Finset.range (n + 1), (iteratedDeriv k f a) / (k.factorial : ℝ) * (x - a) ^ k) =
    (iteratedDeriv (n + 1) f c) / ((n + 1).factorial : ℝ) * (x - a) ^ (n + 1) := by
  sorry

theorem theorem_838064_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (S : ℕ → X →L[𝕜] X)
  (T : X →L[𝕜] X)
  (h : Filter.Tendsto (fun m => ‖S m - T‖) Filter.atTop (nhds 0)) :
  ∀ x : X, Filter.Tendsto (fun m => ‖(S m) x - T x‖) Filter.atTop (nhds 0) := by
  sorry















theorem theorem_838073_problem (N Delta : ℕ)
  (hN : 0 < N)
  (hDelta : 0 < Delta)
  (h_cond : (N : ℝ) > 3 * (Delta : ℝ) * Real.logb 2 (Delta : ℝ)) :
  N ^ Delta < 2 ^ N := by
  sorry

theorem theorem_838053_problem (f : ℝ → ℝ)
  (h : ∀ α, 0 < α → f α = ∫ u in Set.Ioi (0 : ℝ), Real.exp (-α * u ^ 2)) :
  deriv (deriv f) 1 = ∫ u in Set.Ioi (0 : ℝ), u ^ 4 * Real.exp (-u ^ 2) := by
  sorry





theorem theorem_838212_problem (f g : ℝ → ℝ) (x : ℝ)
  (hf : DifferentiableAt ℝ f x)
  (hg : DifferentiableAt ℝ g x) :
  deriv (f * g) x = deriv f x * g x + f x * deriv g x := by
  sorry

theorem theorem_838308_problem
  (k : ℕ)
  (p : Fin k → ℕ)
  (hp : ∀ i, Nat.Prime (p i))
  (h_distinct : Function.Injective p)
  (n : ℕ)
  (hn : n = ∏ i, p i)
  (a : ZMod n) :
  ∀ x : ZMod n, x^2 = a ↔ ∀ i, (x.val : ZMod (p i))^2 = (a.val : ZMod (p i)) := by
  sorry

theorem theorem_838584_problem
  (M N : Type*)
  (zero_M : M) (succ_M : M → M) (add_M : M → M → M) (mul_M : M → M → M)
  (zero_N : N) (succ_N : N → N) (add_N : N → N → N) (mul_N : N → N → N)
  (f : M → N)
  (h_bij : Function.Bijective f)
  (h_add : ∀ a b, f (add_M a b) = add_N (f a) (f b))
  (h_mul : ∀ a b, f (mul_M a b) = mul_N (f a) (f b))
  (h_zero : f zero_M = zero_N)
  (h_succ : ∀ a, f (succ_M a) = succ_N (f a)) :
  ∃ e : M ≃ N,
    (e zero_M = zero_N) ∧
    (∀ a, e (succ_M a) = succ_N (e a)) ∧
    (∀ a b, e (add_M a b) = add_N (e a) (e b)) ∧
    (∀ a b, e (mul_M a b) = mul_N (e a) (e b)) := by
  sorry







theorem theorem_838254_problem (d : ℤ) (h_sf : Squarefree d) (h_d : d ≠ 1)
  (p : ℕ) (hp : p.Prime) :
  Irreducible ((p : ℤ) : Zsqrtd (-d)) ↔ ¬ ∃ (u v : ℤ), u ^ 2 + d * v ^ 2 = p := by
  sorry

theorem theorem_838607_problem
  {R S : Type*} {n : Type*}
  [CommRing R] [AddCommGroup S] [Module R S]
  [Fintype n] [DecidableEq n] :
  ∃ Ψ : Module.End R (n → S) ≃ₗ[R] Matrix n n (Module.End R S),
    ∀ (ϕ : Module.End R (n → S)) (i j : n),
      (Ψ ϕ) i j = (LinearMap.proj j).comp (ϕ.comp (LinearMap.stdBasis R (fun _ ↦ S) i)) := by
  sorry



theorem theorem_838723_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (A B C : V)
  (D : V) (hD : D = midpoint ℝ B C)
  (G : V) (hG : G = (1 / 3 : ℝ) • (A + B + C)) :
  dist A G = 2 * dist G D := by
  sorry















theorem theorem_838970_problem
  (a : ℕ → ℚ)
  (P : Polynomial ℚ)
  (hP : P = ∑ i in Finset.range 6, Polynomial.C (a (i + 1)) * Polynomial.X^(i + 1))
  (A : PowerSeries ℚ)
  (hA : A = (P : PowerSeries ℚ) * (1 - PowerSeries.X^6)⁻¹)
  (B : PowerSeries ℚ)
  (hB : B = (PowerSeries.X^8 * (P : PowerSeries ℚ)) *
    ((1 - PowerSeries.X^6) * (1 - 2 * PowerSeries.X^8))⁻¹) :
  B = PowerSeries.X^8 * A * (1 - 2 * PowerSeries.X^8)⁻¹ := by
  sorry











theorem theorem_838808_problem (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℝ) :
  ∃ Ag : Matrix (Fin m) (Fin n) ℝ, A * Ag * A = A := by
  sorry

theorem theorem_839448_problem
  {K : Type*} [Field K]
  {n : ℕ}
  (A : Matrix (Fin n) (Fin n) K)
  (L : Matrix (Fin n) (Fin n) K →ₗ[K] Matrix (Fin n) (Fin n) K)
  (h : ∀ X, L X = A * X) :
  LinearMap.charpoly L = (Matrix.charpoly A) ^ n := by
  sorry

theorem theorem_839645_problem {α β : Type*} (A : Set α) (B : Set β) :
  A ×ˢ B = {p | ∃ a ∈ A, ∃ b ∈ B, p = (a, b)} := by
  sorry



theorem theorem_838915_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) (ZMod 2))
  (hA : A.IsSymm) :
  ∃ x : Fin n → ZMod 2, A.mulVec x = fun i => A i i := by
  sorry

theorem theorem_839744_problem (f_seq g_seq : ℕ → ℝ) (f g : ℝ)
  (h_eq : ∀ n, f_seq n = g_seq n)
  (hf : Filter.Tendsto f_seq Filter.atTop (nhds f))
  (hg : Filter.Tendsto g_seq Filter.atTop (nhds g)) :
  f = g := by
  sorry



theorem theorem_839503_problem
  (F : ℕ → ℤ)
  (f : ℕ → ℝ)
  (hf : ∀ n, 0 ≤ f n)
  (h : ∀ n, 1 ≤ n → (2 : ℝ)^(F n) ≤ ∑ k in Finset.Icc 1 n, (2 : ℝ)^(-f k) ∧
                     ∑ k in Finset.Icc 1 n, (2 : ℝ)^(-f k) < (2 : ℝ)^(F n + 1)) :
  ∀ m : ℤ, 0 ≤ m → (∑' k, if 1 ≤ k ∧ F k = m then (2 : ℝ)^(-f k) else 0) ≥ (2 : ℝ)^m - 1 := by
  sorry





theorem theorem_839634_problem (f : ℤ → ℝ) (hf : ∀ n, f n ∈ Set.Icc (-1 : ℝ) 1) :
  ∃ f_bar : ℝ → ℝ, ContDiff ℝ ⊤ f_bar ∧ 
  (∀ x, f_bar x ∈ Set.Icc (-1 : ℝ) 1) ∧ 
  (∀ n : ℤ, f_bar n = f n) := by
  sorry









theorem theorem_839959_problem (a : ℕ → ℝ) (L : ℝ)
  (h_conv : Summable a)
  (h_not_abs : ¬ Summable (fun n => |a n|)) :
  ∃ σ : ℕ ≃ ℕ, HasSum (a ∘ σ) L := by
  sorry







theorem theorem_840720_problem (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
  (h : ∀ k, ∃ N, ∀ n ≥ N, a n k = b k) :
  ∀ k, Filter.Tendsto (fun n ↦ a n k) Filter.atTop (nhds (b k)) := by
  sorry

theorem theorem_840995_problem
  {X : Type*} [MetricSpace X] [CompleteSpace X]
  (K : ℕ → Set X)
  (h_nonempty : ∀ n, (K n).Nonempty)
  (h_closed : ∀ n, IsClosed (K n))
  (h_nested : ∀ n, K (n + 1) ⊆ K n)
  (h_diam : Filter.Tendsto (fun n ↦ Metric.diam (K n)) Filter.atTop (nhds 0)) :
  ∃! x, x ∈ ⋂ n, K n := by
  sorry



theorem theorem_840970_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (h_inf : ¬ FiniteDimensional ℝ X)
  (f : X →ₗ[ℝ] ℝ) (hf_discont : ¬ Continuous f)
  {X₁ : Type*} [NormedAddCommGroup X₁] [NormedSpace ℝ X₁]
  (L : X ≃ₗ[ℝ] X₁)
  (h_norm : ∀ x : X, ‖L x‖ = ‖x‖ + |f x|) :
  ¬ CompleteSpace X₁ := by
  sorry

theorem theorem_841362_problem (c_i g_i : ℝ) :
  c_i^2 + 2 * c_i * g_i + g_i^2 ≥ 0 := by
  sorry





theorem theorem_841256_problem :
  ∃ (f : ℝ × ℝ → ℝ) (x₀ y₀ : ℝ),
    ContDiff ℝ 1 f ∧
    f (x₀, y₀) = 0 ∧
    deriv (fun y => f (x₀, y)) y₀ = 0 ∧
    ¬ ∃ (U : Set ℝ) (g : ℝ → ℝ), IsOpen U ∧ x₀ ∈ U ∧ ContDiffOn ℝ 1 g U ∧ g x₀ = y₀ ∧ ∀ x ∈ U, f (x, g x) = 0 := by
  sorry







theorem theorem_841418_problem (f : ℝ × ℝ → ℝ)
  (h : ∀ x1 x2 : ℝ, f (x1, x2) = x1^6 + x2^6 - 5 * x1 * x2) :
  Filter.Tendsto f (Filter.cocompact (ℝ × ℝ)) Filter.atTop := by
  sorry









theorem theorem_841937_problem {n : ℕ} {K : Type*} [Field K] 
  (E : Matrix (Fin n) (Fin n) K) :
  (∀ b : Fin n → K, ∃! x : Fin n → K, Matrix.mulVec E x = b) ↔ IsUnit E := by
  sorry



theorem theorem_841943_problem (n m k T : ℝ)
  (hn : 0 ≤ n)
  (hm : 0 < m)
  (hk : 0 < k)
  (hT : 0 < T) :
  ∫ v in Set.Ioi 0, v ^ (n + 2) * Real.exp (- (m * v ^ 2) / (2 * k * T)) =
  (2 ^ ((n + 1) / 2) * Real.Gamma ((n + 3) / 2) * (k * T) ^ ((n + 3) / 2)) / m ^ ((n + 3) / 2) := by
  sorry





theorem theorem_841732_problem
  (F : Type*) [Field F]
  (n : ℕ) (hn : n > 0)
  (c : F) :
  ∃ (A : AffineSubspace F (Fin n → F)),
    (A : Set (Fin n → F)) = {x | ∑ i, x i = c} ∧
    FiniteDimensional.finrank F A.direction = n - 1 := by
  sorry



theorem theorem_842370_problem {X : Type*} [MetricSpace X] (A : Set X) :
  IsClosed A ↔ {x : X | ∀ ε > 0, ∃ y ∈ A, y ≠ x ∧ dist x y < ε} ⊆ A := by
  sorry

theorem theorem_842144_problem
  (F : Type*) [Field F]
  (V W : Type*) [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  (T : V →ₗ[F] W)
  (h_surj : Function.Surjective T) :
  ∃ S : W →ₗ[F] V, ∀ w, T (S w) = w := by
  sorry





theorem theorem_842116_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  {W : Type*} [AddCommGroup W] [Module K W]
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  (bV : Basis n K V)
  (bW : Basis m K W)
  (T : V →ₗ[K] W) :
  LinearMap.toMatrix bW.dualBasis bV.dualBasis (LinearMap.dualMap T) =
  (LinearMap.toMatrix bV bW T).transpose := by
  sorry

theorem theorem_842391_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
  (h : ∃ C : Matrix (Fin n) (Fin n) ℝ, IsUnit C ∧ A = C⁻¹ * B.transpose * C) :
  A.charpoly = B.charpoly := by
  sorry







theorem theorem_842590_problem (a b c : ℝ)
  (h1 : a ≠ b) (h2 : b ≠ c) (h3 : c ≠ a) :
  (a^2 * (b - c)^3 + b^2 * (c - a)^3 + c^2 * (a - b)^3) /
  ((a - b) * (b - c) * (c - a)) = a * b + b * c + c * a := by
  sorry

theorem theorem_841252_problem
  -- Define a complete normed vector space over Complex numbers
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  -- Variables corresponding to the problem entities
  (phi : ℕ → E)
  (T : E →L[ℂ] E) -- Continuous linear map representing the integral operator
  (lambda : ℕ → ℂ)
  (psi : ℕ → E)
  (c : ℕ → ℂ)
  -- Conditions derived from the problem
  (h_recurrence : ∀ n : ℕ, n ≥ 1 → phi n = T (phi (n - 1)))
  (h_eigen : ∀ k : ℕ, T (psi k) = lambda k • psi k)
  (h_init : HasSum (fun k => c k • psi k) (phi 0)) :
  -- Conclusion: The series expansion for phi_n
  ∀ n : ℕ, HasSum (fun k => (c k * (lambda k) ^ n) • psi k) (phi n) := by
  sorry



theorem theorem_842574_problem (X Y : TopCat) (f : X → Y) :
  (∃ (g : X ⟶ Y), (g : X → Y) = f) ↔ Continuous f := by
  sorry

theorem theorem_842462_problem
  (ρ₂ : (ℝ × ℝ) → (ℝ × ℝ) → ℝ)
  (hρ₂_cont : Continuous (Function.uncurry ρ₂))
  (hρ₂_zero : ∀ x : ℝ × ℝ, ρ₂ x x = 0)
  (h : ℝ ≃ₜ {p : ℝ × ℝ // ‖p‖ = 1 ∧ p ≠ (0, 1)}) :
  Filter.Tendsto (fun z => ρ₂ (h z) (h (-z))) Filter.atTop (nhds 0) := by
  sorry







