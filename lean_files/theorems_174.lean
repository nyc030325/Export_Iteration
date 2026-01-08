import Mathlib
import Mathlib.Tactic









theorem theorem_953641_problem (a : ℕ → ℝ)
  (h_bounded : Bornology.IsBounded (Set.range a))
  (h_mono : Monotone a ∨ Antitone a) :
  ∃ L, Filter.Tendsto a Filter.atTop (nhds L) := by
  sorry



theorem theorem_954798_problem (s : Setoid ℝ)
  (h : ∀ x y : ℝ, s.r x y ↔ ∃ q : ℚ, x - y = (q : ℝ)) :
  ∀ U : Set (Quotient s), IsOpen U ↔ U = ∅ ∨ U = Set.univ := by
  sorry





theorem theorem_954821_problem (m n : ℕ) (hm : m > 0) (hn : n > 0) 
  (h_gcd : Nat.gcd m n = 1) : 
  Nonempty ((ZMod m × ZMod n) ≃+* ZMod (m * n)) := by
  sorry













theorem theorem_955545_problem (a : ℕ → ℝ)
  (h1 : Filter.Tendsto a Filter.atTop (nhds 0))
  (h2 : Summable a) :
  Summable (fun n => (a n)^2 * Real.cos (n : ℝ)) := by
  sorry





theorem theorem_955296_problem :
  ∃ C > 0, ∃ x₀ > 0, ∀ x : ℝ, x ≥ x₀ →
    |∑ n in Finset.Icc 1 (Nat.floor x), (ArithmeticFunction.moebius n : ℝ) / (Nat.totient n : ℝ)| ≤ C * Real.log x := by
  sorry



theorem theorem_955942_problem
  (M : Type*) [MetricSpace M]
  -- We abstract the notion of Tangent space and Geodesic property 
  -- since they are specific to the problem's geometric context.
  (T : M → Type*)
  (IsGeodesicWithInit : (ℝ → M) → (p : M) → T p → Prop)
  -- Condition 1: Local compactness
  (h1 : LocallyCompactSpace M)
  -- Condition 2: Completeness
  (h2 : CompleteSpace M)
  -- Condition 3: Geodesic completeness (defined on ℝ implies indefinitely extended)
  (h3 : ∀ (p : M) (v : T p), ∃ γ : ℝ → M, IsGeodesicWithInit γ p v) :
  -- Conclusion: M is complete and geodesics can be fully extended
  CompleteSpace M ∧ (∀ (p : M) (v : T p), ∃ γ : ℝ → M, IsGeodesicWithInit γ p v) := by
  sorry





theorem theorem_955935_problem
  (f g : Ordinal → Ordinal)
  (is_definable : Ordinal → ℕ → Prop)
  (h_rayo : ∀ (m L : ℕ) (x : Ordinal), m > L → is_definable x L → f m > x)
  (h_tree : ∃ L : ℕ, ∀ n : ℕ, is_definable (g n) L) :
  ∀ n : ℕ, ∃ m : ℕ, m > n ∧ f m > g m := by
  sorry









theorem theorem_956414_problem (k : ℕ) (hk : k > 0) :
  (2 * k - 1).doubleFactorial = (2 * k).factorial / (2 ^ k * k.factorial) := by
  sorry

theorem theorem_956230_problem (n : ℕ) (h : n > 0) :
  Nat.choose (2 * n - 1) n = ∑ j in Finset.range n, Nat.choose (n + j - 1) j := by
  sorry



theorem theorem_956407_problem (x y a b : ℕ)
  (hx : x > 1) (hy : y > 1)
  (ha : a > 1) (hb : b > 1)
  (h_eq : x^a - y^b = 1) :
  x = 3 ∧ y = 2 ∧ a = 2 ∧ b = 3 := by
  sorry



theorem theorem_956052_problem
  {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
  (p : E → B) (hp : IsCoveringMap p)
  (F : unitInterval × unitInterval → B) (hF : Continuous F)
  (x₀ y₀ : unitInterval)
  (e₀ : E)
  (h_pt : p e₀ = F (x₀, y₀)) :
  ∃! (F_tilde : unitInterval × unitInterval → E),
    Continuous F_tilde ∧ F_tilde (x₀, y₀) = e₀ ∧ p ∘ F_tilde = F := by
  sorry





theorem theorem_956547_problem {X : Type*} [TopologicalSpace X] (A : Set X) 
  (h1 : Set.Countable A) 
  (h2 : IsClosed A) : 
  closure A = A := by
  sorry



theorem theorem_956796_problem {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
  (A : Matrix n n R) (h : A.transpose = -A) :
  (A ^ 2).transpose = A ^ 2 := by
  sorry

theorem theorem_956858_problem (x : ℝ) (h : x = Real.logb 2 7) : Irrational x := by
  sorry





theorem theorem_957047_problem (X : Type*) [TopologicalSpace X] (A : Set X) :
  (∃ r : ContinuousMap X ↥A, ∀ a : ↥A, r a = a) ↔
  (∃ r : ContinuousMap X ↥A, r.comp ⟨Subtype.val, continuous_subtype_val⟩ = ContinuousMap.id ↥A) := by
  sorry





theorem theorem_956857_problem (f : ℝ × ℝ → ℝ)
  (h_smooth_pos : ContDiffOn ℝ ⊤ f {p | 0 < p.1})
  (h_smooth_neg : ContDiffOn ℝ ⊤ f {p | p.1 < 0})
  (h_exist_partial_x : ∀ y, DifferentiableAt ℝ (fun x ↦ f (x, y)) 0)
  (h_exist_partial_y : ∀ y, DifferentiableAt ℝ (fun z ↦ f (0, z)) y)
  (h_cont_partial_x : ∀ y, ContinuousAt (fun p ↦ deriv (fun x ↦ f (x, p.2)) p.1) (0, y))
  (h_cont_partial_y : ∀ y, ContinuousAt (fun p ↦ deriv (fun z ↦ f (p.1, z)) p.2) (0, y)) :
  ContDiff ℝ 1 f := by
  sorry



theorem theorem_956759_problem (m n : ℕ) (p q : ℝ)
  (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) :
  let P : ℝ → ℝ := fun x ↦ (1 - x^(m + n - 1)) / (1 - x)
  (1 / (p^m * (p + q)^n)) * (∑ h in Finset.range m, (Nat.choose (n + h - 1) h : ℝ) * (p / (p + q))^h) +
  (1 / (q^n * (p + q)^m)) * (∑ k in Finset.range n, (Nat.choose (m + k - 1) k : ℝ) * (q / (p + q))^k) =
  (deriv^[n - 1] P (p / (p + q))) / (Nat.factorial (n - 1) : ℝ) +
  (deriv^[m - 1] P (q / (p + q))) / (Nat.factorial (m - 1) : ℝ) := by
  sorry







theorem theorem_958021_problem (n : ℕ) :
  19 ∣ (5^(2 * n + 1) * 2^(n + 2) + 3^(n + 2) * 2^(2 * n + 1)) := by
  sorry









theorem theorem_957625_problem (R₁ R₂ : Matrix (Fin 3) (Fin 3) ℝ)
  (hR₁_orth : R₁.transpose * R₁ = 1)
  (hR₁_det : R₁.det = 1)
  (hR₂_orth : R₂.transpose * R₂ = 1)
  (hR₂_det : R₂.det = 1) :
  (R₁ * R₂).transpose * (R₁ * R₂) = 1 ∧ (R₁ * R₂).det = 1 := by
  sorry

theorem theorem_957926_problem (f : (ℝ → ℝ) →ₗ[ℝ] ℝ)
  (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ⊤ φ → HasCompactSupport φ → f (fun x ↦ x * φ x) = 0) :
  ∃ c : ℝ, ∀ φ : ℝ → ℝ, ContDiff ℝ ⊤ φ → HasCompactSupport φ → f φ = c * φ 0 := by
  sorry

theorem theorem_957890_problem (f : Polynomial ℝ) (q : ℚ)
  (h_symm : ∀ x : ℝ, f.eval x = f.eval ((q : ℝ) - x))
  (h_int_zero : ∀ n : ℕ, ∃ k : ℤ, (Polynomial.derivative^[n] f).eval 0 = k) :
  ∀ n : ℕ, ∃ k : ℤ, (Polynomial.derivative^[n] f).eval (q : ℝ) = k := by
  sorry



theorem theorem_958094_problem
  {X X_tilde : Type*} [TopologicalSpace X] [TopologicalSpace X_tilde]
  (p : X_tilde → X) (hp : IsCoveringMap p)
  (beta : C(unitInterval, X))
  (x_tilde_0 : X_tilde)
  (h_start : p x_tilde_0 = beta 0)
  (h_null : ∃ c : X, ContinuousMap.Homotopic beta (ContinuousMap.const unitInterval c)) :
  ∃! beta_tilde : C(unitInterval, X_tilde),
    beta_tilde 0 = x_tilde_0 ∧ p ∘ beta_tilde = beta := by
  sorry





theorem theorem_958775_problem (r s : ℤ) :
  2 * r = (r + s + 1)^2 - (r + s)^2 - ((s + 1)^2 - s^2) := by
  sorry



theorem theorem_958057_problem
  (R : ℝ → ℝ) -- Autocorrelation function R_xx
  (Q : ℝ → ℝ) -- Autocorrelation function R_xdot_xdot
  (h_diff : ContDiff ℝ 2 R) -- Regularity condition: R is twice differentiable
  -- Condition derived from the definition of the derivative process autocorrelation:
  -- It is the mixed partial derivative of the original autocorrelation R(t1 - t2).
  (h_def : ∀ t1 t2 : ℝ, Q (t1 - t2) = deriv (fun x => deriv (fun y => R (x - y)) t2) t1) :
  ∀ τ : ℝ, Q τ = - (deriv (deriv R) τ) := by
  sorry

















theorem theorem_958684_problem
  {I Brand : Type*} [Fintype I] [DecidableEq Brand]
  (x : I → ℝ) (B : I → Brand) (p v : I → ℝ) (L U : ℝ) (b : Brand)
  (h_binary : ∀ i, x i = 0 ∨ x i = 1)
  (h_denom_pos : ∑ i in Finset.univ.filter (λ j => B j = b), v i * x i > 0) :
  (L ≤ (∑ i in Finset.univ.filter (λ j => B j = b), p i * x i) /
        (∑ i in Finset.univ.filter (λ j => B j = b), v i * x i) ∧
   (∑ i in Finset.univ.filter (λ j => B j = b), p i * x i) /
    (∑ i in Finset.univ.filter (λ j => B j = b), v i * x i) ≤ U) ↔
  (L * (∑ i in Finset.univ.filter (λ j => B j = b), v i * x i) ≤
    ∑ i in Finset.univ.filter (λ j => B j = b), p i * x i ∧
   ∑ i in Finset.univ.filter (λ j => B j = b), p i * x i ≤
    U * (∑ i in Finset.univ.filter (λ j => B j = b), v i * x i)) := by
  sorry

theorem theorem_958800_problem (v k t n : ℕ)
  (hv : v ≠ 0)
  (hk : 1 ≤ k)
  (hkv : k ≤ v)
  (ht : 1 ≤ t)
  (htk : t ≤ k)
  (S : Fin n → Finset (Fin v))
  (h_size : ∀ i, (S i).card = k)
  (h_cover : ∀ T : Finset (Fin v), T.card = t → ∃ i, T ⊆ S i) :
  Nat.choose v t ≤ n * Nat.choose k t := by
  sorry

theorem theorem_959021_problem
  {A B : Type*}
  [LinearOrder A] [IsWellOrder A (· < ·)]
  (f : A → B) (hf : Function.Surjective f)
  (g : B → A)
  (hg_mem : ∀ b, f (g b) = b)
  (hg_min : ∀ b a, f a = b → g b ≤ a) :
  IsWellOrder B (fun b₁ b₂ => g b₁ < g b₂) := by
  sorry





theorem theorem_958317_problem (n m k : ℕ) (hn : n > 0) (hm : m > 0) (hk : k > 0) :
  n^k % m = (∏ p in n.factorization.support, (p ^ (n.factorization p * k)) % m) % m := by
  sorry

theorem theorem_959577_problem (s : ℕ → ℝ) (h : ¬ BddAbove (Set.range s)) :
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (s ∘ φ) Filter.atTop Filter.atTop := by
  sorry











theorem theorem_959548_problem
  (f g : EuclideanSpace ℝ (Fin 3) → ℝ)
  (hf : ContDiff ℝ ⊤ f)
  (hg : ContDiff ℝ ⊤ g) :
  gradient (fun x ↦ f x * g x) = fun x ↦ f x • gradient g x + g x • gradient f x := by
  sorry





theorem theorem_959631_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (n : ℕ)
  (w : ℕ → V)
  (w' : ℕ → V)
  (h_symm : ∀ u v, T u v = T v u)
  (h_def : ∀ i < n, w' i = w i - ∑ j in Finset.range i, (T (w i) (w' j) / T (w' j) (w' j)) • w' j)
  (h_non_iso : ∀ i < n, T (w' i) (w' i) ≠ 0) :
  ∀ i j, i < n → j < n → i ≠ j → T (w' i) (w' j) = 0 := by
  sorry

theorem theorem_959898_problem
  (a : ℕ → ℝ)
  (f : ℝ → ℝ)
  (h_pos : ∀ n, 0 < a n)
  (h_lim : Filter.Tendsto a Filter.atTop (nhds 0))
  (h_mod0 : ∀ n, n % 4 = 0 → f (a n) = 1)
  (h_mod1 : ∀ n, n % 4 = 1 → f (a n) = -1)
  (h_mod23 : ∀ n, n % 4 = 2 ∨ n % 4 = 3 → f (a n) = 0) :
  ¬ ∃ L, Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  sorry

theorem theorem_959880_problem (m n r : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
  (h_rank : A.rank = r) :
  ∃ (rows : Fin r → Fin m) (cols : Fin r → Fin n),
    StrictMono rows ∧ StrictMono cols ∧ (A.submatrix rows cols).det ≠ 0 := by
  sorry





theorem theorem_960255_problem (f : ℝ → ℝ) (ε : ℝ)
  (h_smooth : ContDiff ℝ ⊤ f)
  (h_compact : HasCompactSupport f)
  (h_eps : ε > 0) :
  ∫ x in Set.Ioo (-ε) ε, f x ∂(MeasureTheory.Measure.dirac 0) = f 0 := by
  sorry

theorem theorem_959735_problem (i : ℕ) (hi : i > 0) :
  Int.floor (((2 * (i : ℚ) - 1) ^ 2) / 2) - 1 = 2 * (i : ℤ) ^ 2 - 2 * (i : ℤ) - 1 := by
  sorry

theorem theorem_960406_problem (x y : ℝ) :
  Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y := by
  sorry





