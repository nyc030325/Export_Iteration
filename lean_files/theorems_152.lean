import Mathlib
import Mathlib.Tactic

theorem theorem_826146_problem (n k : ℕ) (a : Fin (k - 1) → ℕ) (b : ℕ)
  (hn : n > 0)
  (h_div : ∀ i, n ∣ a i) :
  (∑ i, a i) + b ≡ b [MOD n] := by
  sorry







theorem theorem_826472_problem
  (p : ℝ)
  (hp_bound : p ∈ Set.Icc 0 1)
  (p_func : ℝ → ℝ)
  -- Representation of the conditional PMF P(Y=y | X=x) as a function of y and x
  (cond_pmf : ℝ → ℝ → ℝ)
  -- Condition: Y is Bernoulli with success probability p(x) for x in the domain
  (h_bernoulli : ∀ x ∈ Set.Icc 0 1, ∀ y,
    cond_pmf y x = if y = 1 then p_func x else if y = 0 then 1 - p_func x else 0)
  -- Condition: p(x) = p for all x in [0, 1]
  (h_const : ∀ x ∈ Set.Icc 0 1, p_func x = p) :
  -- Conclusion: The specific form of the conditional PMF
  ∀ x ∈ Set.Icc 0 1, ∀ y,
    cond_pmf y x = if y = 1 then p else if y = 0 then 1 - p else 0 := by
  sorry

theorem theorem_826384_problem
  (F : Type*) [Field F]
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) F) :
  FiniteDimensional.finrank F (Submodule.span F (Set.range A)) =
  FiniteDimensional.finrank F (Submodule.span F (Set.range A.transpose)) := by
  sorry



theorem theorem_826326_problem (K : Type*) [Field K] (n : ℕ)
  (w : Fin (n + 1) → ℕ) (hw : ∀ i, w i > 0) (d : ℕ) :
  FiniteDimensional K (Submodule.span K
    {p : MvPolynomial (Fin (n + 1)) K | ∃ s : Fin (n + 1) →₀ ℕ,
      p = MvPolynomial.monomial s 1 ∧ s.sum (fun i a => a * w i) = d}) := by
  sorry

theorem theorem_826572_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (X : Set V)
  (h_affine : ∀ x ∈ X, ∀ y ∈ X, ∀ t : ℝ, t • x + (1 - t) • y ∈ X) :
  ∀ x ∈ X, ∀ y ∈ X, ∀ t : ℝ, t ∈ Set.Icc 0 1 → t • x + (1 - t) • y ∈ X := by
  sorry













theorem theorem_826552_problem (a b c : ℝ) 
  (h_disc : b^2 - 4 * a * c < 0) : 
  ∀ (x y : ℝ), a * x^2 + b * x * y + c * y^2 = 0 → x = 0 ∧ y = 0 := by
  sorry

theorem theorem_827075_problem (A : Type*) (R : A → A → Prop)
  (h : ∀ x y, R x y → ¬ R y x) :
  ∀ x y, R x y ∧ R y x → x = y := by
  sorry



theorem theorem_827129_problem (x : ℝ) :
  HasDerivAt (fun x => (1 / 16 : ℝ) * (Real.arctan (x - 1) + Real.arctan (x + 1)))
    ((2 + x ^ 2) / (32 + 8 * x ^ 4)) x := by
  sorry







theorem theorem_825348_problem
  (Prr Prl Plr Pll : ℝ)
  (h_nonneg : 0 ≤ Prr ∧ 0 ≤ Prl ∧ 0 ≤ Plr ∧ 0 ≤ Pll)
  (h_sum_r : Prr + Prl = 1)
  (h_sum_l : Plr + Pll = 1)
  (πR πL : ℝ)
  (h_stat_nonneg : 0 ≤ πR ∧ 0 ≤ πL)
  (h_stat_sum : πR + πL = 1)
  (h_stat_bal_R : πR = πR * Prr + πL * Plr)
  (h_stat_bal_L : πL = πR * Prl + πL * Pll)
  (pr pl : ℝ)
  (h_pr : pr = Prr + Plr)
  (h_pl : pl = Prl + Pll)
  (v : ℝ)
  (h_v : v = (πR * Prr + πL * Plr) * 1 + (πR * Prl + πL * Pll) * (-1)) :
  v = pr - pl := by
  sorry



theorem theorem_826883_problem
  (m L r : ℝ)
  (U : ℝ → ℝ)
  (V : ℝ → ℝ)
  (hm : m = 1)
  (hr : r > 0)
  (hL : L > 0)
  (hV : ∀ x, V x = U x + L^2 / (2 * m * x^2))
  (hU_diff : DifferentiableAt ℝ U r)
  (hU_diff2 : DifferentiableAt ℝ (deriv U) r)
  (h_circ : deriv V r = 0)
  (h_denom_pos : 3 * deriv U r + r * deriv (deriv U) r > 0)
  (h_rad_pos : deriv (deriv V) r > 0) :
  Real.sqrt (deriv U r / (3 * deriv U r + r * deriv (deriv U) r)) =
  L / (r^2 * Real.sqrt (deriv (deriv V) r)) := by
  sorry

theorem theorem_827319_problem (n : ℕ) (M : Type*) [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [SmoothManifoldWithCorners (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M]
  (p : M) :
  Nonempty (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) p ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) := by
  sorry

theorem theorem_827824_problem
  (n m : ℕ)
  (ν : Fin m → ℕ)
  (k : Fin m → ℕ)
  (h_distinct : Function.Injective ν)
  (h_pos : ∀ i, 1 ≤ ν i)
  (h_sum : ∑ i, k i * ν i = n) :
  let target_cycle_type := (∑ i, Multiset.replicate (k i) (ν i)).filter (· ≥ 2)
  (Finset.univ.filter (λ σ : Equiv.Perm (Fin n) ↦ σ.cycleType = target_cycle_type)).card =
  n.factorial / ((∏ i, (k i).factorial) * (∏ i, (ν i) ^ (k i))) := by
  sorry



theorem theorem_827808_problem
  (X : Type*) -- Smooth projective variety
  (n : ℕ) (hn : n ≠ 0) -- Dimension n ≠ 0
  (H : Type*) -- Ample divisor H
  (VectorBundle : Type*) -- Type for vector bundles
  (rank : VectorBundle → ℕ) -- Rank function
  (slope : VectorBundle → ℚ) -- Slope defined by H
  (is_semistable : VectorBundle → Prop) -- Semistability defined by H
  (Hom : VectorBundle → VectorBundle → Type*) -- Set of morphisms
  [∀ E F, Zero (Hom E F)] -- Existence of zero morphism
  (E1 E2 : VectorBundle)
  (h_rank : rank E1 = rank E2)
  (h_ss1 : is_semistable E1)
  (h_ss2 : is_semistable E2)
  (h_mor : ∃ f : Hom E1 E2, f ≠ 0) :
  slope E1 ≤ slope E2 := by
  sorry

theorem theorem_827487_problem
  (c1 c2 : ℕ)
  (p q : ℝ)
  (h_c1 : c1 ≥ 1)
  (P_N1 : ℕ → ℝ)
  (P_N2 : ℕ → ℝ)
  (h_P_N1 : ∀ x, P_N1 x = (c1 - 1).choose x * p ^ x * (1 - p) ^ (c1 - 1 - x))
  (h_P_N2 : ∀ y, P_N2 y = c2.choose y * q ^ y * (1 - q) ^ (c2 - y))
  (P_Delta : ℤ → ℝ)
  (h_P_Delta : ∀ z, P_Delta z = ∑ x in Finset.range c1, ∑ y in Finset.range (c2 + 1),
    if (x : ℤ) - y = z then P_N1 x * P_N2 y else 0) :
  ∀ z, P_Delta z = ∑ y in Finset.range (c2 + 1),
    (if (z + y) ≥ 0 then P_N1 (z + y).toNat else 0) * P_N2 y := by
  sorry

theorem theorem_827237_problem
  {X : Type*}
  (f_n g_n : ℕ → X → ℝ)
  (f g : X → ℝ)
  (h_funif : TendstoUniformly f_n f atTop)
  (h_gunif : TendstoUniformly g_n g atTop)
  (hg_ne : ∀ x, g x ≠ 0)
  (hgn_ne : ∀ n x, g_n n x ≠ 0)
  (h_bound : ∃ C > 0, ∀ n x, |g_n n x| ≥ C) :
  TendstoUniformly (fun n x ↦ f_n n x / g_n n x) (fun x ↦ f x / g x) atTop := by
  sorry



theorem theorem_827459_problem
  (n : ℕ)
  (M : ℕ → ℕ → ℕ → ℕ → Prop)
  (I : ℕ → ℕ → Prop)
  -- The problem references Fischer and Rabin's M_n, which is constructed such that
  -- it is only valid for numbers below a double exponential bound.
  (hM : ∀ (x y z : ℕ), M (n + 1) x y z → x < 2^(2^(n + 1)))
  -- Definition of I_n(x) given in the problem
  (hI : ∀ (x : ℕ), I n x ↔ M (n + 1) x 0 0)
  (x : ℕ)
  (h_Ix : I n x) :
  x < 2^(2^(n + 1)) := by
  sorry













theorem theorem_828340_problem (n : ℕ)
  (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  (g : EuclideanSpace ℝ (Fin n)) :
  inner g (B g) ≤ ‖B‖ * ‖g‖ ^ 2 := by
  sorry

theorem theorem_827550_problem :
  Summable (fun n : ℕ => if n ≤ 1 then 0 else (-1 : ℝ) ^ n / (n * Real.log n)) →
  Summable (fun n : ℕ => if n ≤ 1 then 0 else (-1 : ℝ) ^ (Nat.primeCounting n) / (n * Real.log n)) := by
  sorry



theorem theorem_828937_problem (p q r : ℕ)
  (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
  (hr_even : Even r) :
  p^2 + 1 ≠ q^2 + r^2 := by
  sorry



theorem theorem_827876_problem (a b : Fin 5 → ℕ) (t : ℕ)
  (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (ht : 0 < t)
  (h1 : ∑ i, a i = ∑ i, b i)
  (h2 : ∑ i, (a i)^2 = ∑ i, (b i)^2) :
  (∑ i, (a i + t) = ∑ i, (b i + t)) ∧
  (∑ i, (a i + t)^2 = ∑ i, (b i + t)^2) := by
  sorry





theorem theorem_828595_problem
  (f : ℝ → ℝ) (hf : Continuous f)
  (a k : ℝ) (ha : 0 < a) (hk : 0 < k)
  (h_ineq : ∀ (n : ℕ) (x : ℝ), 0 < n → 0 < x →
    (∏ i in Finset.Icc 1 n, f ((i : ℝ) * x)) ≤ a * (n : ℝ) ^ k) :
  ∃ c : ℝ, ∀ x, f x = c := by
  sorry

theorem theorem_828903_problem {X : Type*} [TopologicalSpace X] (A B : Set X) :
  Dense (Subtype.val ⁻¹' A : Set B) ↔ B ⊆ closure A := by
  sorry

theorem theorem_828699_problem (ν : ℝ) (n : ℕ)
  (h_irr : Irrational ν)
  (h_alg : IsAlgebraic ℚ ν)
  (h_deg : (minpoly ℚ ν).natDegree = n) :
  ∃ c : ℝ, c > 0 ∧ ∀ (p q : ℤ), 0 < q →
    |((p : ℝ) / (q : ℝ)) - ν| ≥ c / ((q : ℝ) ^ n) := by
  sorry

theorem theorem_828234_problem
  (S : Type*)
  (f : S → S)
  (s₁ : S)
  (h1 : ∀ k : ℕ, k ≠ 0 → f^[k] s₁ ≠ s₁)
  (h2 : Function.Injective f)
  (P : S → Prop)
  (h_base : P s₁)
  (h_step : ∀ s : S, P s → P (f s)) :
  ∀ k : ℕ, P (f^[k] s₁) := by
  sorry





theorem theorem_829008_problem (f : ℝ → ℝ) (h : ∀ x, f x = Real.log x / x) :
  Set.image f (Set.Ioi 0) = Set.Iic (1 / Real.exp 1) := by
  sorry



















theorem theorem_829701_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  (R : X →L[𝕜] Y) (x : X) :
  iteratedFDeriv 𝕜 2 R x = 0 := by
  sorry







theorem theorem_829826_problem (k : ℕ) (hk : k > 0) :
  Filter.Tendsto (fun (n : ℕ) => (Nat.choose n k : ℝ) / ((n : ℝ) ^ k / (Nat.factorial k : ℝ))) Filter.atTop (nhds 1) := by
  sorry

theorem theorem_830076_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (B : V →L[ℝ] V →L[ℝ] ℝ) -- Continuous bilinear map
  (h_sym : ∀ u v : V, B u v = B v u) -- Symmetry condition
  (x : ℝ → V)
  (hx : Differentiable ℝ x) -- x is differentiable
  (t : ℝ) :
  deriv (fun s => B (x s) (x s)) t = 2 * B (x t) (deriv x t) := by
  sorry



theorem theorem_829494_problem (n k : ℕ) (x : Fin n → ℝ)
  (hk : 0 < k) (hkn : k ≤ n) :
  ∃ S : Finset (Fin n), S.card = k ∧
  ∀ T : Finset (Fin n), T.card = k → |∑ i in T, x i| ≤ |∑ i in S, x i| := by
  sorry









theorem theorem_830473_problem
  {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  (f : E × F → ℝ)
  (h : F → ℝ)
  (hf_conv : ConvexOn ℝ Set.univ f)
  (h_def : ∀ y, h y = sInf (Set.range (fun x => f (x, y))))
  (h_bdd : ∀ y, BddBelow (Set.range (fun x => f (x, y)))) :
  ConvexOn ℝ Set.univ h := by
  sorry



theorem theorem_830573_problem {X : Type*} [TopologicalSpace X] (M : Set X)
  (h : ¬ Dense M) :
  ∃ x, x ∉ M ∧ ∃ U, IsOpen U ∧ x ∈ U ∧ U ∩ M = ∅ := by
  sorry



theorem theorem_830581_problem 
  (D : Set (ℤ × ℤ))
  (R : Set ℝ)
  (f : D → ℝ)
  (F : ℝ → Set D)
  (h_def : ∀ t, F t = {p : D | f p ≤ t}) :
  ∀ t₁ ∈ R, ∀ t₂ ∈ R, t₁ ≤ t₂ → F t₁ ⊆ F t₂ := by
  sorry







theorem theorem_830561_problem (n : ℕ) :
  Fintype.card { σ : Equiv (Fin (2 * n)) (Fin n × Fin 2) //
    ∀ i : Fin n, σ.symm (i, 0) < σ.symm (i, 1) } =
  n.factorial * (2 * n - 1).doubleFactorial := by
  sorry





theorem theorem_831267_problem (x : ℕ → ℝ) 
  (h_pos : ∀ n, 0 < x n) 
  (h_lim : Filter.Tendsto x Filter.atTop (nhds 0)) :
  ∀ ε > 0, ∃ N, ∀ n ≥ N, 0 < x n ∧ x n < ε := by
  sorry











theorem theorem_831425_problem
  (A : Type*) [CommRing A]
  (C : ℕ → Type*) [∀ p, AddCommGroup (C p)] [∀ p, Module A (C p)]
  (σ : ∀ p, C p)
  (h_free : ∀ p, ∃ b : Basis Unit A (C p), b () = σ p) :
  ∀ p, ∃ φ : C p ≃ₗ[A] A, φ (σ p) = 1 := by
  sorry

theorem theorem_831234_problem (k : ℕ) (hk : k > 0) :
  let basis : Fin k → (Fin k → ℕ) := fun i => Pi.single i 1
  ∀ n : Fin k → ℕ, ∃! a : Fin k → ℕ, n = ∑ i : Fin k, a i • basis i := by
  sorry









theorem theorem_831208_problem (m : ℝ) (k : ℕ) (hm : m > 0) :
  Filter.Tendsto (fun n : ℕ => (Nat.choose n k : ℝ) * (m / (n : ℝ)) ^ k * (1 - m / (n : ℝ)) ^ (n - k))
    Filter.atTop (nhds (m ^ k * Real.exp (-m) / (Nat.factorial k : ℝ))) := by
  sorry

theorem theorem_831213_problem
  (T : (ℝ → ℝ) → ℝ)
  (hT : ∀ φ : ℝ → ℝ, ContDiff ℝ ⊤ φ → HasCompactSupport φ → T φ = φ 0)
  (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f)
  (φ : ℝ → ℝ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ) :
  T (f * φ) = f 0 * φ 0 := by
  sorry

