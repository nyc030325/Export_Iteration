import Mathlib
import Mathlib.Tactic

theorem theorem_848490_problem (S : Type*) [Infinite S] :
  Cardinal.mk (Setoid S) = (2 : Cardinal) ^ Cardinal.mk S := by
  sorry



theorem theorem_848351_problem (n : ℕ) (g : (Fin n → ℝ) → ℝ)
  (hg : ContDiff ℝ ⊤ g) (x : Fin n → ℝ) :
  ∃ χ : Fin n → (Fin n → ℝ) → ℝ, g x = g 0 + ∑ i, x i * χ i x := by
  sorry



theorem theorem_848537_problem (z : ℂ) : Complex.exp z ≠ 0 := by
  sorry









theorem theorem_848770_problem (c₁ c₂ : ℝ) (u : ℝ → ℝ)
  (h_diff : Differentiable ℝ u)
  (h_ode : ∀ r, deriv u r - 4 * u r = Real.exp (3 * r + c₁ + c₂)) :
  ∃ c₃ : ℝ, ∀ r, u r = c₃ * Real.exp (4 * r) + Real.exp (4 * r + c₁ + c₂) * (1 - Real.exp (-r)) := by
  sorry

theorem theorem_848926_problem (a b n y : ℤ) :
  (Nat.choose (b + n + y + 1).toNat (a + y + 1).toNat : ℤ) -
  ((Nat.choose (b + n + y + 1).toNat (a + y + 1).toNat : ℤ) -
   (Nat.choose (b + n + y + 1).toNat (a + y + 1).toNat : ℤ)) =
  (Nat.choose (b + n + y + 1).toNat (a + y + 1).toNat : ℤ) := by
  sorry

theorem theorem_848909_problem (a b : ℕ → ℝ)
  (h₁ : Summable (fun k => (a k) ^ 2))
  (h₂ : Summable (fun k => (b k) ^ 2)) :
  Summable (fun k => a k * b k) := by
  sorry



theorem theorem_848729_problem 
  {α : Type*} 
  (I : α → α → Prop) 
  (D v : α → α) 
  (self_referential : α → Prop) 
  (h_symm : Symmetric I) 
  (a : α) 
  (h_not_sr : ¬ self_referential a) : 
  I a (D a) ∧ I (D a) (v a) := by
  sorry

theorem theorem_848876_problem
  (m n : ℕ)
  (c : Fin n → ℝ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (j : Fin n)
  (y : Fin m → ℝ)
  -- The problem implies we are at a step in the simplex method, so a feasible solution exists
  (h_feas : ∃ x : Fin n → ℝ, A.mulVec x ≤ b ∧ 0 ≤ x)
  -- y are the dual variables for Ax ≤ b, implying non-negativity
  (h_dual_nonneg : 0 ≤ y)
  -- The corresponding column A_j satisfies A_j < 0 (all entries strictly negative)
  (h_col_neg : ∀ i, A i j < 0)
  -- The reduced cost c̄_j = c_j - yᵀA_j is negative
  (h_rc_neg : c j - Matrix.dotProduct y (fun i => A i j) < 0) :
  -- The objective function is unbounded below
  ∀ M : ℝ, ∃ x : Fin n → ℝ, A.mulVec x ≤ b ∧ 0 ≤ x ∧ Matrix.dotProduct c x < M := by
  sorry

theorem theorem_848022_problem
  (R : ℝ) (hR : 0 < R)
  (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.closedBall 0 R))
  (M : ℝ) (hM : M = sSup ((fun z => Complex.abs (f z)) '' Metric.closedBall 0 R))
  (m : ℝ) (hm : m = sSup ((fun z => (f z).re) '' Metric.closedBall 0 R))
  (r : ℝ) (hr_nonneg : 0 ≤ r) (hr_lt : r < R) :
  sSup ((fun z => Complex.abs (f z)) '' Metric.closedBall 0 r) ≤
    (2 * r * M) / (R + r) + ((R - r) / (R + r)) * m := by
  sorry



theorem theorem_848814_problem (a b c : ℝ) :
  (2 * |a| + 2 * |b| + 2 * |c|) - (|a + b| + |b + c| + |a + c|) + 3 * |a + b + c| ≥ |a| + |b| + |c| := by
  sorry

theorem theorem_849091_problem (αs : List Prop) (α_n : Prop) :
  List.foldr (· → ·) α_n αs ↔ (List.foldr (· ∧ ·) True αs → α_n) := by
  sorry

theorem theorem_849291_problem 
  (D : Set (ℝ × ℝ))
  (Area : ℝ)
  (PathIntegral : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ)
  -- Condition 1: Definition of Area as the double integral of 1 over D
  (h_area : Area = ∫ p in D, (1 : ℝ))
  -- Condition 2: Green's Theorem holds for this domain and path integral operator
  (h_green : ∀ (P Q : ℝ → ℝ → ℝ), 
    (∀ p ∈ D, DifferentiableAt ℝ (fun x ↦ Q x p.2) p.1) →
    (∀ p ∈ D, DifferentiableAt ℝ (fun y ↦ P p.1 y) p.2) →
    PathIntegral P Q = ∫ p in D, (deriv (fun x ↦ Q x p.2) p.1 - deriv (fun y ↦ P p.1 y) p.2)) :
  -- Question: Prove the Area formula
  Area = (1 / 2 : ℝ) * PathIntegral (fun x y ↦ -y) (fun x y ↦ x) := by
  sorry





theorem theorem_849522_problem
  (n : ℕ) (hn : n > 0)
  (S : Set (Fin n → ℝ))
  (hS : S = {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1})
  (u : Fin n → ℝ)
  (hu_val : u = fun _ ↦ 1 / (n : ℝ))
  (hu_mem : u ∈ S)
  (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
  (hd_nonneg : ∀ p q, p ∈ S → q ∈ S → 0 ≤ d p q)
  (hd_eq_zero : ∀ p q, p ∈ S → q ∈ S → (d p q = 0 ↔ p = q))
  (p_star : Fin n → ℝ)
  (hp_star : p_star ∈ S)
  (h_min : ∀ q, q ∈ S → d p_star u ≤ d q u) :
  p_star = u := by
  sorry









theorem theorem_850272_problem
  {Formula Constant Variable : Type}
  (is_logical_axiom : Formula → Prop)
  (occurs : Constant → Formula → Prop)
  (is_substitutable : Variable → Constant → Formula → Prop)
  (subst_const : Formula → Constant → Variable → Formula)
  (α : Formula)
  (c : Constant)
  (y : Variable)
  (h_axiom : is_logical_axiom α)
  (h_occ : occurs c α)
  (h_sub : is_substitutable y c α) :
  is_logical_axiom (subst_const α c y) := by
  sorry







theorem theorem_849991_problem {X : Type*} [TopologicalSpace X] (H : Set X) (x : X) :
  x ∈ closure H ↔ ∀ U : Set X, IsOpen U → x ∈ U → (U ∩ H).Nonempty := by
  sorry





theorem theorem_850314_problem :
  ∀ z : ℝ, ∃ x y : ℝ, x ≠ 0 ∧ z = Real.exp (x + y) * Real.arctan (y / x) := by
  sorry



theorem theorem_849917_problem
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (A : E → ℝ) (B : F → E) (c : F)
  (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B) :
  iteratedFDeriv ℝ 2 (A ∘ B) c =
  (iteratedFDeriv ℝ 2 A (B c)).compContinuousLinearMap (fun _ ↦ fderiv ℝ B c) +
  (fderiv ℝ A (B c)).compContinuousMultilinearMap (iteratedFDeriv ℝ 2 B c) := by
  sorry

theorem theorem_849668_problem (n : ℕ) (q : ℝ)
  (hn : n > 2)
  (hq : q > n) :
  ((n : ℝ) * (q - 2)) / (q * ((n : ℝ) - 2)) > 1 := by
  sorry







theorem theorem_850613_problem
  (S : Type*) [Finite S]
  (prec : S → S → Prop)
  (h_trans : Transitive prec)
  (h_irrefl : Irreflexive prec) :
  ¬ ∃ b : ℕ → S, ∀ n, prec (b (n + 1)) (b n) := by
  sorry



theorem theorem_850444_problem (a : ℕ → ℝ)
  (h : ∀ n, n ≥ 1 → a n = (2 : ℝ) ^ n / (8 : ℝ) ^ (n + 2) - 1 / (2 * (n : ℝ))) :
  ¬ Summable (fun n ↦ a (n + 1)) := by
  sorry

theorem theorem_850769_problem
  (hbar : ℝ)
  (ψ : ℝ → ℂ)
  (h_diff : Differentiable ℝ ψ)
  -- The integral term arising from the resolution of identity and the kernel of P
  -- representing ∫ (∂/∂x' δ(x'-x)) ψ(x) dx
  (integral_term : ℝ → ℂ)
  -- The sifting property of the Dirac delta derivative as described in the problem context
  (h_sifting : ∀ x, integral_term x = deriv ψ x)
  -- The action of P on ψ defined via the integral representation (factoring out -iħ)
  (P_action : ℝ → ℂ)
  (h_P_def : ∀ x, P_action x = -I * (hbar : ℂ) * integral_term x) :
  -- Conclusion: The action matches the momentum operator formula
  ∀ x, P_action x = -I * (hbar : ℂ) * deriv ψ x := by
  sorry







theorem theorem_851083_problem (S : Type*) :
  ¬ ∃ f : S → Set S, Function.Surjective f := by
  sorry

theorem theorem_851007_problem (f g : ℝ → ℝ)
  (h_f_zero : ∀ t < 0, f t = 0)
  (h_g_zero : ∀ t < 0, g t = 0)
  (h_f_nonneg : ∀ t, 0 ≤ f t)
  (h_g_nonneg : ∀ t, 0 ≤ g t)
  (t : ℝ) (ht : 0 ≤ t) :
  ∫ τ, f (t - τ) * g τ = ∫ τ in (0)..t, f (t - τ) * g τ := by
  sorry









theorem theorem_851414_problem
  (N : Type*) [Fintype N] [DecidableEq N]
  (A : Finset (N × N))
  (t : N)
  (f : N → N → ℝ)
  (e : N → N → ℝ)
  (E : N → ℝ)
  (h_feasible : ∀ i : N, i ≠ t → ∑ arc in A.filter (λ x => x.1 = i), f arc.1 arc.2 * e arc.1 arc.2 ≤ E i) :
  ∀ i : N, i ≠ t → ∑ arc in A.filter (λ x => x.1 = i), f arc.1 arc.2 * e arc.1 arc.2 ≤ E i := by
  sorry

theorem theorem_851221_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  -- Conditions:
  -- We assume a predicate describing the physical law (Keplerian motion/ODE)
  (is_keplerian : (ℝ → V) → Prop)
  -- E is the Earth's orbit, O is the object's orbit
  (E O : ℝ → V)
  -- Three distinct observation times (modeled as a function from Fin 3)
  (t : Fin 3 → ℝ)
  -- Conditions from the problem statement
  (hO : is_keplerian O)
  (hE : is_keplerian E) :
  -- Conclusion: The Earth's orbit E satisfies the orbit determination system.
  -- The system requires the solution to:
  -- 1. Satisfy the dynamic laws (is_keplerian)
  -- 2. Match the observations (be collinear with E and O at times t_i)
  is_keplerian E ∧ 
  (∀ i : Fin 3, ∃ ρ : ℝ, E (t i) = E (t i) + ρ • (O (t i) - E (t i))) := by
  sorry

theorem theorem_851595_problem
  {α β : Type*} [MetricSpace α] [MetricSpace β]
  (F : ℕ → α → β) (f : α → β)
  (h_cont : ∀ n, Continuous (F n))
  (h_unif : TendstoUniformly F f Filter.atTop) :
  Continuous f := by
  sorry









theorem theorem_851978_problem :
  Summable (fun n : ℕ => (1 : ℝ) / (Nat.nth Nat.Prime (Nat.nth Nat.Prime n - 1))) := by
  sorry





theorem theorem_851552_problem
  (Ω : Type*)
  (ar : Ω → ℕ)
  (A : Type*)
  (ops : (ω : Ω) → (Fin (ar ω) → A) → A) :
  ∃! a : (Σ ω, Fin (ar ω) → A) → A,
    ∀ (ω : Ω) (x : Fin (ar ω) → A), a ⟨ω, x⟩ = ops ω x := by
  sorry





theorem theorem_851678_problem (n : ℕ) (b : ℂ) (z : ZMod n → ℂ)
  (hn : n ≥ 2)
  (hb : b ^ n ≠ 1)
  (h : ∀ i, z i = (1 - b) / (n : ℂ) + b * z (i + 1)) :
  ∀ i, z i = 1 / (n : ℂ) := by
  sorry

theorem theorem_851744_problem
  {S : Type*} [Fintype S] [DecidableEq S]
  (Q : S → S → ℝ)
  (M : S → S → ℝ)
  (i j : S)
  (h_qii_neg : Q i i < 0)
  (h_qik_nonneg : ∀ k, k ≠ i → Q i k ≥ 0)
  (sojourn_mean : ℝ)
  (h_sojourn : sojourn_mean = -1 / Q i i)
  (p : S → S → ℝ)
  (h_p : ∀ k, k ≠ i → p i k = - Q i k / Q i i)
  (h_first_step_decomp : M i j = sojourn_mean + ∑ k in Finset.univ.erase i, (p i k) * (M k j)) :
  M i j = -1 / Q i i + ∑ k in Finset.univ.erase i, (-Q i k / Q i i) * M k j := by
  sorry

theorem theorem_852073_problem
  (n : ℕ)
  (X : Set (Fin n → ℝ))
  (h_compact : IsCompact X)
  (h_convex : Convex ℝ X)
  (h_nonempty : X.Nonempty)
  (f : X → X)
  (h_cont : Continuous f) :
  ∃ x : X, f x = x := by
  sorry



theorem theorem_852462_problem (a : ℕ → ℝ)
  (h_rec : ∀ n, 1 ≤ n → a n = (n : ℝ) * a (n - 1) + (n - 1).factorial) :
  ∀ n, a n = (n.factorial : ℝ) * (a 0 + ∑ k in Finset.Ico 1 (n + 1), 1 / (k : ℝ)) := by
  sorry



theorem theorem_852402_problem {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  (bV1 bV2 : Basis n K V)
  (bW1 bW2 : Basis m K W)
  (T : V →ₗ[K] W)
  (P : Matrix n n K)
  (Q : Matrix m m K)
  (hP : P = bV2.toMatrix bV1)
  (hQ : Q = bW2.toMatrix bW1) :
  LinearMap.toMatrix bV2 bW2 T = Q⁻¹ * LinearMap.toMatrix bV1 bW1 T * P := by
  sorry

theorem theorem_852435_problem (T : ℝ) :
  Real.exp (-T / 8300) * Real.exp (2.996 * T / 1000) = 
  Real.exp (T / 1000 * (2.996 - 1 / 8.3)) := by
  sorry

theorem theorem_849256_problem (f : ℝ → ℝ) (x : ℝ)
  (h_def : ∀ y, f y = Real.arcsin (Real.sin y))
  (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
  deriv f x = 1 := by
  sorry









theorem theorem_853017_problem
  (b : ℕ → ℕ → ℕ)
  (h_boundary_0 : ∀ n, b n 0 = 1)
  (h_boundary_n : ∀ n, b n n = 1)
  (h_recurrence : ∀ n k, 1 ≤ k → k ≤ n - 1 → b n k = b (n - 1) (k - 1) + b (n - 1) k) :
  ∀ n k, k ≤ n → b n k = Nat.factorial n / (Nat.factorial k * Nat.factorial (n - k)) := by
  sorry







theorem theorem_853099_problem (t : ℝ)
  (x₁ q : ℝ → ℝ)
  (h₁ : x₁ = fun t => 1 / (Real.sin t + Real.cos t))
  (h₂ : q = fun t => (3 - 2 * Real.sin t * Real.cos t) / (1 + 2 * Real.sin t * Real.cos t))
  (h₃ : Real.sin t + Real.cos t ≠ 0) :
  deriv (deriv x₁) t = q t * x₁ t := by
  sorry

theorem theorem_852923_problem (n : ℕ) :
  (2 : ℝ) ^ ((n : ℝ) / 2) ≤ ∑ k in Finset.range (n + 1), Real.sqrt ((Nat.choose n k) : ℝ) ∧
  ∑ k in Finset.range (n + 1), Real.sqrt ((Nat.choose n k) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) * Real.sqrt ((n : ℝ) + 1) := by
  sorry



theorem theorem_853044_problem (α : ℝ)
  (h_irr : Irrational α)
  (h_not_root : ∀ (n : ℕ) (m : ℤ), n > 0 → α ^ n ≠ (m : ℝ)) :
  ¬ ∃ (N : ℕ) (p : Fin N → ℕ) (q : Fin N → ℚ),
    (∀ i, Nat.Prime (p i)) ∧ α = ∏ i, (p i : ℝ) ^ (q i : ℝ) := by
  sorry













theorem theorem_853781_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → E) (p : E)
  (h_smooth : ContDiff ℝ ⊤ f)
  (h_jacobian : IsUnit (fderiv ℝ f p)) :
  ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
  ∃ V : Set E, IsOpen V ∧ f p ∈ V ∧
  ∃ g : E → E, ContDiffOn ℝ ⊤ g V ∧
  Set.MapsTo f U V ∧ Set.MapsTo g V U ∧
  (∀ x ∈ U, g (f x) = x) ∧
  (∀ y ∈ V, f (g y) = y) := by
  sorry









theorem theorem_853680_problem (f : ℝ → ℝ) (a b : ℝ)
  (h_diff : ContDiff ℝ 1 f)
  (h_ord : a < b)
  (h_eq : f a = f b) :
  ∃ c ∈ Set.Ioo a b, deriv f c = 0 := by
  sorry

