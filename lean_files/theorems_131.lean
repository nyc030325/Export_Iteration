import Mathlib
import Mathlib.Tactic

theorem theorem_710455_problem (D X : Type*)
  [TopologicalSpace D] [DiscreteTopology D]
  [TopologicalSpace X] :
  Function.Bijective (ContinuousMap.toFun : ContinuousMap D X → (D → X)) := by
  sorry







theorem theorem_709239_problem (g : ℕ → ℝ)
  (h0 : g 0 = 1)
  (h1 : g 1 = 2)
  (h_rec : ∀ n ≥ 2, g n = 2 * g (n - 1) + (∑ k in Finset.range (n - 1), g k) + 1) :
  ∀ n ≥ 1, g n = (2 / Real.sqrt 5) * (((3 + Real.sqrt 5) / 2) ^ n - ((3 - Real.sqrt 5) / 2) ^ n) := by
  sorry





theorem theorem_711075_problem (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hf : Continuous f)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  (ha_sum : Summable a) :
  Summable (fun n => |a n * f (Real.sin (n : ℝ))|) := by
  sorry



theorem theorem_711003_problem
  (N : ℕ)
  (a b : Fin N → ℝ) :
  let a_norm := Real.sqrt (∑ i, (a i)^2)
  Matrix.dotProduct a (Matrix.mulVec (Matrix.diagonal b) a) = ∑ i, (a i)^2 * (b i) ∧
  ∑ i, (a i)^2 * (b i) = a_norm^2 * (∑ i, (b i) * ((a i)^2 / a_norm^2)) := by
  sorry















theorem theorem_711485_problem 
  -- Abstract types representing the formal system and its components
  {Statement : Type}
  {Theory : Type}
  -- Relations and mappings defined in the problem
  (Provable : Theory → Statement → Prop)
  (Consistent : Theory → Prop)
  (RecursivelyEnumerable : Theory → Prop)
  (IncludesArithmetic : Theory → Prop)
  (Con : Theory → Statement)
  -- The specific theory T
  (T : Theory)
  -- Conditions on T
  (h1 : Consistent T)
  (h2 : RecursivelyEnumerable T)
  (h3 : IncludesArithmetic T) :
  -- The conclusion to be proved
  ¬ Provable T (Con T) := by
  sorry

theorem theorem_711315_problem
  (x : ℝ → ℝ)
  (I : Set ℝ)
  (hI : Convex ℝ I)
  (IsExpComposed : (ℝ → ℝ) → Prop)
  (h_comp : IsExpComposed x)
  (h_smooth : ContDiffOn ℝ 2 x I) :
  ∀ t ∈ interior I, derivWithin x (Set.Ici t) t = derivWithin x (Set.Iic t) t := by
  sorry

theorem theorem_711435_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (h_dim : FiniteDimensional ℂ H) :
  let σ_strong := ⨆ (x : H), TopologicalSpace.induced (fun (T : H →L[ℂ] H) ↦ T x) inferInstance
  @Continuous (H →L[ℂ] H) (H →L[ℂ] H) σ_strong σ_strong ContinuousLinearMap.adjoint := by
  sorry





theorem theorem_711630_problem :
  ∃ φ : FreeGroup Unit ≃* Multiplicative ℤ,
  ∀ n : ℤ, φ (FreeGroup.of () ^ n) = Multiplicative.ofAdd n := by
  sorry

theorem theorem_711977_problem (m n : ℕ) :
  ∑ k in Finset.range (n + 1), Nat.choose m k * Nat.choose n (n - k) = Nat.choose (m + n) n := by
  sorry

theorem theorem_711608_problem
  (A B S : ℕ → Set ℕ)
  (hA : ∀ n, A n = {k | 10 * (n - 1) + 1 ≤ k ∧ k ≤ 10 * n})
  (hB : ∀ n, B n = {n})
  (hS : ∀ n, S n = (⋃ i ∈ Finset.range n, A (i + 1)) \ (⋃ i ∈ Finset.range n, B (i + 1))) :
  ∀ x, ∃ N, ∀ n ≥ N, x ∉ S n := by
  sorry



theorem theorem_711382_problem
  (n : ℕ)
  (K : Type*) [Field K]
  (a b : K)
  (X A : Matrix (Fin n) (Fin n) K)
  (ha : a ≠ 0)
  (hX : ∀ i j, X i j = if i = j then 1
                       else if (i : ℤ) - j = 1 ∨ (j : ℤ) - i = 1 then b / a
                       else 0)
  (hX_inv : IsUnit X)
  (hA : A = a • X) :
  IsUnit A ∧ A⁻¹ = (a⁻¹) • X⁻¹ := by
  sorry

















theorem theorem_711257_problem (r_i w_b : EuclideanSpace ℝ (Fin 3)) :
  crossProduct r_i (crossProduct w_b (crossProduct w_b r_i)) =
  crossProduct w_b (crossProduct r_i (crossProduct w_b r_i)) := by
  sorry

theorem theorem_711986_problem
  {𝕜 : Type*} [NormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (A : X →L[𝕜] X)
  (norm_A_1 : ℝ)
  (h1 : norm_A_1 = sSup {r | ∃ x : X, ‖x‖ = 1 ∧ r = ‖A x‖})
  (norm_A_2 : ℝ)
  (h2 : norm_A_2 = sSup {r | ∃ x : X, ‖x‖ ≤ 1 ∧ r = ‖A x‖}) :
  norm_A_1 = norm_A_2 := by
  sorry



theorem theorem_712424_problem {R : Type*} [CommRing R] [IsDomain R] (f : Polynomial R)
  (h : ∃ g : Polynomial R, f * g = 1) :
  ∃ r : R, f = Polynomial.C r := by
  sorry





theorem theorem_712270_problem (X : Type*) (A : Set X) (C : Set (Set X)) :
  MeasurableSpace.generateFrom { S : Set A | ∃ B ∈ C, S = Subtype.val ⁻¹' B } =
  (MeasurableSpace.generateFrom C).comap Subtype.val := by
  sorry

theorem theorem_712590_problem
  (u v : ℝ → ℝ)
  (U V u_z v_z : ℂ → ℂ)
  (hU_anal : Differentiable ℂ U)
  (hV_anal : Differentiable ℂ V)
  (hu_z_anal : Differentiable ℂ u_z)
  (hv_z_anal : Differentiable ℂ v_z)
  (hU_eq : ∀ (x : ℝ), U x = u x)
  (hV_eq : ∀ (x : ℝ), V x = v x)
  (hu_z_eq : ∀ (x : ℝ), u_z x = u x)
  (hv_z_eq : ∀ (x : ℝ), v_z x = v x) :
  (∀ z, u_z z = U z) ∧ (∀ z, v_z z = V z) := by
  sorry









theorem theorem_712375_problem (k l K L m : ℝ)
  (hk_pos : k > 0) (hl_pos : l > 0)
  (hK_pos : K > 0) (hL_pos : L > 0)
  (hm_def : m = K / L)
  (hk_sq : k^2 = ((3 + m)^3 * (m - 1)) / (16 * m^3))
  (hl_sq : l^2 = ((m - 1)^3 * (3 + m)) / (16 * m)) :
  (2 * k * K / Real.pi + 6 * l * L / Real.pi) * (2 * K / Real.pi + 6 * L / Real.pi) =
  4 * (2 * k * K / Real.pi) * (2 * K / Real.pi) := by
  sorry





theorem theorem_712824_problem (f : ℝ × ℝ → ℝ) (a b : ℝ)
  (hf : ContDiff ℝ 2 f)
  (h_crit : fderiv ℝ f (a, b) = 0)
  (fxx : ℝ := iteratedFDeriv ℝ 2 f (a, b) ![((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))])
  (fyy : ℝ := iteratedFDeriv ℝ 2 f (a, b) ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))])
  (fxy : ℝ := iteratedFDeriv ℝ 2 f (a, b) ![((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))])
  (h_det : fxx * fyy - fxy ^ 2 < 0) :
  ¬ IsLocalMin f (a, b) ∧ ¬ IsLocalMax f (a, b) := by
  sorry

theorem theorem_712868_problem 
  (V : Type*) 
  (Embedding : Type*) 
  (CyclicOrder : Type*) 
  (C : Embedding → V → CyclicOrder) 
  (E₁ E₂ : Embedding) :
  E₁ ≠ E₂ ↔ ∃ v : V, C E₁ v ≠ C E₂ v := by
  sorry





theorem theorem_712941_problem
  {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M]
  (n : ℕ)
  (g : Fin (n + 1) → M)
  (h_gen : Submodule.span R (Set.range g) = ⊤)
  (h_comb : g (Fin.last n) ∈ Submodule.span R (g '' {i : Fin (n + 1) | i ≠ Fin.last n}))
  (h_distinct : g (Fin.last n) ∉ g '' {i : Fin (n + 1) | i ≠ Fin.last n}) :
  ¬ ((Submodule.span R (Set.range g) = ⊤) ∧ 
     (∀ T : Set M, T ⊂ Set.range g → Submodule.span R T ≠ ⊤)) := by
  sorry

theorem theorem_712823_problem (x y z : ℕ)
  (hx : x > 0) (hy : y > 0) (hz : z > 0)
  (hxy : x ≥ y) (hyz : y ≥ z)
  (hdiv : x^2 ∣ (x^3 + y^3 + z^3)) :
  x ≤ 108 := by
  sorry

theorem theorem_713127_problem
  (g : ℝ → ℝ)
  (hg : Continuous g)
  (f : ℝ → ℝ)
  (h_pos : ∀ x, 0 ≤ x → f x = ∫ t in (0 : ℝ)..x, g t)
  (h_neg : ∀ x, x < 0 → f x = ∫ t in x..(0 : ℝ), g t) :
  Continuous f := by
  sorry





theorem theorem_713986_problem (n : ℕ) (h : 1 ≤ n) (x : ℝ) :
  deriv (fun x => (Real.cos x) ^ (n - 1) * Real.sin x / n) x =
  (Real.cos x) ^ n - ((n : ℝ) - 1) / n * (Real.cos x) ^ (n - 2) := by
  sorry

theorem theorem_713760_problem
  (a x θ : ℝ)
  (n : ℕ)
  (s : ℂ)
  (ha : 0 < a)
  (hn : 0 < n)
  (hs : s = x + θ * Complex.I) :
  Complex.abs ((a : ℂ) ^ (s - 1) * Complex.exp (-(n : ℂ) * (a : ℂ))) = 
  Complex.abs ((a : ℂ) ^ ((x : ℂ) - 1) * Complex.exp (-(n : ℂ) * (a : ℂ))) := by
  sorry

theorem theorem_713924_problem
  (L : ℕ)
  (Ms : Fin L → Matrix (Fin 2) (Fin 2) ℝ)
  (norm : Matrix (Fin 2) (Fin 2) ℝ → ℝ)
  (h_norm_pos : ∀ i, 0 < norm (Ms i))
  (k : ℝ := ∏ i, norm (Ms i))
  (As : Fin L → Matrix (Fin 2) (Fin 2) ℝ := fun i => (norm (Ms i))⁻¹ • Ms i)
  (A : Matrix (Fin 2) (Fin 2) ℝ := (List.ofFn As).prod)
  (M : Matrix (Fin 2) (Fin 2) ℝ := (List.ofFn Ms).prod)
  (h_det_M_pos : 0 < (1 + M).det)
  (h_det_A_pos : 0 < (k⁻¹ • 1 + A).det) :
  Real.log (1 + M).det = 2 * Real.log k + Real.log (k⁻¹ • 1 + A).det := by
  sorry





theorem theorem_713558_problem (t r : ℝ) (P : ℝ → ℝ)
  (ht : 0 < t) (hr : 0 < r)
  (hP_nonneg : ∀ x, 0 ≤ P x)
  (hP_antitone : Antitone P) :
  P t ≤ ∑ k in Finset.range (Nat.floor (t / r) + 1), P (k * r) := by
  sorry

theorem theorem_713787_problem
  -- Context: Domain of problems and Complexity Classes
  (DecisionProblem : Type)
  (P NP : Set DecisionProblem)
  (poly_time_reduce : DecisionProblem → DecisionProblem → Prop)
  -- Standard axioms of Complexity Theory assumed in the problem context
  (h_P_subset_NP : P ⊆ NP)
  (h_P_closed_under_reduction : ∀ (L1 L2 : DecisionProblem), poly_time_reduce L1 L2 → L2 ∈ P → L1 ∈ P)
  -- Definition of NP-complete provided in the context/solution
  (NP_complete : DecisionProblem → Prop)
  (h_NP_complete_def : ∀ L, NP_complete L ↔ L ∈ NP ∧ ∀ L' ∈ NP, poly_time_reduce L' L)
  -- Specific Problem Conditions
  (L : DecisionProblem)
  (h_L_NPC : NP_complete L)
  (h_L_in_P : L ∈ P) :
  -- Conclusion
  P = NP := by
  sorry

theorem theorem_713554_problem {F : Type*} [Field F] (p : Polynomial F)
  (hp : p.degree = 2 ∨ p.degree = 3) :
  Irreducible p ↔ ¬ ∃ a : F, p.eval a = 0 := by
  sorry

theorem theorem_714181_problem (n : ℕ) (a : Fin n → ℝ) (m : ℝ)
  (hn : 0 < n)
  (ha : ∀ i, 0 < a i)
  (hm : 1 < m) :
  (∑ i, a i) ^ m ≤ (n : ℝ) ^ (m - 1) * ∑ i, (a i) ^ m := by
  sorry





theorem theorem_714507_problem (f : ℝ → ℝ) (h : Monotone f) :
  Set.Countable {x | ¬ ContinuousAt f x} := by
  sorry

theorem theorem_714697_problem :
  ∃ (X Y : Type) (tX : TopologicalSpace X) (tY : TopologicalSpace Y)
    (f : X → Y) (U : Set X),
    @Continuous X Y tX tY f ∧ @IsOpen X tX U ∧ ¬ @IsOpen Y tY (f '' U) := by
  sorry

theorem theorem_714476_problem
  (R : Type*) [Ring R]
  (S : Set R) (hS : Subring.closure S = ⊤)
  (f : S → R)
  (h_add : ∀ (x y : S) (h : (x : R) + y ∈ S), f ⟨x + y, h⟩ = f x + f y)
  (h_mul : ∀ (x y : S) (h : (x : R) * y ∈ S), f ⟨x * y, h⟩ = f x * f y) :
  ∃! F : R →+* R, ∀ s : S, F s = f s := by
  sorry

theorem theorem_714415_problem
  (V : Type*) [Fintype V] [DecidableEq V]
  (G : SimpleGraph V)
  (n : ℕ) (hn : n > 0)
  (T : G ≃g G)
  (hT : orderOf T = n) :
  ∃ H : Subgroup (G ≃g G), Nonempty (H ≃* Multiplicative (ZMod n)) := by
  sorry





theorem theorem_714824_problem (k : ℕ) :
  Filter.Tendsto (fun (n : ℕ) => (n : ℝ) ^ k / (3 : ℝ) ^ Real.sqrt n) Filter.atTop (nhds 0) := by
  sorry







theorem theorem_714438_problem (x1 x2 y1 y2 : ℝ) 
  (h1 : y1 > y2) (h2 : y2 > 0) : 
  x1^2 / y1 - x2^2 / y2 ≤ (x1 - x2)^2 / (y1 - y2) := by
  sorry

theorem theorem_714646_problem {G : Type*} [Group G] :
  let μ : G × G → G := fun p => p.1 * p.2
  let η : PUnit → G := fun _ => 1
  let Δ : G → G × G := fun x => (x, x)
  let ε : G → PUnit := fun _ => PUnit.unit
  let s : G → G := fun x => x⁻¹
  μ ∘ (Prod.map id s) ∘ Δ = η ∘ ε := by
  sorry



theorem theorem_714279_problem (n : ℕ) (a : Fin n → ℤ)
  (h : ∀ i j, i ≠ j → Int.gcd (a i) (a j) = 1) :
  ∃ x : Fin n → ℤ, ∀ k, Int.gcd (∏ j in Finset.univ.erase k, a j) (a k) = 1 := by
  sorry





















theorem theorem_715489_problem
  (n : ℕ)
  (R S : Type*) [CommRing R] [CommRing S]
  (f_star : R →+* S)
  (c : ℕ → R)
  (x : Fin n → S)
  -- Condition: Relationship between Chern classes and Chern roots (Splitting Principle)
  (h_map : ∀ k, f_star (c k) = MvPolynomial.eval x (MvPolynomial.esymm (Fin n) S k))
  -- Condition: The first n-1 Chern classes vanish
  (h_vanish : ∀ k, 1 ≤ k ∧ k < n → c k = 0) :
  -- Question: The symmetric polynomials of the roots vanish
  ∀ k, 1 ≤ k ∧ k < n → MvPolynomial.eval x (MvPolynomial.esymm (Fin n) S k) = 0 := by
  sorry

theorem theorem_715792_problem (a : ℕ → ℝ)
  (h_a : ∀ n, a n = if IsSquare n then 1 else 0)
  (x : ℝ)
  (h_x : x = ∑' n, if n = 0 then 0 else a n / (10 : ℝ) ^ n) :
  Irrational x := by
  sorry

theorem theorem_715870_problem (F L : Type*) [Field F] [Field L] [Algebra F L]
  (r : L) (h_alg : IsAlgebraic F r) :
  FiniteDimensional.finrank F (IntermediateField.adjoin F {r}) = (minpoly F r).natDegree := by
  sorry





theorem theorem_715858_problem 
  (X : Type*) (τ : TopologicalSpace X)
  (U V : Set X)
  (hU : U ≠ ∅) (hV : V ≠ ∅)
  (hVU : V ⊆ U)
  (τ_U : TopologicalSpace U := TopologicalSpace.induced Subtype.val τ)
  (τ_V : TopologicalSpace V := TopologicalSpace.induced Subtype.val τ)
  (τ' : TopologicalSpace V := TopologicalSpace.induced (fun x : V => (⟨x.1, hVU x.2⟩ : U)) τ_U)
  (h_connected : @ConnectedSpace V τ_V) :
  @ConnectedSpace V τ' := by
  sorry

