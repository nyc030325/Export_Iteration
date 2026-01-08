import Mathlib
import Mathlib.Tactic

theorem theorem_629585_problem
  {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
  (T : V →L[𝕜] V)
  (c : ℕ → 𝕜)
  (v : V)
  (u : 𝕜)
  (h_eigen : T v = u • v) :
  (∑' n : ℕ, c n • (T ^ n)) v = (∑' n : ℕ, c n * u ^ n) • v := by
  sorry

theorem theorem_629475_problem
  {X Y : Type*} [MetricSpace Y]
  (f_n : ℕ → X → Y) (f g : X → Y)
  (h_pointwise : ∀ x, Filter.Tendsto (fun n ↦ f_n n x) Filter.atTop (nhds (f x)))
  (h_uniform : TendstoUniformly f_n g Filter.atTop) :
  f = g := by
  sorry

theorem theorem_629026_problem {R : Type*} [CommRing R]
  {V : Type*} [AddCommGroup V] [Module R V]
  {W : Type*} [AddCommGroup W] [Module R W]
  (T : V →ₗ[R] W) (v w : V) :
  ExteriorAlgebra.map T ((ExteriorAlgebra.ι R v) * (ExteriorAlgebra.ι R w)) =
  (ExteriorAlgebra.ι R (T v)) * (ExteriorAlgebra.ι R (T w)) := by
  sorry



theorem theorem_629401_problem 
  (LP : Type) 
  (IsFeasible : LP → Prop) 
  (P Pc : LP) 
  (h_equiv : IsFeasible P ↔ IsFeasible Pc) 
  (h_infeasible_Pc : ¬ IsFeasible Pc) : 
  ¬ IsFeasible P := by
  sorry



theorem theorem_629545_problem (I : Type*) [Infinite I] :
  ∃ U : Ultrafilter I, Filter.cofinite ≤ U.1 ∧ ∀ x : I, U.1 ≠ Filter.principal {x} := by
  sorry

theorem theorem_629532_problem (z : ℂ) (h : Complex.abs (z - 1) < 2) :
  ∑' n : ℕ, ((n : ℂ) + 1) / 4 * ((-1 : ℂ) / 2) ^ n * (z - 1) ^ n = 1 / (z + 1) ^ 2 := by
  sorry

theorem theorem_629571_problem (D : Set ℝ) (f g : ℝ → ℝ)
  (h : ∀ y_a ∈ D, ∀ y_b ∈ D, y_a ≠ y_b →
    ∀ x₁ x₂ : ℝ, (x₁ * f y_a + x₂ * g y_a = 0 ∧ x₁ * f y_b + x₂ * g y_b = 0) →
    x₁ = 0 ∧ x₂ = 0) :
  ∀ c₁ c₂ : ℝ, (∀ y ∈ D, c₁ * f y + c₂ * g y = 0) → c₁ = 0 ∧ c₂ = 0 := by
  sorry

theorem theorem_629371_problem {α : Type} (a : α) (L : Set (List α))
  (hL : L = { w | ∃ s : List α, s ≠ [] ∧ (∀ c ∈ s, c = a) ∧ w = s ++ s }) :
  L = { w | ∃ n : ℕ, n ≥ 1 ∧ w = List.replicate (2 * n) a } := by
  sorry

theorem theorem_629424_problem
  (n : ℕ)
  (Q : Matrix (Fin n) (Fin n) ℝ)
  (c : Fin n → ℝ)
  (r : ℝ)
  (h_symm : Q.IsSymm)
  (h_psd : Q.PosSemidef)
  (f : (Fin n → ℝ) → ℝ)
  (h_f : ∀ x, f x = (1 / 2 : ℝ) * Matrix.dotProduct x (Matrix.mulVec Q x) + Matrix.dotProduct c x + r) :
  ConvexOn ℝ Set.univ f := by
  sorry





theorem theorem_628939_problem
  {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
  (π : E → B)
  (U : Set B) (hU : IsOpen U)
  (O : Set B) (hO : IsOpen O)
  (O' : Set E) (hO' : IsOpen O')
  (φ : U → E) -- Local trivialization map (section)
  (ψ : O → O')
  (η : O' → E)
  (φ_inv : E → U) -- Inverse of φ
  (hφ_sec : ∀ u : U, π (φ u) = u) -- φ identifies base point with point in image
  (hφ_inv : ∀ u : U, φ_inv (φ u) = u) -- φ⁻¹ recovers the point u
  (h_img : Set.MapsTo (η ∘ ψ) Set.univ (φ '' Set.univ)) -- The condition η(ψ(O)) ⊆ φ(U)
  :
  let σ : O → U := λ x => φ_inv (η (ψ x))
  ∀ x : O, (σ x : B) = π (η (ψ x)) := by
  sorry

theorem theorem_629862_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
  Polynomial.aeval A (Matrix.charpoly A) = 0 := by
  sorry

theorem theorem_629713_problem (x1 x2 : ℕ) (x c : ℝ)
  (hx1 : 0 < x1) (hx2 : 0 < x2) (hc : 0 < c) :
  14 * c * ((x1 : ℝ) - (x2 : ℝ))^2 + x^2 * (1 + c^2) > 0 := by
  sorry







theorem theorem_629879_problem 
  (a α : ℝ) 
  (ha : 0 < a) 
  (hα : Real.cos α ≠ 0)
  (b : ℝ) (hb : b = (a / 2) * (1 / Real.cos α - 1))
  (e₁ e₂ e₃ : Fin 3 → ℝ)
  (he₁ : e₁ = (1 / Real.sqrt (a^2 + 2 * b^2)) • ![a, b, b])
  (he₂ : e₂ = (1 / Real.sqrt (a^2 + 2 * b^2)) • ![b, a, b])
  (he₃ : e₃ = (1 / Real.sqrt (a^2 + 2 * b^2)) • ![b, b, a]) :
  ((e₁ 0)^2 + (e₁ 1)^2 + (e₁ 2)^2 = 1) ∧ 
  ((e₂ 0)^2 + (e₂ 1)^2 + (e₂ 2)^2 = 1) ∧ 
  ((e₃ 0)^2 + (e₃ 1)^2 + (e₃ 2)^2 = 1) := by
  sorry



theorem theorem_630101_problem (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (P Q : EuclideanSpace ℝ (Fin n))
  (h_diff : Differentiable ℝ f)
  (h_eq : f P = f Q) :
  ∃ Q₀ ∈ segment ℝ P Q, inner (gradient f Q₀) (P - Q) = (0 : ℝ) := by
  sorry







theorem theorem_629892_problem
  (A B : (Fin 3 → ℝ) → (Fin 3 → ℝ))
  (hA : Differentiable ℝ A)
  (hB : Differentiable ℝ B) :
  ∀ p : Fin 3 → ℝ,
    fderiv ℝ B p (A p) = 
    fun i => ∑ j : Fin 3, (A p j) * (fderiv ℝ (fun q => B q i) p (Pi.single j 1)) := by
  sorry





theorem theorem_630426_problem (a : ℕ → ℝ) (c R : ℝ) (hR : R > 0)
  (h : Summable (fun n ↦ |a n * ((c + R) - c) ^ n|) ∨
       Summable (fun n ↦ |a n * ((c - R) - c) ^ n|)) :
  Summable (fun n ↦ |a n * ((c - R) - c) ^ n|) ∧
  Summable (fun n ↦ |a n * ((c + R) - c) ^ n|) := by
  sorry

theorem theorem_630516_problem (U : Set ℝ) (hU : IsOpen U) :
  interior U = ∅ ∨ ¬ (interior U).Countable := by
  sorry





theorem theorem_630522_problem (x y z : ℕ → ℝ) (L : ℝ)
  (hx : Filter.Tendsto x Filter.atTop (nhds L))
  (hy : Filter.Tendsto y Filter.atTop (nhds L))
  (h_weave : ∃ φ ψ : ℕ → ℕ, StrictMono φ ∧ StrictMono ψ ∧ 
    Set.range φ ∪ Set.range ψ = Set.univ ∧ 
    Disjoint (Set.range φ) (Set.range ψ) ∧ 
    z ∘ φ = x ∧ z ∘ ψ = y) :
  Filter.Tendsto z Filter.atTop (nhds L) := by
  sorry





theorem theorem_630603_problem {A : Type*} [NormedRing A] [CompleteSpace A]
  (h_noncomm : ¬ ∀ x y : A, x * y = y * x) :
  ¬ ∃ C : ℝ, C > 0 ∧ ∀ (x y z : A) (M : ℝ), M > 0 → ‖x - y‖ < M → ‖z * x - x * z‖ ≤ C * M := by
  sorry



theorem theorem_630114_problem
  (R : ℝ) (hR : R > 0)
  (A : ℝ × ℝ) (hA : A.1^2 + A.2^2 = R^2)
  (P : ℝ × ℝ) (hP : P = (A.1, -A.2))
  (t : ℝ)
  (Q : ℝ × ℝ) (hQ_on_circle : Q.1^2 + Q.2^2 = R^2)
  (hQ_neq_A : Q ≠ A)
  (hQ_slope_defined : Q.1 ≠ A.1)
  (hQ_slope : (Q.2 - A.2) / (Q.1 - A.1) = t)
  (B C : ℝ × ℝ)
  (hB_on_circle : B.1^2 + B.2^2 = R^2)
  (hC_on_circle : C.1^2 + C.2^2 = R^2)
  (hB_neq_A : B ≠ A)
  (hC_neq_A : C ≠ A)
  (hB_slope_defined : B.1 ≠ A.1)
  (hC_slope_defined : C.1 ≠ A.1)
  (h_slope_prod : ((B.2 - A.2) / (B.1 - A.1)) * ((C.2 - A.2) / (C.1 - A.1)) = t^2)
  (hBC_distinct : B ≠ C) :
  ∃ I : ℝ × ℝ,
    (I.1 * P.2 = I.2 * P.1) ∧ -- I lies on the line OP (O is origin)
    ((I.2 - B.2) * (C.1 - B.1) = (C.2 - B.2) * (I.1 - B.1)) ∧ -- I lies on the line BC
    (I.1 * Q.1 + I.2 * Q.2 = R^2) -- I lies on the tangent to Ω at Q
  := by sorry





theorem theorem_630416_problem
  (P_omega1 P_omega2 : ℝ)
  (lambda_11 lambda_12 lambda_21 lambda_22 : ℝ)
  -- Represent integrals over regions R1 and R2 for class 1 and 2
  (int_R1_p_w1 int_R2_p_w1 : ℝ) 
  (int_R1_p_w2 int_R2_p_w2 : ℝ)
  -- Conditions
  (h_prior : P_omega2 = 1 - P_omega1)
  (h_prob_w1 : int_R1_p_w1 + int_R2_p_w1 = 1)
  (h_prob_w2 : int_R1_p_w2 + int_R2_p_w2 = 1)
  (Risk : ℝ)
  (h_Risk_def : Risk = 
    (lambda_11 * P_omega1 * int_R1_p_w1 + lambda_12 * P_omega2 * int_R1_p_w2) + 
    (lambda_21 * P_omega1 * int_R2_p_w1 + lambda_22 * P_omega2 * int_R2_p_w2)) :
  Risk = lambda_22 + (lambda_12 - lambda_22) * int_R1_p_w2 + 
    P_omega1 * ((lambda_11 - lambda_22) + (lambda_21 - lambda_11) * int_R2_p_w1 - 
    (lambda_12 - lambda_22) * int_R1_p_w2) := by
  sorry



theorem theorem_630634_problem (f : ℝ → ℝ) (x : ℝ)
  (hf : ContDiffAt ℝ ⊤ f x) :
  ∀ n : ℕ, iteratedDeriv n (fun h ↦ f (x + h)) 0 = iteratedDeriv n f x := by
  sorry



theorem theorem_631645_problem
  {Ω : Type*} -- Sample space
  (n : ℕ) [Nonempty (Fin n)] -- n random variables, n >= 1
  (X : Fin n → Ω → ℝ) -- Sequence of random variables
  (a : ℝ) -- Real number threshold
  : {ω : Ω | Finset.univ.sup' Finset.univ_nonempty (fun i ↦ X i ω) > a} =
    ⋃ i, {ω : Ω | X i ω > a} := by
  sorry

theorem theorem_631510_problem (X : Type*) [Nonempty X] (A : Set (Set X))
  (h_algebra : Set.univ ∈ A ∧ (∀ s ∈ A, sᶜ ∈ A) ∧ (∀ s t, s ∈ A → t ∈ A → s ∪ t ∈ A))
  (h_countable_union : ∀ f : ℕ → Set X, (∀ n, f n ∈ A) → (⋃ n, f n) ∈ A) :
  Set.univ ∈ A ∧ (∀ s ∈ A, sᶜ ∈ A) ∧ (∀ f : ℕ → Set X, (∀ n, f n ∈ A) → (⋃ n, f n) ∈ A) := by
  sorry

theorem theorem_631664_problem (a b : ℝ) (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
  (h1 : ∀ n, ContinuousOn (fn n) (Set.Icc a b))
  (h2 : TendstoUniformlyOn fn f atTop (Set.Icc a b)) :
  ContinuousOn f (Set.Icc a b) := by
  sorry











theorem theorem_632047_problem
  (a b : ℝ)
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (f : ℝ → ℝ)
  (hf : Differentiable ℝ f)
  (u : ℝ → ℝ → ℝ)
  (hu : ∀ x y, u x y = f (b * x - a * y)) :
  ∀ x y, a * deriv (fun x' ↦ u x' y) x + b * deriv (fun y' ↦ u x y') y = 0 := by
  sorry



theorem theorem_631513_problem (y : ℝ → ℝ) (h_diff : Differentiable ℝ y)
  (h_ode : ∀ x, 2 * y x * deriv y x + 2 * y x * x^2 * y x = 14 * x^2) :
  ∃ C : ℝ, ∀ x, y x = Real.sqrt (C * Real.exp (-2 * x^3 / 3) + 7) ∨
                y x = -Real.sqrt (C * Real.exp (-2 * x^3 / 3) + 7) := by
  sorry













theorem theorem_631710_problem :
  ∑' n : ℕ, (if n = 0 then 0 else ((-1 : ℝ) ^ n) / ((2 * (n : ℝ) + 3) * (3 : ℝ) ^ n)) =
    8 / 3 - Real.sqrt 3 * Real.pi / 2 := by
  sorry





















theorem theorem_633515_problem (n : ℕ) (hn : n > 0) :
  ∫ x in (0 : ℝ)..Real.pi, (Real.sin x) ^ (2 * n) =
  ((2 * n - 1).doubleFactorial : ℝ) / ((2 * n).doubleFactorial : ℝ) * Real.pi := by
  sorry

theorem theorem_633188_problem
  (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
  (n j : ℕ)
  (v : ℕ → V)
  (hj_ge : 1 ≤ j)
  (hj_lt : j < n)
  (h_span_inter : Submodule.span K (v '' (Set.Icc 1 j)) ⊓ 
                  Submodule.span K (v '' (Set.Icc (j + 1) n)) ≠ ⊥) :
  ∃ (a b : ℕ → K),
    ((∃ i, 1 ≤ i ∧ i ≤ j ∧ a i ≠ 0) ∨ (∃ k, j + 1 ≤ k ∧ k ≤ n ∧ b k ≠ 0)) ∧
    (∑ i in Finset.Icc 1 j, a i • v i = ∑ k in Finset.Icc (j + 1) n, b k • v k) := by
  sorry











theorem theorem_633979_problem
  -- f is a smooth transformation from R^2 to R^2
  (f : (ℝ × ℝ) → (ℝ × ℝ))
  (hf : ContDiff ℝ ⊤ f)
  -- Coordinates on the domain
  (x_coord : (ℝ × ℝ) → ℝ := Prod.fst)
  (t_coord : (ℝ × ℝ) → ℝ := Prod.snd)
  -- Components of the transformation f (X and T)
  (X : (ℝ × ℝ) → ℝ := fun p => (f p).1)
  (T : (ℝ × ℝ) → ℝ := fun p => (f p).2)
  -- Differentials defined as Fréchet derivatives (linear maps)
  (dx : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ := fun p => fderiv ℝ x_coord p)
  (dt : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ := fun p => fderiv ℝ t_coord p)
  (dX : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ := fun p => fderiv ℝ X p)
  (dT : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ := fun p => fderiv ℝ T p)
  -- Jacobian determinant of f
  (det_df : (ℝ × ℝ) → ℝ := fun p => (fderiv ℝ f p).det)
  -- Definition of the wedge product for 1-forms (linear maps)
  (wedge : ((ℝ × ℝ) →L[ℝ] ℝ) → ((ℝ × ℝ) →L[ℝ] ℝ) → (ℝ × ℝ) → (ℝ × ℝ) → ℝ :=
    fun α β u v => α u * β v - α v * β u) :
  -- The relation to prove
  ∀ p : ℝ × ℝ, ∀ u v : ℝ × ℝ,
    wedge (dX p) (dT p) u v = det_df p * wedge (dx p) (dt p) u v := by
  sorry



theorem theorem_634065_problem (f : ℕ → ℝ → ℝ)
  (h_def : ∀ n x, f n x = ((-1 : ℝ)^(n + 1) * n.factorial) / (n : ℝ)^(2 * n) * Real.cos (2 * n * x)) :
  ∃ g : ℝ → ℝ, TendstoUniformlyOn (fun N x ↦ ∑ n in Finset.range N, f (n + 1) x) g Filter.atTop Set.univ := by
  sorry







theorem theorem_634841_problem (a b : ℝ) (f : ℝ → ℝ)
  (h_le : a ≤ b)
  (h_cont : ContinuousOn f (Set.Icc a b))
  (h_nonneg : ∀ x ∈ Set.Icc a b, 0 ≤ f x) :
  0 ≤ ∫ x in a..b, f x := by
  sorry

theorem theorem_634260_problem (ε δ C E : ℝ)
  (hC : 0 < C)
  (h_model : E ≤ C * δ)
  (h_condition : δ ≤ ε / C) :
  E ≤ ε := by
  sorry



theorem theorem_634394_problem
  {D : Type*}
  (f g : D → ℝ)
  (hf : ∀ s, f s ≠ 0)
  (theta : D → ℝ)
  (h_theta : ∀ s, Real.tan (theta s) = g s / f s)
  (t : ℝ)
  (s : D)
  (h_sol : theta s = t) :
  Real.tan t = g s / f s := by
  sorry





theorem theorem_634631_problem {α β : Type*} (X : Set α) (F : α → β → Prop)
  (hF : ∀ x ∈ X, ∃! y, F x y) :
  ∃ Y : Set β, Y = {y | ∃ x ∈ X, F x y} := by
  sorry



theorem theorem_634938_problem (f F : ℝ → ℝ) (b x₀ : ℝ)
  -- Condition: F is the CDF of f, satisfying the Fundamental Theorem of Calculus relation
  (h_cdf : ∀ u v, ∫ t in u..v, f t = F v - F u)
  -- Condition: F(upper bound) = 1
  (h_bound : F b = 1)
  -- Condition: x₀ is in the domain such that the denominator is non-zero
  (h_denom : F x₀ ≠ 1) :
  (1 / (1 - F x₀)) * (∫ x in x₀..b, f x) = 1 := by
  sorry

theorem theorem_634881_problem (n k : ℕ) (hn : n > 0) (hk : k > 0) :
  (Fintype.card { f : Fin n → Fin k // Function.Surjective f } : ℤ) =
  ∑ i in Finset.range (k + 1), (-1 : ℤ) ^ i * (Nat.choose k i) * (k - i) ^ n := by
  sorry



theorem theorem_635341_problem 
  (FoundationSystem Concept : Type)
  (F : FoundationSystem)
  (C : Set Concept)
  (encodes : FoundationSystem → Set Concept → Prop)
  (supports_efficient_verification : FoundationSystem → Set Concept → Prop)
  (practically_feasible : FoundationSystem → Set Concept → Prop)
  (h_encodes : encodes F C)
  (h_verify : supports_efficient_verification F C) :
  practically_feasible F C := by
  sorry

theorem theorem_634843_problem
  {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {A : Type*} [NormedRing A] [NormedAlgebra K A] [CompleteSpace A]
  {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (h : A → C(X, K))
  (h_lin : IsLinearMap K h)
  (h_mul : ∀ x y, h (x * y) = h x * h y)
  (h_graph_closed : IsClosed {p : A × C(X, K) | p.2 = h p.1}) :
  Continuous h := by
  sorry



theorem theorem_634948_problem (n : ℕ) (z : ℕ → Fin n → ℂ)
  (h : ∀ j : Fin n,
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ a : ℝ, Filter.Tendsto (fun k => (z (φ k) j).re) Filter.atTop (nhds a)) ∧
    (∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ b : ℝ, Filter.Tendsto (fun k => (z (ψ k) j).im) Filter.atTop (nhds b))) :
  ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ L : Fin n → ℂ, Filter.Tendsto (z ∘ θ) Filter.atTop (nhds L) := by
  sorry

