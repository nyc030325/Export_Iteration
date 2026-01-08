import Mathlib
import Mathlib.Tactic





theorem theorem_974132_problem (b : ℕ → ℕ → ℂ)
  (h1 : ∀ n, Summable (fun i => ‖b n i‖))
  (h2 : Summable (fun n => ∑' i, ‖b n i‖)) :
  (∑' i, ∑' n, b n i) = (∑' n, ∑' i, b n i) := by
  sorry

theorem theorem_974357_problem
  (n k : ℕ)
  (Y : Matrix (Fin n) (Fin 1) ℝ)
  (X : Matrix (Fin n) (Fin k) ℝ)
  (Ψ : Matrix (Fin n) (Fin n) ℝ)
  (P : Matrix (Fin n) (Fin n) ℝ)
  [Invertible Ψ]
  (hP : P.transpose * P = ⅟Ψ)
  [Invertible (X.transpose * (⅟Ψ) * X)]
  [Invertible ((P * X).transpose * (P * X))] :
  let Y_star := P * Y
  let X_star := P * X
  let β_GLS := ⅟(X.transpose * (⅟Ψ) * X) * X.transpose * (⅟Ψ) * Y
  let β_OLS_star := ⅟(X_star.transpose * X_star) * X_star.transpose * Y_star
  β_GLS = β_OLS_star := by
  sorry



theorem theorem_974580_problem (k : ℝ) (hk : 0 < k) (y : ℝ → ℝ)
  (h_diff : ContDiff ℝ 2 y)
  (h_ode : ∀ x, deriv (deriv y) x - (k + Real.pi ^ 2) * y x = 0)
  (h_bc1 : y 0 = 0)
  (h_bc2 : y 1 = 1) :
  ∀ x, y x = Real.sinh (Real.sqrt (k + Real.pi ^ 2) * x) / Real.sinh (Real.sqrt (k + Real.pi ^ 2)) := by
  sorry





theorem theorem_974729_problem {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (h_edges : G.edgeFinset.card + 1 = Fintype.card V)
  (h_acyclic : G.IsAcyclic) :
  G.Connected := by
  sorry







theorem theorem_974845_problem
  -- Setup: Abstract types for Language and Problem
  {Sentence : Type}
  (neg : Sentence → Sentence)
  (T : Set Sentence)
  (P : Set ℕ)
  
  -- Definitions of logical properties
  (is_consistent : Prop := ∀ s, ¬ (s ∈ T ∧ neg s ∈ T))
  (is_complete : Prop := ∀ s, s ∈ T ∨ neg s ∈ T)
  (is_independent : Sentence → Prop := λ s ↦ s ∉ T ∧ neg s ∉ T)
  
  -- Definitions of computability properties (abstracted)
  (is_recursively_enumerable : Set Sentence → Prop)
  (is_decidable_theory : Set Sentence → Prop)
  (is_decidable_problem : Set ℕ → Prop)
  (expresses : Set Sentence → Set ℕ → Prop)

  -- Conditions from the problem statement
  (h_cons : is_consistent)
  (h_sound : Prop) -- "assuming T is sound"
  (h_undecidable : ¬ is_decidable_problem P) -- "P is algorithmically undecidable"
  
  -- Implicit conditions required for the mathematical validity of the theorem (from solution context)
  (h_re : is_recursively_enumerable T)
  (h_expr : expresses T P)

  -- Axioms representing the standard theorems of computability logic used in the proof
  (ax_re_complete_imp_decidable : is_recursively_enumerable T → is_complete → is_decidable_theory T)
  (ax_expr_decidable_imp_decidable_prob : expresses T P → is_decidable_theory T → is_decidable_problem P) :
  ∃ θ, is_independent θ := by
  sorry

theorem theorem_975144_problem (n : ℕ)
  (h_pole : n ≥ 1)
  (h_bound : n ≤ 15)
  (h_contradiction : n = 15 → False) :
  n < 15 := by
  sorry



theorem theorem_975494_problem
  (n : ℕ)
  (C : Matrix (Fin n) (Fin n) ℝ)
  (C' : Matrix (Fin n) (Fin n) ℝ)
  (h_def : ∀ i j, C' i j = - C i j)
  (S : Equiv.Perm (Fin n))
  (h_optimal_C' : ∀ T : Equiv.Perm (Fin n), ∑ i, C' i (S i) ≤ ∑ i, C' i (T i)) :
  ∀ T : Equiv.Perm (Fin n), ∑ i, C i (S i) ≥ ∑ i, C i (T i) := by
  sorry

theorem theorem_975522_problem (x y r θ : ℝ)
  (h_r : 0 ≤ r)
  (hx : x = r * Real.cos θ)
  (hy : y = r * Real.sin θ) :
  r = Real.sqrt (x^2 + y^2) := by
  sorry

theorem theorem_975596_problem
  {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  (T : X →L[ℝ] Y)
  (x_n : ℕ → X)
  (x : X)
  (h_weak_conv : ∀ f : X →L[ℝ] ℝ, Filter.Tendsto (fun n ↦ f (x_n n)) Filter.atTop (nhds (f x))) :
  ∀ g : Y →L[ℝ] ℝ, Filter.Tendsto (fun n ↦ g (T (x_n n))) Filter.atTop (nhds (g (T x))) := by
  sorry



theorem theorem_975451_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  (U : Submodule 𝕜 V)
  (z : V)
  (hz : z ∉ U)
  (d : ℝ)
  (hd : d = sInf {r | ∃ x ∈ U, r = ‖x - z‖})
  (hd_pos : 0 < d) :
  ∃ ψ : V →L[𝕜] 𝕜, (∀ u ∈ U, ψ u = 0) ∧ ψ z = 1 := by
  sorry



theorem theorem_975568_problem {A : Type*} [CommRing A] (S : Set A) :
  Ideal.span S = sInf { I : Ideal A | S ⊆ I } := by
  sorry



theorem theorem_976202_problem (a : ℕ → ℝ)
  (h : ∀ k, 1 ≤ k → a k = (((k : ℝ) + 2) / ((k : ℝ)^2 * ((k : ℝ)^2 + 1))) ^ ((1 : ℝ) / 3)) :
  ¬ Summable a := by
  sorry

theorem theorem_976476_problem (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (r : ℝ)
  (hr_pos : 0 < r)
  (h_not_pow : ∀ n : ℤ, r ≠ (p : ℝ) ^ n) :
  Metric.ball x r = Metric.closedBall x r := by
  sorry

theorem theorem_975850_problem
  (n : ℕ)
  (a b : Fin n → ℝ)
  (p q : ℝ)
  (hp : 1 < p)
  (hq : 1 < q)
  (hpq : 1 / p + 1 / q = 1) :
  |∑ i, a i * b i| ≤ (∑ i, |a i| ^ p) ^ (1 / p) * (∑ i, |b i| ^ q) ^ (1 / q) := by
  sorry







theorem theorem_975379_problem
  (E_total : ℝ → ℝ)
  (t₁ t₂ : ℝ)
  (h_time : t₁ < t₂)
  -- Abstract variable representing the volume integral of the divergence
  (div_rho_integral : ℝ)
  -- Abstract variable representing the flux integral over the lateral boundary S
  (lateral_flux : ℝ)
  -- The Divergence Theorem relationship applied to the specific frustum geometry described
  -- ∫_V (∇·ρ) = E(t₁) - E(t₂) + ∫_S ρ·n
  (h_div_thm : div_rho_integral = E_total t₁ - E_total t₂ + lateral_flux)
  -- Condition: The divergence is non-negative
  (h_div_nonneg : div_rho_integral ≥ 0)
  -- Condition: The frustum is of a light cone (implies lateral flux contribution is non-positive)
  (h_light_cone : lateral_flux ≤ 0) :
  E_total t₂ ≤ E_total t₁ := by
  sorry

theorem theorem_976466_problem
  (Manifold4 : Type)
  (Manifold3 : Type)
  (boundary : Manifold4 → Manifold3)
  (boundarySum : Manifold4 → Manifold4 → Manifold4)
  (diffeomorphic : Manifold3 → Manifold3 → Prop)
  (cp2_minus_b4 : Manifold4)
  (X : Manifold4) :
  diffeomorphic (boundary (boundarySum X cp2_minus_b4)) (boundary X) := by
  sorry



theorem theorem_976621_problem (D : Type*) (hD : Nonempty D) (P Q : D → Prop) :
  (∃ x, ¬ (P x → Q x)) ↔ (∃ a, P a ∧ ¬ Q a) := by
  sorry

theorem theorem_976669_problem :
  (∑' p : ℕ, (1 : ℝ) / p.factorial) * (∑' q : ℕ, (-1 : ℝ) ^ q / q.factorial) = 1 := by
  sorry



theorem theorem_976794_problem (a m n : ℕ) (ha : a > 1) (hm : m > 0) (hn : n > 0) :
  Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ (Nat.gcd m n) - 1 := by
  sorry



theorem theorem_976578_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
  LinearMap.range (Matrix.toLin' (A * A.transpose)) ≤ LinearMap.range (Matrix.toLin' A) := by
  sorry

theorem theorem_976693_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (D_nabla2 : V → V)
  (F : V → V)
  (J : V → V)
  (u u_s w : ℝ → V)
  (partial_t : (ℝ → V) → (ℝ → V))
  (h_lin_D : IsLinearMap ℝ D_nabla2)
  (h_lin_t : ∀ f g, partial_t (f + g) = partial_t f + partial_t g)
  (h_sys_u : ∀ t, partial_t u t = D_nabla2 (u t) + F (u t))
  (h_steady_us : partial_t u_s = 0)
  (h_sys_us : ∀ t, partial_t u_s t = D_nabla2 (u_s t) + F (u_s t))
  (h_def_w : u = u_s + w)
  (h_approx : ∀ t, F (u_s t + w t) = F (u_s t) + J (w t)) :
  ∀ t, partial_t w t = D_nabla2 (w t) + J (w t) := by
  sorry

theorem theorem_977075_problem
  (f g : ℝ → ℝ)
  (hf : Continuous f)
  (hg : Continuous g)
  (h : ∀ V : Set ℝ, IsOpen V → ∫ x in V, f x = ∫ x in V, g x) :
  f = g := by
  sorry

theorem theorem_976764_problem {X : Type*} [MetricSpace X] (A : Set X) (x : X)
  (hA : A.Nonempty) (h : Metric.infDist x A = 0) : x ∈ closure A := by
  sorry



theorem theorem_976570_problem (a b : ℝ) (hab : a ≤ b) (f g h F : ℝ → ℝ)
  (hf : ContDiffOn ℝ ⊤ f (Set.Icc a b))
  (hg : ContDiffOn ℝ ⊤ g (Set.Iic a))
  (hh : ContDiffOn ℝ ⊤ h (Set.Ici b))
  (h_glue_a : ∀ k : ℕ, iteratedDerivWithin k g (Set.Iic a) a = iteratedDerivWithin k f (Set.Icc a b) a)
  (h_glue_b : ∀ k : ℕ, iteratedDerivWithin k h (Set.Ici b) b = iteratedDerivWithin k f (Set.Icc a b) b)
  (hF : ∀ x, F x = if x ≤ a then g x else if x < b then f x else h x) :
  ContDiff ℝ ⊤ F := by
  sorry

theorem theorem_976579_problem (R : Type*) [CommRing R] [IsArtinianRing R]
  (P₁ P₂ : Ideal R) (hP₁ : P₁.IsPrime) (hP₂ : P₂.IsPrime) (h_neq : P₁ ≠ P₂) :
  P₁ ≠ P₁ * P₂ := by
  sorry



theorem theorem_976491_problem
  (G : Type*) [Group G] [Finite G]
  (N : Subgroup G) [N.Normal]
  (g : G) :
  Nat.card (Subgroup.centralizer {(g : G ⧸ N)}) ≤ Nat.card (Subgroup.centralizer {g}) := by
  sorry

theorem theorem_976627_problem
  (S1 : Set (ℝ × ℝ))
  (f : ℝ → ℝ × ℝ)
  (A : Set (ℝ × ℝ))
  (hS1 : S1 = {p | p.1^2 + p.2^2 = 1})
  (hf : f = fun t ↦ (Real.cos (2 * Real.pi * t), Real.sin (2 * Real.pi * t)))
  (hA : A = f '' (Set.Ico 0 (1 / 4))) :
  ¬ ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V ∩ S1 = A := by
  sorry





theorem theorem_976796_problem {F : Type*} [Field F] (A : Set F) :
  (A = {0} → (∀ a ∈ A, 0 ∣ a) ∧ (∀ d : F, (∀ a ∈ A, d ∣ a) → d ∣ 0)) ∧
  (∀ x ∈ A, x ≠ 0 → (∀ a ∈ A, x ∣ a) ∧ (∀ d : F, (∀ a ∈ A, d ∣ a) → d ∣ x)) := by
  sorry

theorem theorem_976730_problem (a x : ℝ) (ha : 0 < a) (hx1 : 0 < x) (hx2 : x < 1) :
  HasDerivAt (fun t => - (1 / a) * (1 - t) ^ a * t ^ (-a))
    (1 / (x ^ (1 + a) * (1 - x) ^ (1 - a))) x := by
  sorry





theorem theorem_977351_problem (m : ℕ) (hm : 2 < m) :
  ∀ p ∈ m.factors, (∀ q ∈ m.factors, q ≤ p) →
  (p : ℝ) ≤ (m : ℝ) ^ ((Real.log m) ^ 2) := by
  sorry

theorem theorem_976995_problem (X : Type*) (B : Type*)
  (X_beta : B → Set X)
  (h_cover : (⋃ β, X_beta β) = Set.univ)
  (t_beta : ∀ β, TopologicalSpace (X_beta β)) :
  ∃ T : TopologicalSpace X,
    (∀ U : Set X, T.IsOpen U ↔ ∀ β, (t_beta β).IsOpen ((Subtype.val : X_beta β → X) ⁻¹' U)) ∧
    (∀ T' : TopologicalSpace X, (∀ β, @Continuous _ _ (t_beta β) T' (Subtype.val : X_beta β → X)) →
      ∀ U, T'.IsOpen U → T.IsOpen U) := by
  sorry

theorem theorem_977207_problem
  (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y)
  (h_cont : Continuous f)
  (h_closed : IsClosedMap f)
  (h_surj : Function.Surjective f)
  (h_fiber : ∀ y : Y, IsCompact (f ⁻¹' {y}))
  (h_haus_X : T2Space X) :
  T2Space Y := by
  sorry

theorem theorem_977772_problem (p k : ℕ) (b : ℤ)
  (hp : Nat.Prime p)
  (h_gcd : Int.gcd b p = 1) :
  Nonempty ((Localization.Away (b : ZMod (p ^ k))) ≃+* ZMod (p ^ k)) := by
  sorry







theorem theorem_978388_problem
  (G G' : Type*)
  [CommGroup G] [Finite G]
  [CommGroup G'] [Finite G']
  (h : ∀ (p : ℕ) [Fact (Nat.Prime p)],
    ∀ (S : Sylow p G) (S' : Sylow p G'), Nonempty (S ≃* S')) :
  Nonempty (G ≃* G') := by
  sorry





theorem theorem_978808_problem (f : ℝ → ℝ) (θ : ℝ)
  (hf : Differentiable ℝ f) :
  let x := fun (t : ℝ) => f t * Real.cos t
  let y := fun (t : ℝ) => f t * Real.sin t
  Real.sqrt ((deriv x θ)^2 + (deriv y θ)^2) = Real.sqrt ((f θ)^2 + (deriv f θ)^2) := by
  sorry





theorem theorem_978765_problem (n : ℕ) (hn : n > 0) :
  {z : ℂ | z ^ n = -1} = 
  (fun z => z * Complex.exp (Complex.I * Real.pi / (n : ℂ))) '' {z : ℂ | z ^ n = 1} := by
  sorry

theorem theorem_978484_problem
  (I : Set (Set ℝ))
  (h_open : ∀ s ∈ I, ∃ a b : ℝ, s = Set.Ioo a b)
  (h_disjoint : Set.PairwiseDisjoint I id)
  (h_exists_f : ∃ f : I → ℚ, ∀ (s : I), (f s : ℝ) ∈ (s : Set ℝ)) :
  Set.Countable I := by
  sorry









theorem theorem_975305_problem {R : Type*} [Ring R] (n m : ℕ) 
  (hn : n > 0) (hm : m > 0) :
  (n : R) * (m : R) = ((n * m) : R) := by
  sorry





theorem theorem_979874_problem
  {X : Type*} [MeasurableSpace X]
  (f g : X → ℝ)
  (hf : Measurable f)
  (hg : Measurable g) :
  MeasurableSet {x | (f - g) x ≤ 0} := by
  sorry



theorem theorem_979691_problem (n m : ℕ) :
  let E := EuclideanSpace ℝ (Fin (n + m))
  let e := PiLp.basisFun 2 ℝ (Fin (n + m))
  let V := Submodule.span ℝ { x | ∃ i : Fin (n + m), i.val < n ∧ x = e i }
  ∀ v : E,
    let p := ∑ i in Finset.filter (fun j => j.val < n) Finset.univ, (v i) • (e i)
    p ∈ V ∧ ∀ w ∈ V, dist v p ≤ dist v w := by
  sorry

theorem theorem_979219_problem
  (a b c d : ℝ)
  (f : ℝ → ℝ → ℝ)
  (f_t : ℝ → ℝ → ℝ)
  (hab : a < b)
  (hcd : c < d)
  (h_unif : ∀ x ∈ Set.Icc c d, UniformContinuousOn (fun t ↦ f t x) (Set.Icc a b))
  (h_deriv_exists : ∀ t ∈ Set.Icc a b, ∀ x ∈ Set.Icc c d, HasDerivAt (fun u ↦ f u x) (f_t t x) t)
  (h_deriv_cont : ContinuousOn (fun p : ℝ × ℝ ↦ f_t p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d))
  (t : ℝ) (ht : t ∈ Set.Ioo a b) :
  HasDerivAt (fun u ↦ ∫ x in c..d, f u x) (∫ x in c..d, f_t t x) t := by
  sorry











theorem theorem_979159_problem
  (n : ℕ)
  (A L D S : Matrix (Fin n) (Fin n) ℝ)
  (d : Fin n → ℝ)
  (hD : D = Matrix.diagonal d)
  (hS : S = Matrix.diagonal (fun i => Real.sqrt (d i)))
  (h_pos : ∀ i, 0 < d i)
  (hL : L = 1 - (Matrix.diagonal (fun i => (Real.sqrt (d i))⁻¹)) * A * (Matrix.diagonal (fun i => (Real.sqrt (d i))⁻¹))) :
  A = D - S * L * S := by
  sorry



theorem theorem_980862_problem
  (p : ℕ) (hp : Nat.Prime p)
  (a : ℤ) (ha1 : 1 ≤ a) (ha2 : a ≤ p - 1) :
  ∀ k₁ k₂ : ℤ, 1 ≤ k₁ → k₁ ≤ p - 1 →
  1 ≤ k₂ → k₂ ≤ p - 1 →
  a * k₁ ≡ a * k₂ [ZMOD p] → k₁ = k₂ := by
  sorry



theorem theorem_980685_problem (n d : ℕ) (M : Matrix (Fin d) (Fin n) ℤ)
  (deg : (Fin n → ℕ) → (Fin d → ℤ))
  (h_deg : ∀ a, deg a = M.mulVec (fun i => (a i : ℤ))) :
  ∀ a b : Fin n → ℕ, deg (a + b) = deg a + deg b := by
  sorry





theorem theorem_980786_problem (n d k : ℕ)
  (h_valid_knots : k ≥ d + 1)
  (h_bspline_dim : n = k - d - 1) :
  k = n + d + 1 := by
  sorry





theorem theorem_981349_problem (p : ℕ → ℕ)
  (h_asc : StrictMono p)
  (h_prime : Set.range p = {x | Nat.Prime x}) :
  Filter.Tendsto (fun n => ∑ i in Finset.range n, 1 / (p i : ℝ)) Filter.atTop Filter.atTop := by
  sorry





theorem theorem_981437_problem (n : ℕ) :
  (iteratedDeriv n Real.cos (Real.pi / 3)).sign = (-1 : ℝ) ^ Int.ceil ((n : ℝ) / 2) := by
  sorry



theorem theorem_981908_problem
  {Formula : Type*}
  (is_tautology : Formula → Prop)
  (consistent : Set Formula → Prop)
  (maximal_consistent : Set Formula → Prop)
  (h_mcs_def : ∀ S, maximal_consistent S ↔ (consistent S ∧ ∀ φ, φ ∉ S → ¬ consistent (insert φ S)))
  (A : Formula)
  (h_not_taut : ¬ is_tautology A)
  (h_cons_union : consistent (insert A {x | is_tautology x})) :
  ¬ maximal_consistent {x | is_tautology x} := by
  sorry

