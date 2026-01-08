import Mathlib
import Mathlib.Tactic



theorem theorem_584161_problem {V : Type*} [Fintype V] [DecidableEq V] (f : Finset V → ℝ) :
  (∀ (A B : Finset V) (x : V), A ⊆ B → x ∉ B → f (insert x A) - f A ≥ f (insert x B) - f B) ↔
  (∀ (A B : Finset V), f A + f B ≥ f (A ∩ B) + f (A ∪ B)) := by
  sorry





theorem theorem_583578_problem
  -- Types for the manifold P, Lie algebra G (as a vector space), and Vector Fields VF
  {P : Type*} [TopologicalSpace P]
  {G : Type*} [AddCommGroup G]
  {VF : Type*} [AddCommGroup VF]

  -- Abstract Operators representing the geometric structures
  (LieBracket_G : G → G → G) -- Lie bracket on the Lie algebra G
  (LieBracket_VF : VF → VF → VF) -- Lie bracket on vector fields
  (omega : VF → P → G) -- The connection 1-form ω
  (Omega : VF → VF → P → G) -- The curvature 2-form Ω
  (deriv : VF → (P → G) → (P → G)) -- Directional derivative X(f)

  -- Definition of Curvature Form via Structure Equation: Ω = dω + [ω, ω]
  -- Using the formula for exterior derivative dω(X,Y) = X(ω(Y)) - Y(ω(X)) - ω([X,Y])
  -- and [ω, ω](X,Y) = 2[ω(X), ω(Y)], the 1/2 factor cancels out.
  (h_curvature_def : ∀ (X Y : VF) (q : P),
    Omega X Y q = (deriv X (omega Y) q) - (deriv Y (omega X) q) - (omega (LieBracket_VF X Y) q)
                  + LieBracket_G (omega X q) (omega Y q))

  -- Definition of the vertical component in the Lie algebra
  -- We identify the vertical component of a vector Z with -ω(Z) 
  -- (consistent with the problem statement [X, Y]_vert = Ω(X, Y) and derivation)
  (vert_component : VF → P → G)
  (h_vert_def : ∀ (Z : VF) (q : P), vert_component Z q = - omega Z q)

  -- The zero function for horizontal checks
  (zero_G : G)
  (h_zero_def : ∀ q : P, (fun _ => zero_G) q = 0)

  -- Given Variables
  (p : P)
  (X_tilde Y_tilde : VF) -- Horizontal extensions of X and Y

  -- Conditions: The extensions are horizontal
  (h_horiz_X : omega X_tilde = fun _ => zero_G)
  (h_horiz_Y : omega Y_tilde = fun _ => zero_G) :

  -- Conclusion: The vertical component of the bracket equals the curvature
  vert_component (LieBracket_VF X_tilde Y_tilde) p = Omega X_tilde Y_tilde p := by
  sorry

theorem theorem_583923_problem
  (f : ℝ → ℝ)
  (x : ℕ → ℝ)
  (h_mono : MonotoneOn f (Set.Ioi 0))
  (hx_pos : ∀ k, 0 < x k)
  (hx_lim : Filter.Tendsto x Filter.atTop (nhds 0))
  (h_ratio : Filter.Tendsto (fun k ↦ f (x k) / f (2 * x k)) Filter.atTop (nhds 0)) :
  Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  sorry





theorem theorem_584598_problem (n : ℕ) (h1 : 1 < n)
  (h2 : ∀ p : ℕ, Nat.Prime p → p^2 ≤ n → ¬ p ∣ n) :
  Nat.Prime n := by
  sorry



theorem theorem_584462_problem (R : Type*) [Field R]
  (h1 : ∃ S1 : Subfield R, Nonempty (S1 ≃+* ZMod 5))
  (h2 : ∃ S2 : Subfield R, Nonempty (S2 ≃+* ZMod 7)) :
  False := by
  sorry

theorem theorem_583926_problem :
  LinearIndependent ℚ ![(1 : ℝ), Real.pi, Real.pi ^ 2] := by
  sorry

theorem theorem_584051_problem {X : Type*} [MetricSpace X] (E : Set X) :
  interior E = closure E \ frontier E := by
  sorry

theorem theorem_584649_problem (p : ℕ) (s M x r : ℤ) (y : ℕ)
  (hp : p.Prime)
  (h_div : s ∣ (M - x ^ y))
  (h_gcd : Int.gcd ((p : ℤ) - 1) s > 1) :
  s * r ≡ M - x ^ y [ZMOD (p : ℤ) - 1] ↔
  r ≡ (M - x ^ y) / s [ZMOD ((p : ℤ) - 1) / (Int.gcd ((p : ℤ) - 1) s)] := by
  sorry







theorem theorem_584294_problem (f : ℂ → ℂ)
  (h_entire : Differentiable ℂ f)
  (h_lipschitz : ∃ K : NNReal, LipschitzWith K f) :
  ∃ a b : ℂ, ∀ z, f z = a * z + b := by
  sorry











theorem theorem_584889_problem
  (R : Type*) [CommRing R] [IsDomain R]
  (F : Type*) [AddCommGroup F] [Module R F] [Module.Free R F]
  (N : Submodule R F)
  (hM_torsion : ∃ (m : F ⧸ N) (r : R), m ≠ 0 ∧ r ≠ 0 ∧ r • m = 0)
  (hN_tf : ∀ (n : N) (r : R), n ≠ 0 → r ≠ 0 → r • n ≠ 0) :
  ¬ Nonempty ((F ⧸ N) × N ≃ₗ[R] F) := by
  sorry



theorem theorem_585049_problem (n : ℕ) (U D C : Set (Fin n → ℝ))
  (hU : IsOpen U)
  (hD : IsClosed D)
  (hC_compact : IsCompact C)
  (hC_conn_comp_Uc : C ⊆ Uᶜ ∧ IsConnected C ∧ ∀ S, S ⊆ Uᶜ → IsConnected S → C ⊆ S → S = C)
  (hC_sub_D : C ⊆ D) :
  C ⊆ (U ∩ D)ᶜ ∧ IsConnected C ∧ ∀ S, S ⊆ (U ∩ D)ᶜ → IsConnected S → C ⊆ S → S = C := by
  sorry







theorem theorem_584269_problem 
  (f : ℕ → ℕ → ℕ → ℝ) 
  (x y z : ℝ)
  (h_sym : ∀ a b c, f a b c = f c b a)
  (h_init : f 0 0 0 = 1)
  (h_rec : ∀ a b c, 2 ≤ a → 2 ≤ b → 2 ≤ c → 
    f a b c = f (a - 2) b c + f a (b - 2) c + f a b (c - 2) + 2 * f (a - 1) (b - 1) (c - 1))
  (h_denom : 1 - x^2 - y^2 - z^2 - 2 * x * y * z ≠ 0) :
  (∑' a, ∑' b, ∑' c, f a b c * x^a * y^b * z^c) = 
  (x + z + x * y + y * z + 1 - y^2) / (1 - x^2 - y^2 - z^2 - 2 * x * y * z) := by
  sorry





theorem theorem_585260_problem
  (k a b c d : ℝ)
  (hk : k > 0)
  (y₁ y₂ : ℝ → ℂ)
  (h_diff1 : ∀ t, HasDerivAt y₁ (Complex.I * k * y₂ t) t)
  (h_diff2 : ∀ t, HasDerivAt y₂ (-Complex.I * k * y₁ t) t)
  (h_init1 : y₁ 0 = a + c * Complex.I)
  (h_init2 : y₂ 0 = b + d * Complex.I) :
  ∀ t,
    y₁ t = (1 / 2 : ℂ) * ((a + c * Complex.I) * (Complex.exp (k * t : ℂ) + Complex.exp (-(k * t : ℂ))) +
           (b + d * Complex.I) * (Complex.exp (k * t : ℂ) - Complex.exp (-(k * t : ℂ))) * Complex.I) ∧
    y₂ t = (1 / 2 : ℂ) * ((b + d * Complex.I) * (Complex.exp (k * t : ℂ) + Complex.exp (-(k * t : ℂ))) -
           (a + c * Complex.I) * (Complex.exp (k * t : ℂ) - Complex.exp (-(k * t : ℂ))) * Complex.I) := by
  sorry



theorem theorem_585035_problem : Nonempty (G ≃ ℕ) := by
  sorry





theorem theorem_585963_problem
  (h : ℝ → ℝ)
  (g : ℝ → ℝ)
  (h_diff : Differentiable ℝ h)
  (h_zero : h 0 = 0)
  (hg : ∀ x, g x = (1 + h x) ^ (-(1 : ℝ) / 2)) :
  g 0 = 1 ∧ deriv g 0 = -(deriv h 0) / 2 := by
  sorry



theorem theorem_586040_problem (A B : Set (Fin 3 → ℝ))
  (hA_nonempty : A.Nonempty)
  (hB_nonempty : B.Nonempty)
  (hA_inj : ∃ f : ℝ → A, Function.Injective f)
  (hB_inj : ∃ f : ℝ → B, Function.Injective f) :
  Cardinal.mk A = Cardinal.continuum ∧ Cardinal.mk B = Cardinal.continuum := by
  sorry



theorem theorem_586075_problem (n : ℕ) (a : Fin n → ℤ)
  (h_gcd : Finset.gcd Finset.univ (fun i ↦ Int.natAbs (a i)) = 1)
  (m : ℤ) :
  ∃ x : Fin n → ℤ, ∑ i, x i * a i = m := by
  sorry



theorem theorem_585862_problem 
  -- Context Definitions (X, Forms, Cycles)
  (X : Type*) 
  (g : ℕ)
  (OneForm TwoForm Cycle : Type*)
  [AddCommGroup OneForm] [Module ℝ OneForm]
  [AddCommGroup TwoForm] [Module ℝ TwoForm]
  
  -- Operations (Wedge, Closedness, Integration)
  (wedge : OneForm → OneForm → TwoForm)
  (is_closed : OneForm → Prop)
  (int_X : TwoForm → ℝ)
  (int_cycle : Cycle → OneForm → ℝ)
  
  -- Condition: a, b denote a basis for H_1(X, ℤ)
  (a b : Fin g → Cycle)
  (is_homology_basis : (Fin g → Cycle) → (Fin g → Cycle) → Prop)
  (h_basis : is_homology_basis a b)
  
  -- Condition: ω and η are closed one-forms
  (ω η : OneForm)
  (hω : is_closed ω)
  (hη : is_closed η) :
  
  -- Conclusion: Riemann's bilinear relation
  int_X (wedge ω η) = ∑ i : Fin g, (int_cycle (a i) ω * int_cycle (b i) η - int_cycle (b i) ω * int_cycle (a i) η) := by
  sorry



theorem theorem_586257_problem
  (Point : Type*)
  (C : Set Point)
  (Col : Point → Point → Point → Prop)
  (op : Point → Point → Point)
  -- Condition: The set of intersection points is independent of order (symmetric)
  (h_col_symm_1 : ∀ x y z, Col x y z ↔ Col x z y)
  (h_col_symm_2 : ∀ x y z, Col x y z ↔ Col y x z)
  -- Condition: Definition of the operation based on the third intersection point
  (h_def : ∀ x y z, x ∈ C → y ∈ C → z ∈ C → (op x y = z ↔ Col x y z))
  (a b c : Point)
  (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C)
  -- Condition: a ∘ b = c
  (h_eq : op a b = c) :
  -- Question: Total symmetry (all permutations)
  op b a = c ∧ op a c = b ∧ op c a = b ∧ op b c = a ∧ op c b = a := by
  sorry

theorem theorem_586278_problem
  (R : Type*) [Ring R]
  (D : Type*)
  (E : Set (D → R))
  (h_add_closed : ∀ f g, f ∈ E → g ∈ E → (f + g) ∈ E)
  (h_mul_closed : ∀ f g, f ∈ E → g ∈ E → (f * g) ∈ E)
  (ringE : Ring {f // f ∈ E})
  (h_add_def : ∀ (f g : {f // f ∈ E}), (f + g).val = f.val + g.val)
  (h_mul_def : ∀ (f g : {f // f ∈ E}), (f * g).val = f.val * g.val) :
  ∀ f ∈ E, (-f) ∈ E := by
  sorry

theorem theorem_586016_problem
  {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {I : Type*} (A : I → Set X) (f : X → Y)
  (h_cover : (⋃ i, A i) = Set.univ)
  (h_open : ∀ i, IsOpen (A i))
  (h_gluing : ∀ i j, IsOpen (A i ∩ A j))
  (h_continuous_restrictions : ∀ i, ContinuousOn f (A i)) :
  Continuous f := by
  sorry



theorem theorem_586209_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ) (c : ℝ) (r : ℝ → E)
  (hf : Differentiable ℝ f)
  (hr : Differentiable ℝ r)
  (h_level : ∀ t : ℝ, f (r t) = c) :
  ∀ t : ℝ, inner (gradient f (r t)) (deriv r t) = (0 : ℝ) := by
  sorry









theorem theorem_586837_problem
  (x₁ x₂ : ℝ)
  (T_mean : ℝ)
  (P_T_gt : ℝ → ℝ)
  (N_mean : ℝ)
  (Z_sum_mean : ℝ)
  (h_x : 0 ≤ x₁ ∧ x₁ < x₂)
  (h_T_pos : 0 < T_mean)
  (h_int : IntervalIntegrable P_T_gt volume x₁ x₂)
  (h_renewal : ∃ α : ℝ, α > 0 ∧
    N_mean = α * T_mean ∧
    Z_sum_mean = α * (∫ t in x₁..x₂, P_T_gt t)) :
  Z_sum_mean / N_mean = (∫ t in x₁..x₂, P_T_gt t) / T_mean := by
  sorry









theorem theorem_586457_problem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (C : Set H) :
  Convex ℝ C ↔ ∀ x ∈ C, ∀ y ∈ C, ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - t) • x + t • y ∈ C := by
  sorry





theorem theorem_586617_problem (k : ℕ) (hk : k > 0)
  (I : Set ℕ := { i | i ≤ k })
  (X : I → Type := fun _ ↦ ℕ) :
  Nonempty ((Π i : I, X i) ≃ (Fin (k + 1) → ℕ)) := by
  sorry

theorem theorem_587060_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : E → ℝ) (x v : E)
  (h_diff : DifferentiableAt ℝ f x)
  (hv : v ≠ 0) :
  Filter.Tendsto (fun h : ℝ => (f (x + h • v) - f x) / (h * ‖v‖))
    (nhdsWithin 0 {0}ᶜ) (nhds ((fderiv ℝ f x v) / ‖v‖)) := by
  sorry

theorem theorem_586489_problem (a : ℕ → ℝ) (r : ℝ) (N : ℕ)
  (hr : r ≠ 1) :
  ∑ n in Finset.Ico 1 (N + 1), r^n * (∑ j in Finset.Ico 1 (n + 1), a j) =
  a N * ((1 - r^N) / (1 - r)) +
  ∑ n in Finset.Ico 1 N, (a n - a (n + 1)) * ((1 - r^(n + 1)) / (1 - r)) := by
  sorry

theorem theorem_586719_problem (n m : ℕ) (hn : n > 0) (hm : m > 0) :
  ∑ k in Finset.Icc 1 n, (∏ j in Finset.Icc k (k + m - 2), (j : ℚ)) =
  (∏ j in Finset.Icc n (n + m - 1), (j : ℚ)) / m := by
  sorry







theorem theorem_587659_problem
  {Ω : Type*} [MeasurableSpace Ω]
  (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
  (X : Ω → ℝ)
  (h : Measurable (fun ω ↦ (X ω) ^ 2)) :
  Measurable (fun ω ↦ |X ω|) := by
  sorry



theorem theorem_587512_problem {G : Type*} [Group G] [Fintype G] (h : Fintype.card G = 540) :
  ¬ IsSimpleGroup G := by
  sorry









theorem theorem_588044_problem
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (u : Fin n → ℝ)
  (hu_ne : u ≠ 0)
  (h_orth : A.mulVec u = 0) :
  A.rank < n := by
  sorry

theorem theorem_587660_problem
  {ι : Type*} [Fintype ι]
  (x₁ x₂ y₁ y₂ : ι → ℝ)
  (X₁ X₂ : ℝ)
  (hX₁ : X₁ = ∑ i, x₁ i)
  (hX₂ : X₂ = ∑ i, x₂ i)
  (hX₁_ne_zero : X₁ ≠ 0)
  (hX₂_ne_zero : X₂ ≠ 0) :
  (∑ i, x₂ i * y₂ i) / X₂ - (∑ i, x₁ i * y₁ i) / X₁ =
  ∑ i, ((x₂ i * y₂ i) / X₂ - (x₁ i * y₁ i) / X₁) := by
  sorry

theorem theorem_588136_problem (x y z : ℕ)
  (hx : x > 0) (hy : y > 0) (hz : z > 0)
  (h_gcd : Nat.gcd x y = 1)
  (h_eq : x^2 + y^2 = 7 * z^2) :
  False := by
  sorry



theorem theorem_587737_problem
  (r : ℕ)
  (hr : r > 0)
  {V_G : Type*} [Fintype V_G] [DecidableEq V_G]
  (G : SimpleGraph V_G) [DecidableRel G.Adj]
  {V_T : Type*} [Fintype V_T] [DecidableEq V_T]
  (T : SimpleGraph V_T) [DecidableRel T.Adj]
  (hG_minDegree : G.minDegree ≥ r)
  (hG_girth : G.girth ≥ 2 * r)
  (hT_tree : T.IsTree)
  (hT_card : Fintype.card V_T = r) :
  ∃ f : V_T ↪ V_G, ∀ u v, T.Adj u v ↔ G.Adj (f u) (f v) := by
  sorry

theorem theorem_588474_problem (x₁ x₂ : ℝ) :
  |x₁ - 2 * x₂| ≤ Real.sqrt 5 * Real.sqrt (x₁^2 + x₂^2) := by
  sorry





theorem theorem_588364_problem (hat_delta : ℝ → ℂ) (h : ∀ t, hat_delta t = 1) :
  ∫⁻ t, ENNReal.ofReal (‖hat_delta t‖ ^ 2) = ⊤ := by
  sorry











theorem theorem_589605_problem
  {α : Type*} [DecidableEq α]
  (n : ℕ)
  (S : Finset α)
  (STS : Finset (Finset α))
  (h_n : S.card = n)
  (h_mod : n % 6 = 1 ∨ n % 6 = 3)
  (h_subset : ∀ B ∈ STS, B ⊆ S)
  (h_size : ∀ B ∈ STS, B.card = 3)
  (h_steiner : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∃! B ∈ STS, {x, y} ⊆ B)
  (T : Finset α)
  (hT : T ∈ STS) :
  (STS.filter (fun B => Disjoint B T)).card = (n - 3) * (n - 7) / 6 := by
  sorry

theorem theorem_588769_problem
  (r : ℕ)
  (F E : Type*) [Field F] [Field E] [Algebra F E]
  (α : Fin r → E)
  (h_gen : IntermediateField.adjoin F (Set.range α) = ⊤)
  (x : E) :
  ∃ (p q : MvPolynomial (Fin r) F),
    MvPolynomial.aeval α q ≠ 0 ∧
    x = (MvPolynomial.aeval α p) / (MvPolynomial.aeval α q) := by
  sorry















theorem theorem_589233_problem
  {A : Type*} [CommRing A] [IsNoetherianRing A]
  {L : Type*} [AddCommGroup L] [Module A L]
  [Module.Free A L] [Module.Finite A L]
  (n : ℕ) (h_rank : FiniteDimensional.finrank A L = n)
  (S : Set L)
  (h_li : LinearIndependent A ((↑) : S → L))
  (h_max : ∀ T : Set L, S ⊆ T → LinearIndependent A ((↑) : T → L) → S = T) :
  S.ncard = n := by
  sorry

