import Mathlib
import Mathlib.Tactic

theorem theorem_1023081_problem {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] (S T : Module.End F V) :
  IsConj S T ↔ ∃ P : V ≃ₗ[F] V, T = P.symm.conj S := by
  sorry





theorem theorem_1023318_problem (G : Type*) [Group G]
  (h_fg : Group.FG G)
  (h_solvable : IsSolvable G)
  (h_torsion : ∀ g : G, IsOfFinOrder g) :
  Finite G := by
  sorry

theorem theorem_1023271_problem (n : ℕ) (hn : n > 0) :
  let C_n : Set (Fin n → ℝ) := {x | ∑ i, |x i| ≤ 1}
  let Q_n : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {p | ∑ i, p.2 i = 1 ∧ ∀ i, -p.2 i ≤ p.1 i ∧ p.1 i ≤ p.2 i}
  let π : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) := Prod.fst
  π '' Q_n = C_n := by
  sorry

theorem theorem_1023310_problem
  {X : Type*} [TopologicalSpace X] [T2Space X]
  (f : X → X) (x₀ : X)
  (hf : Continuous f)
  (h_conv : Filter.Tendsto (fun k ↦ f^[k] x₀) Filter.atTop (nhds x₀))
  (h_dist : ∀ i j : ℕ, 0 < i → 0 < j → i ≠ j → f^[i] x₀ ≠ f^[j] x₀) :
  f x₀ = x₀ := by
  sorry



theorem theorem_1023689_problem (f g : ℕ → ℝ)
  (h : ∃ c : ℝ, c > 0 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, |f n| ≤ c * |g n|) :
  f =O[atTop] g := by
  sorry





theorem theorem_1023458_problem (θ : ℝ) (hθ : 1 < θ) :
  True := by
  sorry

theorem theorem_1023727_problem
  (k Kbar : Type*) [Field k] [Field Kbar] [Algebra k Kbar] [IsAlgClosure k Kbar]
  (K : IntermediateField k Kbar) [IsGalois k K]
  (τ : K →ₐ[k] Kbar) :
  Set.range τ = (K : Set Kbar) := by
  sorry







theorem theorem_1023135_problem
  {G : Type*} [TopologicalSpace G] [Group G] [TopologicalGroup G]
  (A : ℝ → G) (hA : ContinuousOn A (Set.Icc 0 1))
  (V : Set G) (hV_open : IsOpen V) (hV_one : 1 ∈ V) :
  ∃ (m : ℕ) (t : Fin (m + 1) → ℝ),
    t 0 = 0 ∧
    t (Fin.last m) = 1 ∧
    (∀ i, t i ∈ Set.Icc 0 1) ∧
    ∀ k : Fin m, (A (t (Fin.castSucc k)))⁻¹ * A (t (Fin.succ k)) ∈ V := by
  sorry

theorem theorem_1024011_problem (x : ℝ) (h : x ∈ Set.Ioo (-1 : ℝ) 1) :
  HasDerivAt (fun y => - Real.arcsin y * Real.sqrt (1 - y^2) + y)
    (x * Real.arcsin x / Real.sqrt (1 - x^2)) x := by
  sorry





theorem theorem_1023608_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
  [T2Space M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [SmoothManifoldWithCorners J N]
  [T2Space N]
  (F G : M → N)
  (hF : ContMDiff I J ⊤ F)
  (hG : ContMDiff I J ⊤ G) :
  IsClosed {x : M | F x = G x ∧ HEq (mfderiv I J F x) (mfderiv I J G x)} := by
  sorry

theorem theorem_1023736_problem
  (n : ℕ)
  (P : Finset (ℝ × ℝ))
  (h_even : Even n)
  (h_card : P.card = n)
  (h_origin : ∀ p ∈ P, p ≠ 0)
  (h_general_pos : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p.1 * q.2 ≠ p.2 * q.1) :
  ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
    (P.filter (fun p => a * p.1 + b * p.2 > 0)).card = n / 2 ∧
    (P.filter (fun p => a * p.1 + b * p.2 < 0)).card = n / 2 := by
  sorry



theorem theorem_1024184_problem (D : Set ℝ) (f : ℝ → ℝ) (c L : ℝ)
  (h_cont : ContinuousOn f D)
  (h_cond : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, |x - c| < δ → |f x - L| ≤ ε) :
  Filter.Tendsto f (nhdsWithin c D) (nhds L) := by
  sorry

theorem theorem_1024405_problem (a b c d : ℝ) (y : ℝ → ℝ)
  (h : ∀ x, y x = a * Real.exp x + b * Real.exp (-x) + c * Real.cos x + d * Real.sin x) :
  ∀ x, iteratedDeriv 4 y x - y x = 0 := by
  sorry

theorem theorem_1024154_problem
  {W : Type*} [PartialOrder W]
  (dim : W → ℕ)
  -- Condition: Strict containment implies strictly larger dimension (from geometry of Schubert varieties)
  (h_mono : ∀ {w y : W}, w < y → dim w < dim y)
  -- Condition: Covering relation in Bruhat order implies dimension increases by exactly 1
  (h_cover : ∀ {w y : W}, w ⋖ y → dim y = dim w + 1)
  (w y : W) :
  -- Question: The graph edge condition (inclusion + dim diff 1) is equivalent to the covering relation
  (w ≤ y ∧ dim y - dim w = 1) ↔ w ⋖ y := by
  sorry





theorem theorem_1024635_problem
  (n : ℕ)
  (Q : Matrix (Fin n) (Fin n) ℝ)
  (N : Matrix (Fin n) (Fin n) ℝ)
  (s : Fin n → ℝ)
  (h_inv : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) - Q))
  (hN : N = ((1 : Matrix (Fin n) (Fin n) ℝ) - Q)⁻¹)
  (hs : ∀ i, s i = 1 + ∑ j, Q i j * s j) :
  ∀ i, s i = ∑ j, N i j := by
  sorry







theorem theorem_1023585_problem (R : Type*) [AddGroup R] [Mul R] [One R]
  (h1 : ∀ a b c : R, a * (b + c) = a * b + a * c)
  (h2 : ∀ a b c : R, (a + b) * c = a * c + b * c)
  (h3 : ∀ a : R, 1 * a = a)
  (h4 : ∀ a : R, a * 1 = a) :
  ∀ a b : R, a + b = b + a := by
  sorry







theorem theorem_1024955_problem
  (k : Type*) [Field k]
  (n : ℕ)
  (m : ℤ)
  (hm : m < 0) :
  ∀ (f : MvPolynomial (Fin (n + 1)) k),
  (∀ d ∈ f.support, (d.sum (fun _ e => e) : ℤ) = m) → f = 0 := by
  sorry



theorem theorem_1024860_problem (a : ℕ) (h : a ≥ 2) :
  ∫ x : ℝ, 1 / (x^2 + x + 1) ^ a = 
  2 * Real.pi * (Nat.choose (2 * a - 2) (a - 1) : ℝ) * Real.sqrt 3 / (3 : ℝ) ^ a := by
  sorry







theorem theorem_1025576_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  (A : ℝ → (X →L[𝕜] X))
  (hA : Continuous A)
  (t₀ : ℝ)
  (h_inv : IsUnit (1 + A t₀)) :
  ∃ U : Set ℝ, IsOpen U ∧ t₀ ∈ U ∧ ∀ t ∈ U, IsUnit (1 + A t) := by
  sorry



theorem theorem_1026085_problem (n : ℕ) (A₁ A₂ : Set (Fin n → ℝ))
  (h₁ : IsClosed A₁) (h₂ : IsClosed A₂) :
  IsClosed (A₁ ∪ A₂) := by
  sorry



theorem theorem_1025605_problem (x y a b : ℕ)
  (hx : x > 0) (hy : y > 0)
  (ha : a > 1) (hb : b > 1)
  (h : x^a - y^b = 1) :
  x = 3 ∧ a = 2 ∧ y = 2 ∧ b = 3 := by
  sorry

theorem theorem_1026303_problem (P : Type) (h : P → Empty) : IsEmpty P := by
  sorry

theorem theorem_1024843_problem
  (a b : ℝ)
  (f : ℝ → ℝ)
  (q : ℚ)
  (n : ℕ)
  (hn : n > 0) :
  Set.Countable {x | x ∈ Set.Ioo a b ∧
    ∀ y z, y ∈ Set.Ioo a b → z ∈ Set.Ioo a b →
    x - 1 / (n : ℝ) < y ∧ y < x ∧ x < z ∧ z < x + 1 / (n : ℝ) →
    f z > (q : ℝ) ∧ f y < (q : ℝ)} := by
  sorry

theorem theorem_1025891_problem :
  Filter.Tendsto (fun x : ℝ => Complex.log (x : ℂ) - Complex.log (1 - (x : ℂ)))
  Filter.atTop (nhds (-Real.pi * Complex.I)) := by
  sorry



theorem theorem_1026188_problem (n : ℕ) (hn : 1 < n) :
  ¬ ∃ f : (Fin n → ℝ) → ℝ,
    ContDiff ℝ 2 f ∧
    ∀ x : Fin n → ℝ, ∀ i j : Fin n,
      iteratedFDeriv ℝ 2 f x ![Pi.single i 1, Pi.single j 1] = x i * x j := by
  sorry



theorem theorem_1026471_problem {X : Type*} [MetricSpace X] (x y : X) (xn yn : ℕ → X) :
  ∀ n, |dist (xn n) (yn n) - dist x y| ≤ |dist (xn n) x + dist (yn n) y| := by
  sorry





theorem theorem_1026242_problem
  (A : Type*) [CommRing A]
  (M : Type*) [AddCommGroup M] [Module A M]
  (t : A) (ht : t ≠ 0)
  (h_t_ann : ∀ x ∈ Module.annihilator A M, t * x = 0)
  (n : ℕ)
  (G : Type*) [Group G]
  (rho : G →* Matrix.GeneralLinearGroup (Fin n) A)
  (M_mat : Matrix (Fin n) (Fin n) A)
  (h_comm : ∀ g : G, ∀ i j, (M_mat * (rho g : Matrix (Fin n) (Fin n) A) - (rho g : Matrix (Fin n) (Fin n) A) * M_mat) i j ∈ Module.annihilator A M)
  (k : Type*) [Field k]
  (pi : A →+* k)
  (h_pi_kill_ann : ∀ x ∈ Module.annihilator A M, pi x = 0)
  (h_schur : ∀ (X : Matrix (Fin n) (Fin n) k),
    (∀ g : G, X * ((rho g : Matrix (Fin n) (Fin n) A).map pi) = ((rho g : Matrix (Fin n) (Fin n) A).map pi) * X) →
    ∃ c : k, X = c • 1) :
  ∃ c : k, M_mat.map pi = c • 1 := by
  sorry



theorem theorem_1026479_problem
  (f : ℝ → ℝ → ℝ)
  (a b : ℝ → ℝ)
  (x : ℝ)
  (ha : Differentiable ℝ a)
  (hb : Differentiable ℝ b)
  (hf : Continuous (Function.uncurry f))
  (h_par_diff : ∀ y, Differentiable ℝ (fun x ↦ f x y))
  (h_par_cont : Continuous (Function.uncurry (fun x y ↦ deriv (fun t ↦ f t y) x))) :
  deriv (fun t ↦ ∫ y in a t..b t, f t y) x =
    deriv b x * f x (b x) - deriv a x * f x (a x) +
    ∫ y in a x..b x, deriv (fun t ↦ f t y) x := by
  sorry





theorem theorem_1026708_problem (n : ℕ) (S U : Matrix (Fin n) (Fin n) ℝ)
  (hS : S.IsSymm)
  (hU : U.transpose * U = 1) :
  Matrix.trace (U * S * U.transpose) = Matrix.trace S := by
  sorry



theorem theorem_1026399_problem
  (D : Set (ℝ × ℝ))
  (hD : IsOpen D)
  (f g : ℝ × ℝ → ℝ)
  (hf : ContDiffOn ℝ 1 f D)
  (hg : ContDiffOn ℝ 1 g D)
  (φ : ℝ × ℝ → ℝ)
  (hφ : ContDiffOn ℝ 1 φ D)
  (h_sign : (∀ p ∈ D, deriv (fun x => φ (x, p.2) * f (x, p.2)) p.1 +
                      deriv (fun y => φ (p.1, y) * g (p.1, y)) p.2 > 0) ∨
            (∀ p ∈ D, deriv (fun x => φ (x, p.2) * f (x, p.2)) p.1 +
                      deriv (fun y => φ (p.1, y) * g (p.1, y)) p.2 < 0)) :
  ¬ ∃ (γ : ℝ → ℝ × ℝ) (T : ℝ),
    T > 0 ∧
    (∀ t, γ t ∈ D) ∧
    (∀ t, HasDerivAt γ (f (γ t), g (γ t)) t) ∧
    (∀ t, γ (t + T) = γ t) ∧
    ¬ (∃ c, ∀ t, γ t = c) := by
  sorry

theorem theorem_1026603_problem :
  ¬ ∃ (f₁ : ℝ → ℝ) (f₂ : ℝ → ℝ), ∀ a ∈ ({0, 1} : Set ℝ), ∀ b ∈ ({0, 1} : Set ℝ),
  max a b = f₁ a * f₂ b := by
  sorry



theorem theorem_1026918_problem (S : Type*) (m n : ℕ)
  (hm : m > 0) (hn : n > 0) :
  Nonempty ((Fin m → Fin n → S) ≃ (Fin m × Fin n → S)) := by
  sorry

theorem theorem_1027149_problem (D : Type*) (φ : D → Prop) :
  ∃ B : Set D, ∀ x : D, x ∈ B ↔ φ x := by
  sorry







theorem theorem_1027133_problem (X : Type*) [TopologicalSpace X] :
  Nonempty (X ≃ₜ X × ℕ) ↔
  ∃ (A B : Type*) (tA : TopologicalSpace A) (tB : TopologicalSpace B),
    Infinite B ∧ @DiscreteTopology B tB ∧
    Nonempty (@Homeomorph X (A × B) _ (by haveI := tA; haveI := tB; exact inferInstance)) := by
  sorry



theorem theorem_1027176_problem (a b w : ℝ)
  (h1 : a^2 + w^2 = 144)
  (h2 : b^2 + w^2 = 100)
  (h3 : a * b = 5 * (a + b)) :
  Real.sqrt ((144 - w^2) * (100 - w^2)) = 5 * (Real.sqrt (144 - w^2) + Real.sqrt (100 - w^2)) := by
  sorry



theorem theorem_1027308_problem
  (X Y : Type*)
  [TopologicalSpace X] [TopologicalSpace Y]
  (BU : Set (Set X)) (BL : Set (Set Y))
  (hBU : TopologicalSpace.IsTopologicalBasis BU)
  (hBL : TopologicalSpace.IsTopologicalBasis BL)
  (BUL : Set (Set (X × Y)))
  (hBUL_def : BUL = {W | ∃ U ∈ BU, ∃ V ∈ BL, W = U ×ˢ V}) :
  ∀ A : Set (X × Y), IsOpen A ↔ ∀ p ∈ A, ∃ W ∈ BUL, p ∈ W ∧ W ⊆ A := by
  sorry



theorem theorem_1027852_problem {L : FirstOrder.Language} (Γ : FirstOrder.Language.Theory L) :
  FirstOrder.Language.Theory.IsSatisfiable Γ ↔
  ∀ (S : Finset (FirstOrder.Language.Sentence L)), (S : Set (FirstOrder.Language.Sentence L)) ⊆ Γ →
  FirstOrder.Language.Theory.IsSatisfiable (S : Set (FirstOrder.Language.Sentence L)) := by
  sorry

theorem theorem_1027885_problem (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
  x^3 + y^3 ≥ x^2 * y + x * y^2 := by
  sorry



theorem theorem_1026473_problem (M : ZFSet) (h : M ⊆ M.powerset) :
  M.powerset = M := by
  sorry





theorem theorem_1028037_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (T S : X →L[𝕜] X)
  (x : X) :
  ‖T - S‖ * ‖x‖ ≥ ‖T x - S x‖ := by
  sorry





theorem theorem_1028083_problem
  (n : ℕ) (hn : 0 < n)
  (u : ℝ → ℝ) (hu : ∀ t, u t = (1 - t / (n : ℝ)) ^ n)
  (t : ℝ) :
  deriv u t = -(1 - t / (n : ℝ)) ^ (n - 1) := by
  sorry

theorem theorem_1028132_problem {α : Type*} (φ ψ : α → Prop) :
  (∀ x, φ x → ∃ x, ψ x) ↔ (∀ x, ¬ φ x ∨ ∃ y, ψ y) := by
  sorry





theorem theorem_1027998_problem
  (P : Type*) [PartialOrder P]
  (h_complete : ∀ C : Set P, IsChain (· ≤ ·) C → ∃ s, IsLUB C s)
  (x : ℕ → P)
  (h_mono : Monotone x) :
  ∃ s, IsLUB (Set.range x) s := by
  sorry

theorem theorem_1027958_problem
  (t₀ x₀ : ℝ)
  (x : ℝ → ℝ)
  (h_t₀ : t₀ > 0)
  (h_diff : ∀ t, t > 0 → DifferentiableAt ℝ x t)
  (h_ode : ∀ t, t > 0 → deriv x t + x t / Real.sqrt (1 + t^3) = 1 / t)
  (h_init : x t₀ = x₀) :
  ∀ t, t > 0 → x t = x₀ * Real.exp (- ∫ s in t₀..t, 1 / Real.sqrt (1 + s^3)) +
    Real.exp (- ∫ s in t₀..t, 1 / Real.sqrt (1 + s^3)) *
    ∫ r in t₀..t, Real.exp (∫ s in t₀..r, 1 / Real.sqrt (1 + s^3)) * (1 / r) := by
  sorry











theorem theorem_1027995_problem (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
  ∫ x in Set.Ioi 0, x * Real.cos (a * x) / (Real.exp (b * x) - 1) =
  1 / 2 * (1 / a ^ 2 - Real.pi ^ 2 * (1 / Real.sinh (a * Real.pi / b)) ^ 2 / b ^ 2) := by
  sorry

theorem theorem_1028534_problem
  (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
  (a_seq b_seq : ℕ → ℝ)
  (h_start : a_seq 0 = a ∧ b_seq 0 = b)
  (h_iter : ∀ n, a_seq (n + 1) = (a_seq n + b_seq n) / 2 ∧ b_seq (n + 1) = Real.sqrt (a_seq n * b_seq n))
  (agm : ℝ)
  (h_lim : Filter.Tendsto a_seq Filter.atTop (nhds agm)) :
  ∫ x in (0)..(Real.pi / 2), 1 / Real.sqrt (a^2 * (Real.cos x)^2 + b^2 * (Real.sin x)^2) = Real.pi / (2 * agm) := by
  sorry



theorem theorem_1028771_problem
  (n : ℕ)
  (s : Set (Fin n → ℝ))
  (f : (Fin n → ℝ) → ℝ)
  (hs : Convex ℝ s)
  (hf : ContDiffOn ℝ 2 f s)
  (h_hess : ∀ x ∈ s, ∀ v : Fin n → ℝ, 0 ≤ iteratedFDerivWithin ℝ 2 f s x ![v, v]) :
  ConvexOn ℝ s f := by
  sorry

