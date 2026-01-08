import Mathlib
import Mathlib.Tactic



theorem theorem_870080_problem (μ σ : ℝ) (hσ : σ > 0) (x : ℝ) (hx : x > 0) :
  let f_Y := fun y : ℝ ↦ (1 / (σ * Real.sqrt (2 * Real.pi))) * Real.exp (-((y - μ) ^ 2) / (2 * σ ^ 2))
  let f_X := fun x : ℝ ↦ (1 / (σ * x * Real.sqrt (2 * Real.pi))) * Real.exp (-((Real.log x - μ) ^ 2) / (2 * σ ^ 2))
  f_X x = f_Y (Real.log x) * (1 / x) := by
  sorry



theorem theorem_868847_problem (ZF DC : Prop) (Consistent : Prop → Prop) :
  Consistent (ZF ∧ DC ∧ ¬ Nonempty (InnerProductSpace.Core ℝ (ContinuousMap ℝ ℝ))) := by
  sorry

theorem theorem_870379_problem {G : Type*} [Group G] (A B : Subgroup G) :
  ∃ H : Subgroup G, (H : Set G) = (A : Set G) ∩ (B : Set G) := by
  sorry





theorem theorem_870347_problem (θ : ℝ)
  (Rx : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
  (hRx : ∀ t, Rx t = !![1, 0, 0;
                        0, Real.cos t, -Real.sin t;
                        0, Real.sin t, Real.cos t]) :
  Rx θ * Rx (-θ) = 1 := by
  sorry

theorem theorem_870216_problem (p k q : ℕ)
  (hp : Nat.Prime p)
  (hk_gt_1 : 1 < k)
  (hk_lt_p : k < p)
  (hq_prime : Nat.Prime q)
  (hq_dvd : q ∣ k) :
  q < p := by
  sorry









theorem theorem_870362_problem (a b : ℝ)
  (ha : 0 ≤ a ∧ a ≤ 1)
  (hb : 0 ≤ b ∧ b ≤ 1) :
  (∃ P : Matrix (Fin 2) (Fin 2) ℝ, P ^ 2 = !![1 - a, a; b, 1 - b]) ↔ a + b ≤ 1 := by
  sorry

theorem theorem_869714_problem (f : ℝ → ℝ)
  (h : ∀ x : ℝ, x ≠ 0 → f x = x^3 + Real.cos (1 / x)) :
  Set.image f {x : ℝ | x ≠ 0} = Set.univ := by
  sorry





theorem theorem_870574_problem
  -- We model the algebra of vector fields (V) and Lie algebra valued forms (L)
  {V L : Type*} [LieRing V] [LieRing L]
  -- ω is the connection 1-form mapping vector fields to the Lie algebra L
  (omega : V → L)
  -- deriv represents the action X(f). We require that X(0) = 0.
  (deriv : V → L → L)
  (h_deriv_zero : ∀ (X : V), deriv X 0 = 0)
  -- Definition of the exterior derivative dω
  (d_omega : V → V → L)
  (h_d_omega : ∀ X Y, d_omega X Y = deriv X (omega Y) - deriv Y (omega X) - omega ⁅X, Y⁆)
  -- Definition of the curvature 2-form Ω = dω + (1/2)[ω,ω]
  -- Note: (1/2)[ω,ω](X,Y) simplifies to [ω(X), ω(Y)]
  (Omega : V → V → L)
  (h_Omega : ∀ X Y, Omega X Y = d_omega X Y + ⁅omega X, omega Y⁆)
  -- X and Y are horizontal vector fields
  (X Y : V)
  (hX : omega X = 0)
  (hY : omega Y = 0) :
  -- Conclusion
  Omega X Y = - omega ⁅X, Y⁆ := by
  sorry







theorem theorem_870562_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  (f g : V →ₗ[F] F)
  (h : LinearMap.ker f = LinearMap.ker g) :
  ∃ c : F, f = c • g := by
  sorry





theorem theorem_870556_problem (S : Set ℕ) (hS : S = { n : ℕ | n > 1 }) :
  ∃ p ∈ S, ∀ a b : ℕ, p = a * b → a = 1 ∨ b = 1 := by
  sorry

theorem theorem_871080_problem (a n : ℤ) (h : Int.gcd a n = 1) :
  a ^ Nat.totient n.natAbs ≡ 1 [ZMOD n] := by
  sorry





theorem theorem_871322_problem
  (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (hf : Differentiable ℝ f)
  (x_star e : EuclideanSpace ℝ (Fin n))
  (x : EuclideanSpace ℝ (Fin n))
  (hx : x = x_star + e) :
  f x = f x_star + ∫ (t : ℝ) in (0)..1, inner (gradient f (x_star + t • e)) e := by
  sorry





theorem theorem_871305_problem (y : ℝ → ℝ) (h_diff : Differentiable ℝ y)
  (h_ode : ∀ x, x ≠ 0 → x * deriv y x - y x + x^2 * ((y x)^2 + 2 * x * (y x) * deriv y x) = 0) :
  ∃ C₁ C₂ : ℝ, ∀ x, x ≠ 0 → x^2 * (y x)^2 - C₁ * x + y x = C₂ := by
  sorry

theorem theorem_871655_problem
  (f : ℝ → ℝ) (g : ℝ → ℝ) (a b : ℝ)
  (hab : a ≤ b)
  (hf_int : MeasureTheory.IntegrableOn f (Set.Icc a b) MeasureTheory.volume)
  (hf_bdd : BddAbove ((fun t => |f t|) '' Set.Icc a b))
  (hg_def : ∀ x ∈ Set.Icc a b, g x = ∫ t in Set.Icc a x, |f t|)
  (hg_lip : ∃ K, LipschitzOnWith K g (Set.Icc a b)) :
  ∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b →
  ∫ t in Set.uIcc x y, |f t| ≤ |x - y| * sSup ((fun t => |f t|) '' Set.Icc a b) := by
  sorry

theorem theorem_871600_problem (f : Polynomial ℚ)
  (h_real : (f.map (algebraMap ℚ ℂ)).roots.countP (fun z => z.im = 0) = 1)
  (h_complex : ∃ z ∈ (f.map (algebraMap ℚ ℂ)).roots, z.im ≠ 0) :
  Even (FiniteDimensional.finrank ℚ f.SplittingField) := by
  sorry

theorem theorem_871362_problem (W X Y Z : Prop) :
  ((W ∧ X ∧ Y) → Z) ↔ (W → (X → (Y → Z))) := by
  sorry



theorem theorem_870627_problem (t : ℝ) (h : t > 2) :
  HasDerivAt (fun x => (2 * Real.sqrt (x - 2) + Real.sqrt 2 * x * Real.arctan (Real.sqrt ((x - 2) / 2))) / (4 * x))
    (1 / (t ^ 2 * Real.sqrt (t - 2))) t := by
  sorry

theorem theorem_871311_problem (n : ℕ) (hn : n > 0) :
  let r2 := (Finset.filter (fun p : ℤ × ℤ => p.1^2 + p.2^2 = (n : ℤ))
    ((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ (Finset.Icc (-(n : ℤ)) (n : ℤ)))).card
  let d1 := ((Nat.divisors n).filter (fun d => d % 4 = 1)).card
  let d3 := ((Nat.divisors n).filter (fun d => d % 4 = 3)).card
  (r2 : ℤ) = 4 * ((d1 : ℤ) - (d3 : ℤ)) := by
  sorry











theorem theorem_872089_problem
  (n : ℕ)
  (I : Type*) [Finite I]
  (q : I → MvPolynomial (Fin n) ℝ)
  (S : Set (Fin n → ℝ))
  (hS : S = {x | ∀ i, MvPolynomial.eval x (q i) < 0})
  (h_close : 0 ∈ closure S) :
  ∃ ε > 0, ∃ F : (Fin n → ℝ) → (Fin n → ℝ),
    AnalyticOn ℝ F (Set.pi Set.univ (fun _ ↦ Set.Ico 0 ε)) ∧
    F 0 = 0 ∧
    ∀ t, (∀ i, 0 < t i) → (∀ i, t i < ε) → F t ∈ S := by
  sorry





theorem theorem_872325_problem
  (n : ℕ)
  (f : (Fin n → ℝ) → ℝ)
  (h_diff : ContDiff ℝ 2 f)
  (h_hess : ∀ x : Fin n → ℝ, ∀ u : Fin n → ℝ, u ≠ 0 →
    iteratedFDeriv ℝ 2 f x (fun _ ↦ u) > 0) :
  ConvexOn ℝ Set.univ f := by
  sorry





















theorem theorem_872771_problem (x : ℝ) (h : x > (3 : ℝ) ^ (1 / 3 : ℝ)) :
  HasDerivAt (fun x => (2 / 27 : ℝ) * x ^ (-(9 / 2 : ℝ)) * (x ^ 3 - 3) ^ (3 / 2 : ℝ))
    (Real.sqrt ((x ^ 3 - 3) / x ^ 11)) x := by
  sorry







theorem theorem_873420_problem (R : ℝ) (hR : 0 ≤ R) :
  MeasureTheory.Measure.hausdorffMeasure 2 (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) R) = 
  ENNReal.ofReal (4 * Real.pi * R ^ 2) := by
  sorry



theorem theorem_873108_problem
  (a b α β : ℝ)
  (h_interval : a < b)
  (h_α : α ∈ Set.Icc 0 (2 * Real.pi))
  (h_β : β ∈ Set.Icc 0 (2 * Real.pi))
  (h_cos_a : Real.cos α = a)
  (h_cos_b : Real.cos β = b) :
  let f : ℝ → ℝ := fun x ↦ (β - α) * ((x - a) / (b - a)) + α
  let g : ℝ → ℝ × ℝ := fun x ↦ (Real.cos (f x), Real.sin (f x))
  let S : Set (ℝ × ℝ) := g '' (Set.Icc a b)
  ∃ h : Homeomorph (Set.Icc a b) S, ∀ x : Set.Icc a b, h x = ⟨g x.1, Set.mem_image_of_mem g x.2⟩ := by
  sorry



theorem theorem_873486_problem 
  (G X : Type*) [Group G] [MulAction G X]
  (sim_G : X → X → Prop)
  (h_sim_def : ∀ x₁ x₂, sim_G x₁ x₂ ↔ ∃ g : G, x₂ = g • x₁)
  (X_slash_G : Set (Set X))
  (h_X_slash_G_def : X_slash_G = {s | ∃ x, s = {y | sim_G x y}}) :
  ⋃₀ X_slash_G = Set.univ := by
  sorry

theorem theorem_872668_problem (R : Type*) [Ring R] (x y : R) :
  let I_x : Submodule ℤ R :=
    Submodule.span ℤ {a | ∃ r s, a = r * x * s} ⊔
    Submodule.span ℤ {a | ∃ r, a = r * x} ⊔
    Submodule.span ℤ {a | ∃ s, a = x * s} ⊔
    Submodule.span ℤ {a | ∃ n : ℤ, a = n • x}
  let I_y : Submodule ℤ R :=
    Submodule.span ℤ {a | ∃ r s, a = r * y * s} ⊔
    Submodule.span ℤ {a | ∃ r, a = r * y} ⊔
    Submodule.span ℤ {a | ∃ s, a = y * s} ⊔
    Submodule.span ℤ {a | ∃ n : ℤ, a = n • y}
  I_x * I_y =
    Submodule.span ℤ {a | ∃ r s t, a = r * x * s * y * t} ⊔
    Submodule.span ℤ {a | ∃ r s, a = r * x * s * y} ⊔
    Submodule.span ℤ {a | ∃ r s, a = r * x * y * s} ⊔
    Submodule.span ℤ {a | ∃ r s, a = x * r * y * s} ⊔
    Submodule.span ℤ {a | ∃ r s, a = r * x * s * y} ⊔
    Submodule.span ℤ {a | ∃ r, a = x * r * y} ⊔
    Submodule.span ℤ {a | ∃ r, a = r * x * y} ⊔
    Submodule.span ℤ {a | ∃ s, a = x * y * s} ⊔
    Submodule.span ℤ {a | ∃ n : ℤ, a = n • (x * y)} := by
  sorry







theorem theorem_874074_problem (x : ℝ) 
  (f : ℝ → ℝ)
  (h : f x = 5 * x^2 + 4 * Real.exp (7 - x) - x^2 * Real.exp (7 - x) - 20) : 
  f x = Real.exp (-x) * (5 * Real.exp x - Real.exp 7) * (x - 2) * (x + 2) := by
  sorry

theorem theorem_873659_problem (R n phi d_lambda : ℝ)
  (hR : R > 0) (hn : n > 0)
  (d_phi : ℝ) (h_d_phi : d_phi = Real.pi / n)
  (meridional_arc : ℝ) (h_meridional_arc : meridional_arc = R * d_phi)
  (longitudinal_arc : ℝ) (h_longitudinal_arc : longitudinal_arc = R * Real.cos phi * d_lambda)
  (area_approx : ℝ) (h_area_approx : area_approx = R^2 * Real.cos phi * d_phi * d_lambda)
  (h_geometric_cond : longitudinal_arc = meridional_arc) :
  area_approx = (R * d_phi)^2 := by
  sorry







theorem theorem_873874_problem
  {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (g : X → ℝ)
  (E : ℕ → Set X)
  (h_domain : (⋃ n, E n) = Set.univ)
  (h_meas : ∀ n, MeasurableSet (E n))
  (h_cont : ∀ n, ContinuousOn g (E n)) :
  Measurable g := by
  sorry

theorem theorem_873749_problem
  (n : ℕ)
  (x : Fin n → ℝ)
  (X : ℝ) :
  sInf {v | ∃ (y : Fin n → ℝ) (s t : ℝ),
    (∀ i, y i = 0 ∨ y i = 1) ∧
    s ≥ 0 ∧ t ≥ 0 ∧
    (∑ i, x i * y i) - X = s - t ∧
    v = s + t} =
  sInf {v | ∃ (y : Fin n → ℝ),
    (∀ i, y i = 0 ∨ y i = 1) ∧
    v = |(∑ i, x i * y i) - X|} := by
  sorry

theorem theorem_874195_problem (y p q : ℝ → ℝ)
  (hy : ContDiff ℝ 2 y)
  (h_eq : ∀ x, x > 0 → x^2 * (deriv (deriv y) x) + p x * x * (deriv y x) + q x * y x = 0) :
  ∀ t, deriv (deriv (y ∘ Real.exp)) t + (p (Real.exp t) - 1) * deriv (y ∘ Real.exp) t +
    q (Real.exp t) * (y ∘ Real.exp) t = 0 := by
  sorry



theorem theorem_874499_problem (G : Type*) [Group G] :
  let ρ : G → Equiv.Perm G := fun g ↦ Equiv.mulLeft g
  Function.Injective ρ ∧ ∀ g h : G, ρ (g * h) = ρ g * ρ h := by
  sorry





















theorem theorem_875177_problem
  (I : Set ℝ)
  (y : ℝ → ℝ)
  (h_open : IsOpen I)
  (h_conn : IsConnected I)
  (h_diff : DifferentiableOn ℝ y I)
  (h_valid : ∀ x ∈ I, x ≠ 0 ∧ Real.cos x ≠ 0 ∧ Real.tan x ≠ 0)
  (h_ode : ∀ x ∈ I, x * deriv y x - y x = x^2 / (Real.tan x * (Real.cos x)^2)) :
  ∃ C : ℝ, ∀ x ∈ I, y x = x * Real.log (abs (Real.tan x)) + C * x := by
  sorry



theorem theorem_875836_problem (E : Set EReal)
  (h_nonempty : E.Nonempty)
  (h_sup : sSup E = ⊥) :
  E = {⊥} := by
  sorry









theorem theorem_875743_problem
  (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (U : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n))
  (hU : IsOpen U)
  (hx : x ∈ U)
  (h_diff : DifferentiableOn ℝ f U)
  (h_max : IsLocalMaxOn f U x) :
  gradient f x = 0 := by
  sorry





