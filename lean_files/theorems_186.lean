import Mathlib
import Mathlib.Tactic

theorem theorem_1028140_problem (N : ℕ) (hN : N ≥ 2)
  (remaining_possibilities : ℕ → ℝ)
  (h_init : remaining_possibilities 0 = Nat.choose N 2)
  (h_step : ∀ k, remaining_possibilities (k + 1) ≤ remaining_possibilities k / 3) :
  remaining_possibilities (Nat.ceil (Real.log (Nat.choose N 2) / Real.log 3)) ≤ 1 := by
  sorry

theorem theorem_1028945_problem
  (n : ℕ)
  (γ : ℝ → (Fin n → ℝ))
  (hγ : ContDiff ℝ ⊤ γ)
  (t : ℝ)
  (μ : Fin n)
  (coord : (Fin n → ℝ) → ℝ)
  (hcoord : coord = fun p ↦ p μ) :
  (fderiv ℝ coord (γ t)) (deriv γ t) = deriv (coord ∘ γ) t := by
  sorry

theorem theorem_1028691_problem (n : ℕ) (hn : Odd n)
  [Module ℂ (Fin n → ℝ)]
  [IsScalarTower ℝ ℂ (Fin n → ℝ)] :
  False := by
  sorry







theorem theorem_1030001_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℕ)
  (hA_adj : ∀ i j, A i j = 0 ∨ A i j = 1)
  (h_loop : ∀ i, A i i = 0)
  (h_symm : ∀ i j, A i j = 1 → A j i = 0)
  (h_tree : (SimpleGraph.fromRel (λ i j => A i j = 1)).IsTree) :
  ∀ k, k ≥ n → A^k = 0 := by
  sorry







theorem theorem_1029937_problem
  (n : ℕ)
  (U V : Set (Fin n → ℝ))
  (hU : IsOpen U)
  (hV : IsOpen V)
  (f g : (Fin n → ℝ) → (Fin n → ℝ))
  (hf : Set.MapsTo f U V)
  (hg : Set.MapsTo g V U)
  (hfg : ∀ x ∈ U, g (f x) = x)
  (hgf : ∀ y ∈ V, f (g y) = y)
  (hf_smooth : ContDiffOn ℝ ⊤ f U)
  (hg_smooth : ContDiffOn ℝ ⊤ g V)
  (x : Fin n → ℝ)
  (hx : x ∈ U) :
  LinearMap.det ((fderiv ℝ f x).toLinearMap) ≠ 0 := by
  sorry





theorem theorem_1029357_problem {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
  Continuous f ↔ ∀ V : Set Y, IsOpen V → IsOpen (f ⁻¹' V) := by
  sorry





theorem theorem_1029884_problem
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : E → ℝ) (hf : Continuous f)
  (h : ∀ P Q : E, P ≠ Q →
    ∃ γ₁ γ₂ : Path P Q, γ₁ ≠ γ₂ ∧
      ∀ t₁ : unitInterval, ∃ t₂ : unitInterval,
        f (γ₁ t₁) = f (γ₂ t₂) ∧ ‖γ₁ t₁ - γ₂ t₂‖ > 0) :
  ∀ x y : E, f x = f y := by
  sorry







theorem theorem_1029666_problem (a : ℕ → ℝ)
  (h : ∀ n, a n = (n : ℝ) ^ Real.sqrt n / (n.factorial : ℝ)) :
  Summable a := by
  sorry



theorem theorem_1030244_problem
  (n : ℕ)
  (f : (Fin n → ℝ) → ℝ)
  (p : Fin n → ℝ)
  (hf : DifferentiableAt ℝ f p) :
  fderiv ℝ f p = ∑ i : Fin n, (fderiv ℝ f p (Pi.basisFun ℝ (Fin n) i)) • (ContinuousLinearMap.proj i) := by
  sorry











theorem theorem_1030636_problem
  (M : ℝ → ℝ)
  (h_pos : ∀ x, 0 < M x)
  (h_eq : ∀ x y, M (x + y) = M x * M y)
  (h_cont : Continuous M) :
  ∃ c : ℝ, ∀ x, M x = Real.exp (c * x) := by
  sorry











theorem theorem_1030879_problem :
  ¬ ∃ X : ZFSet, ∀ A : ZFSet, A ∈ X ↔ {x | x ∈ A}.Countable := by
  sorry

theorem theorem_1030834_problem (a b : ℝ) (f_n : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (g : ℝ → ℝ)
  (h_unif : TendstoUniformlyOn f_n f Filter.atTop (Set.Icc a b))
  (h_g_cont : UniformContinuousOn g (f '' Set.Icc a b)) :
  TendstoUniformlyOn (fun n x ↦ g (f_n n x)) (fun x ↦ g (f x)) Filter.atTop (Set.Icc a b) := by
  sorry













theorem theorem_1031336_problem :
  ∃ f g : ℝ → ℝ,
    ContinuousOn f (Set.Ici 0) ∧
    ContinuousOn g (Set.Ici 0) ∧
    StrictConvexOn ℝ (Set.Ici 0) f ∧
    StrictConvexOn ℝ (Set.Ici 0) g ∧
    (∀ x, 0 ≤ x → 0 ≤ f x) ∧
    (∀ x, 0 ≤ x → 0 ≤ g x) ∧
    Filter.Tendsto (fun x ↦ f x / g x) Filter.atTop Filter.atTop ∧
    ({x | 0 ≤ x ∧ f x = g x}).Infinite := by
  sorry



theorem theorem_1031449_problem (θ k₁ k₂ : ℝ)
  (a b c : ℂ)
  (ha : a = Complex.exp (k₁ * Complex.I))
  (hb : b = Complex.exp (k₂ * Complex.I))
  (hc : c = Complex.exp (θ * Complex.I))
  (h_rel : c = -(a * b + 1 - 2 * a) / (a * b + 1 - 2 * b)) :
  2 * Real.cot (θ / 2) = Real.cot (k₁ / 2) - Real.cot (k₂ / 2) := by
  sorry



theorem theorem_1032021_problem (A : Type*) [CommRing A] (h : A) (h_ne_zero : h ≠ 0)
  (n : ℕ) (hn : n > 0) :
  {p : PrimeSpectrum A | h ∉ p.asIdeal} = {p : PrimeSpectrum A | h ^ n ∉ p.asIdeal} := by
  sorry

theorem theorem_1031982_problem (n : ℕ) (f : Polynomial ℝ)
  (h1 : f.degree = n)
  (h2 : n ≥ 1) :
  Polynomial.derivative (Polynomial.derivative f) ≠ -f := by
  sorry

theorem theorem_1031897_problem
  {n : ℕ}
  (R : Fin n → Fin n → Fin n → Fin n → ℝ)
  (h_anti_first : ∀ a b c d, R a b c d = -R b a c d)
  (h_anti_last : ∀ a b c d, R a b c d = -R a b d c)
  (a b c d : Fin n)
  (h_degen : a = b ∨ c = d) :
  R a b c d = 0 := by
  sorry



theorem theorem_1031613_problem (P : Prop) (h_LEM : ∀ (Q : Prop), Q ∨ ¬Q) : P ∨ ¬P := by
  sorry

theorem theorem_1031559_problem
  {F : Type*} [Field F]
  {n : ℕ}
  (d e : Fin n → ℕ)
  (A : (Π i, Fin (d i)) → F)
  (B : (Π i, Fin (e i)) → F) :
  (∑ x : Π i, Fin (d i) × Fin (e i), A (fun i ↦ (x i).1) * B (fun i ↦ (x i).2)) =
  (∑ x : Π i, Fin (d i), A x) * (∑ x : Π i, Fin (e i), B x) := by
  sorry

theorem theorem_1031717_problem
  {X : Type*} [MetricSpace X]
  (f_n : ℕ → X → ℝ)
  (f : X → ℝ)
  (h_cont : ∀ n, Continuous (f_n n))
  (h_unif : TendstoUniformly f_n f Filter.atTop) :
  Continuous f := by
  sorry

theorem theorem_1031189_problem (z : ℂ)
  (h : Complex.cos z = 3 / 4 + Complex.I / 4) :
  ∃ n : ℤ, z = (Real.pi / 4 : ℂ) + 2 * (n : ℂ) * Real.pi - (Complex.I / 2) * Real.log 2 ∨
           z = -((Real.pi / 4 : ℂ) + 2 * (n : ℂ) * Real.pi - (Complex.I / 2) * Real.log 2) := by
  sorry

theorem theorem_1031478_problem (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n) :
  ((n : ℝ) / (k : ℝ)) ^ k ≤ (Nat.choose n k : ℝ) := by
  sorry



theorem theorem_1031880_problem (K : Type*) [Field K] [NumberField K]
  (n : ℕ) (hn : FiniteDimensional.finrank ℚ K = n)
  (η : Basis (Fin n) ℤ (NumberField.RingOfIntegers K))
  (A : Matrix (Fin n) (Fin n) ℚ)
  (hA : ∀ i j, A i j = Algebra.trace ℚ K ((η i : K) * (η j : K))) :
  (NumberField.discr K : ℚ) = Matrix.det A := by
  sorry



















theorem theorem_1033036_problem (f : ℝ → ℝ)
  (h : ∀ M : ℝ, M > 0 → ContinuousOn f (Set.Icc (-M) M) ∧ DifferentiableOn ℝ f (Set.Icc (-M) M)) :
  Continuous f ∧ Differentiable ℝ f := by
  sorry

theorem theorem_1032843_problem 
  (n m : ℕ)
  (F : Matrix (Fin n) (Fin n) ℝ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hF : Invertible F)
  (hA_sym : A.IsSymm)
  (hA_pos : A.PosSemidef)
  (B : Matrix (Fin n) (Fin n) ℝ)
  (hB : B = F.transpose * F)
  (C : ℝ)
  -- Constraint: Sum of squared Euclidean distances between rows is constant C
  (constraint : Matrix (Fin n) (Fin m) ℝ → Prop)
  (h_constraint : ∀ X, constraint X ↔ (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin m, (X i k - X j k)^2) = C)
  -- Objective function
  -- Note: trace(A Y^T Y) in the problem text has a dimension mismatch for A:nxn and Y:nxm. 
  -- We interpret it as trace(Y^T A Y) (trace of weighted Gram matrix) or trace(A Y Y^T), which are scalar-equivalent.
  (obj : Matrix (Fin n) (Fin m) ℝ → ℝ)
  (h_obj : ∀ Y, obj Y = (Y.transpose * A * Y).trace)
  -- Y* is the minimizer of the problem in the Y domain
  (Y_star : Matrix (Fin n) (Fin m) ℝ)
  (h_opt_Y : constraint (F⁻¹ * Y_star) ∧ ∀ Y, constraint (F⁻¹ * Y) → obj Y_star ≤ obj Y) :
  -- Conclusion: X* = F⁻¹ Y* is the minimizer in the X domain
  let X_star := F⁻¹ * Y_star
  constraint X_star ∧ ∀ X, constraint X → obj (F * X_star) ≤ obj (F * X) := by
  sorry

theorem theorem_1032830_problem 
  (ρ g h₀ p₀ : ℝ) 
  (p : ℝ → ℝ) 
  (h_static_equilibrium : ∀ x, HasDerivAt p (ρ * g) x) 
  (h_boundary : p h₀ = p₀) 
  (h : ℝ) : 
  p h = p₀ + ρ * g * (h - h₀) := by
  sorry



theorem theorem_1032642_problem (ρ ν x : ℝ) (f : ℝ → ℝ) 
  (hf : ContDiff ℝ 2 f) :
  -- The "True" differential parameters given by the standard Itô formula
  let standard_drift := (deriv f x) * ρ + (1 / 2) * (deriv (deriv f) x) * (ν ^ 2)
  let standard_diffusion := (deriv f x) * ν
  
  -- The parameters derived from the "Second Form" expression in the problem:
  -- Term 1: f'(x) dX, where dX has drift ρ and diffusion ν
  let form_term1_drift := (deriv f x) * ρ
  let form_term1_diff := (deriv f x) * ν
  -- Term 2: (1/2) f''(x) ν^2 dt, where dt has drift 1 and diffusion 0
  let form_term2_drift := (1 / 2) * (deriv (deriv f) x) * (ν ^ 2)
  let form_term2_diff := 0
  
  -- The claim is that the Second Form sums to the Standard Form
  standard_drift = form_term1_drift + form_term2_drift ∧ 
  standard_diffusion = form_term1_diff + form_term2_diff := by
  sorry

theorem theorem_1032855_problem (x : ℝ) (h : x > 1) :
  Real.Gamma x = (x - 1) * Real.Gamma (x - 1) := by
  sorry





theorem theorem_1031797_problem
  (D τ x₁ x₂ a : ℝ)
  (hD : 0 < D)
  (hτ : 0 < τ)
  (hx : x₁ < x₂)
  (ha : a = (x₂ - x₁) / (2 * Real.pi * Real.sqrt (D * τ))) :
  (∑' k : ℕ, if 2 ≤ k then
    (2 / (x₂ - x₁)) * (D * (2 * (k : ℝ) + 1)^2 * Real.pi^2 / (x₂ - x₁)^2 + 1 / τ)⁻¹
   else 0) =
  ((x₂ - x₁) / (4 * Real.pi^2 * D)) *
  ((Real.pi * Real.tanh (Real.pi * a)) / a - 8 / (1 + 4 * a^2) - 8 / (9 + 4 * a^2)) := by
  sorry





theorem theorem_1033185_problem
  {X : Type*} [MetricSpace X]
  (a : ℕ → X)
  (ξ η : X)
  (h_cauchy : CauchySeq a)
  (hξ : MapClusterPt ξ atTop a)
  (hη : MapClusterPt η atTop a) :
  ξ = η := by
  sorry





theorem theorem_1033094_problem
  (X : Type*)
  [TopologicalSpace X]
  (h_indiscrete : ∀ U : Set X, IsOpen U ↔ U = ∅ ∨ U = Set.univ)
  (x₀ : X)
  (γ : Path x₀ x₀) :
  Path.Homotopic γ (Path.refl x₀) := by
  sorry





theorem theorem_1033286_problem (n : ℕ)
  (M : Set (List ℕ))
  (hM : M = ⋃ k ∈ Finset.range (n + 1), {l : List ℕ | l.length = k}) :
  Set.Countable M := by
  sorry







theorem theorem_1033645_problem (n : ℕ) :
  ∑ k in Finset.range (n + 1), (Nat.choose n k : ℝ) * (-1 : ℝ) ^ k / ((k + 1 : ℝ) ^ 2) =
  (∑ k in Finset.range (n + 1), (1 : ℝ) / (k + 1)) / (n + 1) := by
  sorry



theorem theorem_1033414_problem
  (N : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
  (P : Matrix (Fin 2) (Fin 2) ℝ)
  (hP : P = !![0, 1; 1, 0])
  (h_comm : ∀ z1 z2, N z1 * N z2 = P * N z2 * N z1 * P) :
  ∀ z1 z2, let Ω := N z1 * N z2 - N z2 * N z1; Ω 0 0 = -Ω 1 1 := by
  sorry

theorem theorem_1033513_problem
  (A : Type*) [CommRing A]
  (I : Ideal A)
  (S : Set A) :
  Ideal.span S * I = Ideal.span { x | ∃ s ∈ S, ∃ i ∈ I, x = s * i } := by
  sorry



theorem theorem_1033907_problem (p : ℕ) (hp : Nat.Prime p) (h : p ∣ (2^p + 1)) : p = 3 := by
  sorry



theorem theorem_1034179_problem
  (a : ℕ → ℝ)
  (r : ℝ)
  (f : ℝ → ℝ)
  (L : ℝ)
  (h_r : 0 < r)
  (h_a : ∀ n, 0 < a n ∧ a n < r)
  (h_sum : Summable a)
  (h_L : 0 < L)
  (h_lim : Filter.Tendsto (fun x ↦ f x / x) (nhdsWithin 0 (Set.Ioi 0)) (nhds L))
  (h_bound : ∃ δ > 0, ∃ M, ∀ x, 0 < x ∧ x < δ → |f x / x| ≤ M) :
  Summable (fun n ↦ f (a n)) := by
  sorry





theorem theorem_1034285_problem (p : ℕ) (hp : Nat.Prime p) :
  ∃ q : ℕ, Nat.Prime q ∧ q > p := by
  sorry

theorem theorem_1034270_problem {α : Type*} (n : ℕ)
  (U V : List α)
  (hU_len : U.length = n)
  (hV_len : V.length = n)
  (compatible : List α → List α → Prop)
  (h_compat : compatible U V) :
  U = V := by
  sorry

theorem theorem_1034620_problem (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
  (h_cont : ContinuousOn f (Set.Icc a b))
  (h_diff : DifferentiableOn ℝ f (Set.Ioo a b)) :
  ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a) := by
  sorry

