import Mathlib
import Mathlib.Tactic















theorem theorem_936132_problem (a b x : ℝ)
  (ha : 0 < a)
  (hx : |x + b| < a) :
  HasDerivAt (fun x => Real.arcsin ((x + b) / a)) (1 / Real.sqrt (a ^ 2 - (x + b) ^ 2)) x := by
  sorry



theorem theorem_936176_problem (R : Type*) [CommRing R] (x y a : R)
  (I₀ J I : Ideal R)
  (hI₀ : I₀ = Ideal.span {x, y})
  (hJ : J = Ideal.span {a})
  (hI : I = I₀ * J)
  (h_nprin : ¬ I₀.IsPrincipal)
  (h_nzd : a ∈ nonZeroDivisors R) :
  ¬ I.IsPrincipal := by
  sorry





theorem theorem_936454_problem
  {G : Type*} [Group G] [Finite G]
  (H : Subgroup G)
  (h_cond : ∃ g : G, ∀ h : H, orderOf g ≠ orderOf (h : G)) :
  (⋃ x : G, (H.map (MulAut.conj x).toMonoidHom : Set G)) ≠ Set.univ := by
  sorry

theorem theorem_935780_problem (x : ℕ) (a : ℕ → ℝ)
  (h_a : ∀ n, a n = 2 * n) :
  ∑ n in Finset.Ico 1 (x + 1), a n * ((x : ℝ) - n) = (x * (x + 1) * ((x : ℝ) - 1)) / 3 := by
  sorry

theorem theorem_936505_problem {G : Type*} [Group G] (U : Subgroup G) :
  Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer U := by
  sorry















theorem theorem_935596_problem (p q : ℝ)
  (hp_pos : 0 < p) (hp_lt_1 : p < 1)
  (hq : q = 1 - p) :
  (∑' k : ℕ, (k + 1 : ℝ) * p ^ k * q) + (∑' k : ℕ, (k + 1 : ℝ) * q ^ k * p) = 1 / p + 1 / q := by
  sorry



theorem theorem_936533_problem
  (f : ℤ → ℝ)
  (a_min a_max b_min b_max : ℤ)
  (ha : a_min ≤ a_max)
  (hb : b_min ≤ b_max) :
  ∑ a in Finset.Icc a_min a_max, ∑ b in Finset.Icc b_min b_max, f (a + b) =
  ∑ m in Finset.Icc (a_min + b_min) (a_max + b_max),
    f m * ((min a_max (m - b_min) + 1 - max a_min (m - b_max) : ℤ) : ℝ) := by
  sorry



theorem theorem_937024_problem (A : Prop) (h : False) : A := by
  sorry

theorem theorem_936946_problem
  (a b : ℕ → ℝ)
  (L : ℝ)
  (h_mono : StrictMono b)
  (h_inf : Filter.Tendsto b Filter.atTop Filter.atTop)
  (h_lim : Filter.Tendsto (fun n ↦ (a (n + 1) - a n) / (b (n + 1) - b n)) Filter.atTop (nhds L)) :
  Filter.Tendsto (fun n ↦ a n / b n) Filter.atTop (nhds L) := by
  sorry

theorem theorem_937344_problem (x y z : ℝ) 
  (h : y^2 + z^2 - 2 * y + x^2 = 0) :
  ∃ θ ∈ Set.Icc 0 Real.pi, ∃ ϕ ∈ Set.Ico 0 (2 * Real.pi),
    x = Real.cos θ ∧ 
    y = 1 + Real.sin θ * Real.cos ϕ ∧ 
    z = Real.sin θ * Real.sin ϕ := by
  sorry







theorem theorem_937081_problem (c : ℝ) (h : c < 0) :
  ¬ ∃ x y z : ℝ, 2 * (x - 2)^2 + (y - x)^2 + 2 * (z - 4)^2 = c := by
  sorry



theorem theorem_937066_problem {X : Type*} [TopologicalSpace X] (U V : Set X)
  (hV : IsOpen V) :
  closure (U ∩ V) = closure U ∩ V := by
  sorry

theorem theorem_937399_problem (k : ℕ) (a : ℝ) (h : 1 < a) :
  ∑' n : ℕ, (-1 : ℝ) ^ n * (n.choose k) * (a - 1) ^ (n - k) = (-1 : ℝ) ^ k * a ^ (-(k + 1 : ℤ)) := by
  sorry



theorem theorem_937688_problem (f : ℂ → ℂ) 
  (h_entire : Differentiable ℂ f) 
  (h_nonvanish : ∀ z, f z ≠ 0) :
  ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) := by
  sorry

theorem theorem_937129_problem (a : ℕ → ℝ)
  (h : ∀ n : ℕ, n ≥ 2 → a n = 1 / (Real.log n) ^ (Real.log (Real.log n))) :
  ¬ Summable a := by
  sorry

theorem theorem_937721_problem
  (n : ℕ)
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (hK : IsCompact K)
  (f : K → ℝ)
  (hf : Continuous f) :
  ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g ∧ ∀ x : K, g x = f x := by
  sorry

theorem theorem_937660_problem (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
  let γ : ℝ → ℂ := fun t ↦ (a : ℂ) * (Real.cos t : ℂ) + Complex.I * (b : ℂ) * (Real.sin t : ℂ)
  (1 / (2 * (Real.pi : ℂ) * Complex.I)) * ∫ t in (0)..(2 * Real.pi), (deriv γ t) / (γ t) = 1 := by
  sorry

theorem theorem_937846_problem
  (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (J K : Module.End ℝ V)
  (hJ : J ^ 2 = -1)
  (hK : K ^ 2 = -1)
  (hJK : J * K = -(K * J)) :
  4 ∣ FiniteDimensional.finrank ℝ V := by
  sorry





theorem theorem_937454_problem (x y : ℤ)
  (h_eq : x^2 - 5 * y^2 = -1)
  (h_pos_x : x > 0)
  (h_pos_y : y > 0)
  (h_prime : Nat.Prime y.natAbs) :
  x = 38 ∧ y = 17 := by
  sorry



theorem theorem_938118_problem 
  (F f : ℝ → ℝ) (CDF_U CDF_X : ℝ → ℝ)
  (hF : ∀ x, F x = 1 / (1 + Real.exp (-x)))
  (hF_range : ∀ x, 0 ≤ F x ∧ F x ≤ 1)
  (hf : ∀ x, f x = Real.exp (-x) / (1 + Real.exp (-x))^2)
  (hU : ∀ y, 0 ≤ y ∧ y ≤ 1 → CDF_U y = y)
  (hX : ∀ x, CDF_X x = CDF_U (F x)) :
  (∀ x, CDF_X x = F x) ∧ (∀ x, HasDerivAt F (f x) x) := by
  sorry



theorem theorem_938089_problem
  (f : ℝ × ℝ → ℝ)
  (h_cont : Continuous f)
  (h_bound : ∀ p, f p ≤ 1)
  (h_partials : (deriv (fun x => f (x, 0)) 0 ≠ 0) ∨ (deriv (fun y => f (0, y)) 0 ≠ 0))
  (h_lim : Filter.Tendsto f (nhds 0) (nhds 1)) :
  ∀ p, f p ≤ f 0 := by
  sorry



theorem theorem_938068_problem (k : ℕ) (t : Fin k → ℝ)
  (h_distinct : Function.Injective t) :
  LinearIndependent ℝ (fun i : Fin k ↦ (fun j : Fin k ↦ t i ^ (j : ℕ))) := by
  sorry



theorem theorem_938125_problem {X : Type*} [TopologicalSpace X]
  [LocallyCompactSpace X] [T2Space X] (A : Set X)
  (h : IsOpen A ∨ IsClosed A) :
  LocallyCompactSpace A := by
  sorry



theorem theorem_937836_problem
  (P Q R S f : ℂ → ℂ)
  (hP : ∃ p : Polynomial ℂ, ∀ z, P z = p.eval z)
  (hQ : ∃ q : Polynomial ℂ, ∀ z, Q z = q.eval z)
  (hR : ∀ z, R z = Complex.exp z)
  (hS : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ z, g z ≠ 0) ∧ ∀ z, S z = (g z)⁻¹)
  (hf : ∀ z, f z = P z + Q z * R z + S z) :
  Differentiable ℂ f := by
  sorry

theorem theorem_938627_problem (R : Type*) [CommRing R] (I : Ideal R) (h : I = ⊤) :
  Nonempty ((R ⧸ I) ≃+* PUnit) := by
  sorry

theorem theorem_938391_problem (y : PowerSeries ℝ)
  (h1 : PowerSeries.constantCoeff ℝ y = 0)
  (h2 : y + y^2 = (PowerSeries.X : PowerSeries ℝ)^3) :
  PowerSeries.trunc 15 y = Polynomial.X^3 - Polynomial.X^6 + 2 * Polynomial.X^9 - 5 * Polynomial.X^12 := by
  sorry

theorem theorem_938760_problem
  (X : Type*) [Countable X]
  (T : Type*) [TopologicalSpace T]
  (Y : Set (Set T))
  (hY_count : Set.Countable Y)
  (hY_inf : Set.Infinite Y)
  (hY_disj : Set.PairwiseDisjoint Y id)
  (hY_dense : ∀ A ∈ Y, Dense A) :
  ∃ f : Y → ℕ, Function.Bijective f := by
  sorry

theorem theorem_938821_problem (n : ℕ)
  (x₁ x₀ : Fin n → ℝ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (x'₁ x'₀ : Fin n → ℝ)
  (hA : A.transpose * A = 1)
  (h₁ : x'₁ = Matrix.mulVec A x₁)
  (h₀ : x'₀ = Matrix.mulVec A x₀) :
  Matrix.dotProduct x₁ x₀ = Matrix.dotProduct x'₁ x'₀ := by
  sorry





theorem theorem_938613_problem
  {K : Type*} [Field K]
  {n : ℕ}
  (b : Fin n → K)
  (hb : Function.Injective b)
  (f : K → K → K)
  (a : K) :
  ∀ i : Fin n,
    (∑ j : Fin n, f a (b j) * ∏ s in Finset.univ.erase j, (b i - b s) / (b j - b s)) = f a (b i) := by
  sorry





theorem theorem_937371_problem :
  ∃ (X : Type) (_ : TopologicalSpace X) (U V : Set X),
    IsOpen U ∧ IsOpen V ∧ interior (U ∩ V)ᶜ ≠ interior Uᶜ ∪ interior Vᶜ := by
  sorry

theorem theorem_939226_problem (x : ℝ) (hx : x > 0) :
  Filter.Tendsto (fun n : ℕ => (1 - (10 : ℝ) ^ (-(n : ℝ))) ^ ((10 : ℝ) ^ (n : ℝ))) Filter.atTop (nhds (Real.exp (-1))) := by
  sorry

theorem theorem_938657_problem
  (G : Type*) [Group G] [Fintype G] [DecidableEq G] [IsCyclic G]
  (n : ℕ)
  (m : ℕ) (hm : m = Fintype.card G) :
  Fintype.card {x : G | x ^ n = 1} = ∑ d in (Nat.divisors m).filter (· ∣ n), Nat.totient d := by
  sorry





theorem theorem_939434_problem
  (D : Set (ℝ × ℝ))
  (fx fy : ℝ → ℝ → ℝ) :
  let r_x : ℝ → ℝ → Fin 3 → ℝ := fun x y => ![1, 0, fx x y]
  let r_y : ℝ → ℝ → Fin 3 → ℝ := fun x y => ![0, 1, fy x y]
  let euclid_norm (v : Fin 3 → ℝ) : ℝ := Real.sqrt ((v 0)^2 + (v 1)^2 + (v 2)^2)
  ∫ p in D, euclid_norm (crossProduct (r_x p.1 p.2) (r_y p.1 p.2)) =
  ∫ p in D, Real.sqrt ((fx p.1 p.2)^2 + (fy p.1 p.2)^2 + 1) := by
  sorry





theorem theorem_939605_problem (a b : ℝ)
  (A B : Matrix (Fin 2) (Fin 2) ℝ)
  (hA : A = !![1, a; 0, 1])
  (hB : B = !![1, b; 0, 1]) :
  ∃ n : ℕ, n > 1 ∧ (A * B) ^ n = (B * A) ^ n := by
  sorry







theorem theorem_939686_problem (f : ℝ → ℝ)
  (h_cont : Continuous f)
  (h_per1 : ∀ x, f (x + 1) = f x)
  (h_per2 : ∀ x, f (x + Real.sqrt 2) = f x) :
  ∀ x y, f x = f y := by
  sorry

theorem theorem_937773_problem
  (r σ T : ℝ)
  (hr : 0 < r)
  (hσ : 0 < σ)
  (hT : 0 < T)
  (p : ℕ → ℝ)
  (hp : ∀ n : ℕ, p n =
    (Real.exp (r * (T / (n : ℝ))) - Real.exp (r * (T / (n : ℝ)) - 0.5 * σ ^ 2 * (T / (n : ℝ)) - σ * Real.sqrt (T / (n : ℝ)))) /
    (Real.exp (r * (T / (n : ℝ)) - 0.5 * σ ^ 2 * (T / (n : ℝ)) + σ * Real.sqrt (T / (n : ℝ))) -
     Real.exp (r * (T / (n : ℝ)) - 0.5 * σ ^ 2 * (T / (n : ℝ)) - σ * Real.sqrt (T / (n : ℝ))))) :
  Filter.Tendsto p Filter.atTop (nhds 0.5) := by
  sorry

theorem theorem_939290_problem
  (Ω : Type*) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
  (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
  (F : Type*) [Field F]
  (V : Type*) [AddCommGroup V] [Module F V]
  (n : ℕ) (v : Fin n → V) :
  True := by
  sorry

theorem theorem_940053_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  (W : Submodule F V)
  {n : ℕ} (v : Fin n → V) :
  LinearIndependent F (fun i => Submodule.mkQ W (v i)) ↔
  (∀ c : Fin n → F, (∑ i, c i • v i) ∈ W → c = 0) := by
  sorry















theorem theorem_939912_problem (a b : ℤ)
  (ha : 0 < a) (hb : 0 < b)
  (h : 7 * b^2 + 7 * b + 7 = a^4) :
  a = 7 ∧ b = 18 := by
  sorry





theorem theorem_940377_problem (a b c : ℤ) (x : ℚ)
  (h : x^3 + (a : ℚ) * x^2 + (b : ℚ) * x + (c : ℚ) = 0) :
  ∃ z : ℤ, x = z := by
  sorry

theorem theorem_939940_problem (a : ℕ → ℝ) (m : ℝ)
  (h1 : -2 < m) (h2 : m < 0)
  (h3 : Filter.Tendsto (fun n => a n / n) Filter.atTop (nhds m)) :
  Filter.Tendsto (fun n => (1 + a n / n) ^ n) Filter.atTop (nhds 0) := by
  sorry









theorem theorem_940384_problem
  -- We abstract the specific function spaces as Hilbert spaces V, H, B
  {V H B : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] -- Represents H^1(Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] -- Represents L^2(Ω)
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] -- Represents H^{1/2}(∂Ω)
  -- The trace operator γ : H^1 → H^{1/2}
  (γ : V →L[ℝ] B)
  -- The embedding ι : H^1 → L^2
  (ι : V →L[ℝ] H)
  -- The extension operator E : H^{1/2} → H^1 (implied by Lipschitz boundary)
  (E : B →L[ℝ] V)
  (hE : γ.comp E = ContinuousLinearMap.id ℝ B) -- Property: γ(E(φ)) = φ
  -- The form representing ∫ ∇u · ∇v (part of the H^1 inner product structure)
  (grad_form : V →L[ℝ] V →L[ℝ] ℝ)
  -- The function u ∈ H^1
  (u : V)
  -- The Laplacian Δu ∈ L^2
  (lap_u : H)
  -- The hypothesis that lap_u is the weak Laplacian of u:
  -- The integration by parts formula holds for functions vanishing on the boundary
  (h_weak_lap : ∀ v : V, γ v = 0 → grad_form u v + inner lap_u (ι v) = 0) :
  -- Conclusion: The normal derivative defines a functional in H^{-1/2} (Dual of B)
  -- The functional matches the Green's formula expression
  ∃ L : B →L[ℝ] ℝ, ∀ v : V, L (γ v) = grad_form u v + inner lap_u (ι v) := by
  sorry

theorem theorem_940669_problem (n : ℝ) (y : ℝ → ℝ)
  (h_n_nonneg : 0 ≤ n)
  (h_n_neq_1 : n ≠ 1)
  (h_diff_y : DifferentiableOn ℝ y (Set.Ioi 0))
  (h_diff_y' : DifferentiableOn ℝ (deriv y) (Set.Ioi 0))
  (h_ode : ∀ x, 0 < x → deriv (deriv y) x - x⁻¹ * deriv y x = x ^ (n - 1)) :
  ∃ C D : ℝ, ∀ x, 0 < x → y x = x ^ (n + 1) / ((n + 1) * (n - 1)) + C * x ^ 2 + D := by
  sorry





