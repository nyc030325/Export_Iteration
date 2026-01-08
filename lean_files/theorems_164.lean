import Mathlib
import Mathlib.Tactic

theorem theorem_893857_problem
  (n : ℕ)
  (hn : n ≥ 1)
  (x y : Fin n → ℕ)
  (hx : Monotone x)
  (hy : Monotone y)
  (σ : Equiv.Perm (Fin n)) :
  ∑ i, max (x i) (y i) ≤ ∑ i, max (x i) (y (σ i)) := by
  sorry









theorem theorem_894595_problem (G₁ G₂ : Grp)
  (P : Grp → Prop)
  (h_iso : G₁ ≅ G₂)
  (h_invariant : ∀ (H₁ H₂ : Grp), (H₁ ≅ H₂) → (P H₁ ↔ P H₂)) :
  P G₁ ↔ P G₂ := by
  sorry



theorem theorem_894233_problem (V : Type*) [AddCommGroup V] [Module ℚ V]
  (b : Basis ℕ ℚ V) : Countable V := by
  sorry

theorem theorem_893608_problem (y : ℝ → ℝ)
  (h : Asymptotics.IsLittleO Filter.atTop
    (fun x => y x - Real.exp (x^2 / 2) * (1 + Real.sqrt (Real.pi / (2 * Real.exp 1))))
    (fun x => Real.exp (x^2 / 2))) :
  Asymptotics.IsEquivalent Filter.atTop y
    (fun x => (1 + Real.sqrt (Real.pi / (2 * Real.exp 1))) * Real.exp (x^2 / 2)) := by
  sorry



theorem theorem_894657_problem
  (a : ℕ → ℝ)
  (c : ℝ)
  (h0 : a 0 = c)
  (h1 : a 1 = 0)
  (h_rec : ∀ n, n ≥ 2 → a n = -a (n - 2) / (n * (3 * n + 1))) :
  ∀ m : ℕ, a (2 * m) =
    ((-1 : ℝ) ^ m * c) /
    ((2 : ℝ) ^ m * (Nat.factorial m : ℝ) * (∏ k in Finset.range m, ((6 * (k + 1) + 1) : ℝ))) := by
  sorry

theorem theorem_894602_problem (μ2 μ3 : ℝ) 
  (h_denom : 1 - μ2 / 2 ≠ 0) :
  let z_c_real := 1 - μ2 / 2
  let z_c_imag := - μ3 / 6
  let θ_c := z_c_imag / z_c_real
  let θ_s := 0
  let Δθ := |θ_c - θ_s|
  Δθ = |(μ3 / 6) / (1 - μ2 / 2)| := by
  sorry









theorem theorem_894206_problem (K : Type*) [Field K] [Algebra ℝ K] [FiniteDimensional ℝ K]
  (α : K) (h_not_real : α ∉ Set.range (algebraMap ℝ K)) :
  (minpoly ℝ α).natDegree = 2 := by
  sorry



theorem theorem_894471_problem (N : ℕ) (h : N > 0) :
  ∑ n in Finset.Icc 1 N, (n : ℚ)^2 = (N : ℚ) * (N + 1) * (2 * N + 1) / 6 := by
  sorry



theorem theorem_894549_problem (θ : ℝ)
  (h1 : 0 ≤ θ) (h2 : θ ≤ 2 * Real.pi)
  (h3 : Real.sin θ + Real.cos θ ≠ 0) :
  Filter.Tendsto (fun r : ℝ ↦ |r * (Real.sin θ + Real.cos θ)^3|) Filter.atTop Filter.atTop := by
  sorry

theorem theorem_895212_problem (LfP Lf ε : ℝ) 
  (hε : ε > 0) 
  (h : |LfP - Lf| < ε) : 
  Lf ≤ LfP + ε := by
  sorry

theorem theorem_889162_problem (p : ℝ) (hp : 1 < p) :
  Summable (fun n : ℕ => 1 / ((n + 2 : ℝ) * Real.log (n + 2) ^ p)) := by
  sorry

theorem theorem_895521_problem (k₁ k₂ : ℝ) (e : ℝ → ℝ)
  (hk1 : k₁ > 0)
  (hk2 : k₂ > 0)
  (he : ContDiff ℝ 2 e)
  (h_ode : ∀ t, deriv (deriv e) t + k₁ * e t + k₂ * deriv e t = 0) :
  Filter.Tendsto e Filter.atTop (nhds 0) := by
  sorry

theorem theorem_894904_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (M N : Submodule 𝕜 E)
  [FiniteDimensional 𝕜 M] [FiniteDimensional 𝕜 N]
  (h : FiniteDimensional.finrank 𝕜 N < FiniteDimensional.finrank 𝕜 M) :
  ∃ x₀ ∈ M, x₀ ≠ 0 ∧ Metric.infDist x₀ N = ‖x₀‖ := by
  sorry

theorem theorem_895211_problem (u v : ℕ → ℝ) (a b : ℝ)
  (ha : 0 < a) (hb : 0 < b)
  (hu : ∀ n, 0 < u n) (hv : ∀ n, 0 < v n)
  (h_conv : Summable (fun n ↦ min (u n) (v n) / (a + b))) :
  Summable (fun n ↦ (u n * v n) / (a * u n + b * v n)) := by
  sorry



theorem theorem_895428_problem (f g h : ℕ → ℝ) (c : ℝ)
  (h_init : f 1 = c)
  (h_rec : ∀ n, 2 ≤ n → f n = g n + h n * f (n - 1)) :
  ∀ n, 1 ≤ n → f n = c * (∏ k in Finset.Ico 2 (n + 1), h k) +
    ∑ j in Finset.Ico 2 (n + 1), (g j * ∏ k in Finset.Ico (j + 1) (n + 1), h k) := by
  sorry



theorem theorem_895869_problem {α β : Type*} [MetricSpace α] [MetricSpace β]
  (g : α → β) (K : Set α)
  (hK : IsCompact K)
  (hg : ContinuousOn g K) :
  UniformContinuousOn g K := by
  sorry

theorem theorem_892570_problem (p : ℕ) [Fact p.Prime] :
  ∃ f : ℚ_[p] → ℚ_[p], (∀ x, HasDerivAt f 0 x) ∧ ¬ IsLocallyConstant f := by
  sorry

theorem theorem_896364_problem
  (I : Set ℝ)
  (hI : IsOpen I)
  (y : ℝ → ℝ)
  (hy_diff : DifferentiableOn ℝ y I)
  (h_domain : ∀ x ∈ I, 0 ≤ x + y x + 1)
  (h_ode : ∀ x ∈ I, deriv y x = Real.sqrt (x + y x + 1)) :
  ∃ C : ℝ, ∀ x ∈ I,
    2 * Real.sqrt (x + y x + 1) - 2 * Real.log (Real.sqrt (x + y x + 1) + 1) = x + C := by
  sorry







theorem theorem_895715_problem (n : ℕ) :
  ∑ i in Finset.Icc 1 n, Nat.fib (3 * i) = (Nat.fib (3 * n + 2) - 1) / 2 := by
  sorry





theorem theorem_896154_problem
  (X : Type*)
  (g : ℕ → X → ℝ)
  (h_unif : ∃ S : X → ℝ, TendstoUniformly (fun N x ↦ ∑ n ∈ Finset.range N, g n x) S atTop)
  (n₀ : ℕ)
  (h_bound : ∀ n, n₀ < n → ∀ x : X, |g n x| < 1/2) :
  ∃ L : X → ℝ, TendstoUniformly (fun N x ↦ ∑ n ∈ Finset.Ioc n₀ N, Real.log (1 + g n x)) L atTop := by
  sorry

theorem theorem_895834_problem (n : ℕ) :
  (Finset.filter (fun r => Odd (Nat.choose n r)) (Finset.range (n + 1))).card =
  2 ^ ((Nat.digits 2 n).count 1) := by
  sorry

theorem theorem_896220_problem (y : ℝ → ℝ)
  (h_diff : ContDiff ℝ 2 y)
  (h_nz : ∀ x, y x ≠ 0)
  (h_ode : ∀ x, deriv (deriv y) x = - (deriv y x)^2 / y x) :
  ∃ C₁ C₂ : ℝ, ∀ x, (y x)^2 = C₁ * x + C₂ := by
  sorry



theorem theorem_896551_problem :
  let S : Set (ℂ × ℂ × ℂ) := { p |
    let x := p.1
    let y := p.2.1
    let z := p.2.2
    let dx := 3 * x^2 * y + z^3
    let dy := x^3 + 3 * y^2 * z
    let dz := y^3 + 3 * z^2 * x
    -- The gradient is parallel to the position vector (x, y, z)
    (dx * y = dy * x) ∧
    (dy * z = dz * y) ∧
    (dz * x = dx * z) ∧
    -- The point lies on the unit sphere
    (x^2 + y^2 + z^2 = 1)
  }
  Set.ncard S = 26 := by
  sorry



theorem theorem_896100_problem {K : Type*} [Field K] 
  (a' b' : K) (h2 : (2 : K) ≠ 0) :
  ∀ x y z : K, x ≠ 0 → 
  (y, y^2 - a' * x^2 - 2 * b' * x * z, 2 * x) ≠ (0, 0, 0) := by
  sorry







theorem theorem_896928_problem
  (m : ℝ)
  (x : ℝ → ℝ)
  (U : ℝ → ℝ)
  (hx : ContDiff ℝ 2 x)
  (hU : Differentiable ℝ U)
  (h_eom : ∀ t, m * deriv (deriv x) t = - deriv U (x t)) :
  ∀ t, deriv (fun t => (1 / 2 : ℝ) * m * (deriv x t) ^ 2 + U (x t)) t = 0 := by
  sorry

theorem theorem_896315_problem (E F : ℝ) (hF : F ≠ 0) (u : ℝ)
  (h_crit : -E * Real.sin u + F * Real.cos u = 0)
  (z : ℝ) (hz : z = Real.tan (u / 2)) :
  z = (-E + Real.sqrt (E ^ 2 + F ^ 2)) / F ∨
  z = (-E - Real.sqrt (E ^ 2 + F ^ 2)) / F := by
  sorry



theorem theorem_896444_problem 
  (n : ℕ) 
  (P : Fin n → ℝ) 
  (C : Fin n → Fin n → ℝ) 
  (D : Matrix (Fin n) (Fin n) ℝ)
  (hD : D = Matrix.of (fun i j => 2 * C i j))
  (curvature : (Fin n → ℝ) → ℝ)
  (h_curvature : ∀ Q, curvature Q = ∑ i, (Matrix.dotProduct (C i) Q)^2) :
  (∀ Q : Fin n → ℝ, curvature P ≤ curvature Q) ↔ Matrix.mulVec D P = 0 := by
  sorry









theorem theorem_897107_problem
  (x : ℝ) (hx : x > 0)
  (n : ℕ) (hn : n > 0)
  (E : Set ℝ) (hE : E = {z : ℝ | z ≥ 0 ∧ z ^ n ≤ x})
  (y : ℝ) (hy : y = sSup E) :
  y ^ n = x := by
  sorry

theorem theorem_897292_problem (a_n : ℕ → ℝ) (a : ℝ)
  (h_bound : Bornology.IsBounded (Set.range a_n))
  (h_sub : ∀ φ : ℕ → ℕ, StrictMono φ →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Filter.Tendsto (a_n ∘ φ ∘ ψ) Filter.atTop (nhds a)) :
  Filter.Tendsto a_n Filter.atTop (nhds a) := by
  sorry



theorem theorem_896613_problem (n : ℕ) (x : Fin n → ℝ) :
  ∑ ξ : Fin n → ({-1, 1} : Set ℝ), (∑ i, (ξ i : ℝ) * x i)^2 = (2 : ℝ)^n * ∑ i, (x i)^2 := by
  sorry

















theorem theorem_897296_problem (F : Type*) [Field F] (f : Polynomial F) (hf : 0 < f.degree) :
  ∃ (E : Type*) (_ : Field E) (_ : Algebra F E),
    (∃ x : E, Polynomial.aeval x f = 0) ∧ ¬ Function.Surjective (algebraMap F E) := by
  sorry



theorem theorem_897573_problem (n : ℕ) (hn : n > 0) :
  IsCyclic (ZMod n)ˣ ↔
  (n = 2 ∨ n = 4 ∨
   (∃ (p k : ℕ), Nat.Prime p ∧ Odd p ∧ k > 0 ∧ n = p ^ k) ∨
   (∃ (p k : ℕ), Nat.Prime p ∧ Odd p ∧ k > 0 ∧ n = 2 * p ^ k)) := by
  sorry

theorem theorem_898468_problem (x : ℝ) (c : ℕ → ℝ)
  (h : ∃ f : ℕ → ℝ, (Asymptotics.IsBigO Filter.atTop f (fun n => 1 / (n : ℝ) ^ 2)) ∧
    (Filter.EventuallyEq Filter.atTop (fun n => Real.log |c n|)
      (fun n => ((n : ℝ) / 2) * Real.log (1 + 2 * x / n + f n)))) :
  Filter.Tendsto (fun n => |c n|) Filter.atTop (nhds (Real.exp x)) := by
  sorry



theorem theorem_896754_problem (t : ℂ) (h : 2 * t^2 - 2 * t + 1 ≠ 0) :
  (2 * t - 1 - Complex.I) / (2 * t^2 - 2 * t + 1) = (1 + Complex.I) / (-1 + (1 + Complex.I) * t) := by
  sorry





theorem theorem_897477_problem (a t ρ θ : ℝ)
  (ha : a > 0)
  (ht : t ∈ Set.Icc 0 Real.pi)
  (h_x : a * ρ * Real.cos θ = a * (t - Real.pi - Real.sin t))
  (h_y : a * ρ * Real.sin θ = a * (1 - Real.cos t)) :
  ρ * Real.cos θ = Real.arccos (1 - ρ * Real.sin θ) - Real.pi - Real.sin (Real.arccos (1 - ρ * Real.sin θ)) := by
  sorry



theorem theorem_897275_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : E × ℝ → E)
  (hf : Continuous f)
  (x_bar : ℝ → E)
  (h_min : ∀ a : ℝ, ∀ x : E, ‖f (x_bar a, a) - f (f (x_bar a, a), a)‖ ≤ ‖f (x, a) - f (f (x, a), a)‖)
  (h_unique : ∀ a : ℝ, ∀ y : E, (∀ x : E, ‖f (y, a) - f (f (y, a), a)‖ ≤ ‖f (x, a) - f (f (x, a), a)‖) → y = x_bar a) :
  Continuous x_bar := by
  sorry

theorem theorem_897892_problem (n : ℕ) 
  (y : Matrix (Fin n) (Fin 1) ℝ) 
  (A : Matrix (Fin n) (Fin n) ℝ) 
  (B : Matrix (Fin n) (Fin 1) ℝ) :
  y.transpose * y - (2 : ℝ) • (y.transpose * A * B) + B.transpose * A.transpose * A * B = 
  y.transpose * y - y.transpose * A * B - y.transpose * A * B + B.transpose * A.transpose * A * B := by
  sorry

theorem theorem_897719_problem : I = (4 - Real.pi) / (4 + Real.pi) := by
  sorry

theorem theorem_898512_problem :
  ∃ δ : SchwartzMap ℝ ℝ →L[ℝ] ℝ, ∀ f : SchwartzMap ℝ ℝ, δ f = f 0 := by
  sorry

theorem theorem_897452_problem :
  (∀ n : ℕ, Even n → n > 2 →
    ∃ p1 p2 : ℕ, Nat.Prime p1 ∧ Nat.Prime p2 ∧ p1 + p2 = n) ↔
  (∀ n : ℕ, Even n → n > 2 →
    ∃ p1 p2 : ℕ, Nat.Prime p1 ∧ Nat.Prime p2 ∧ p1 + p2 = n ∧
    3 * p1 > n ∧ 3 * p1 < 2 * n ∧ 3 * p2 > n ∧ 3 * p2 < 2 * n) := by
  sorry

theorem theorem_897904_problem (r : ℕ) (p : ℝ)
  (hr : 0 < r) (hp_pos : 0 < p) (hp_le : p ≤ 1) :
  ∑' (k : ℕ), (k : ℝ) * ((Nat.choose (k - 1) (r - 1) : ℝ) * p ^ r * (1 - p) ^ (k - r)) = r / p := by
  sorry

theorem theorem_898325_problem (x : ℝ) (h : 0 < x) : 
  deriv log x = 1 / x := by
  sorry

theorem theorem_898576_problem (A : Set ℝ) (s : ℝ)
  (h1 : A ≠ Set.univ)
  (h2 : A.Nonempty)
  (h3 : IsOpen A)
  (h4 : IsLUB A s) :
  s ∉ A := by
  sorry













theorem theorem_898739_problem (p : ℕ) (R : Type*) [CommRing R] [IsDomain R]
  [Fact p.Prime] [CharP R p] : IsDomain (WittVector p R) := by
  sorry









theorem theorem_899064_problem (a1 a2 a3 n : ℕ) :
  let G1 : Polynomial ℕ := ∑ i in Finset.range (a1 + 1), X ^ i
  let G2 : Polynomial ℕ := ∑ i in Finset.range (a2 + 1), X ^ (2 * i)
  let G3 : Polynomial ℕ := ∑ i in Finset.range (a3 + 1), X ^ (5 * i)
  let G := G1 * G2 * G3
  let solutions := (Finset.product (Finset.range (a1 + 1)) 
                   (Finset.product (Finset.range (a2 + 1)) (Finset.range (a3 + 1)))).filter 
                   (fun x => x.1 + 2 * x.2.1 + 5 * x.2.2 = n)
  G.coeff n = solutions.card := by
  sorry

theorem theorem_898898_problem
  (a b : ℝ)
  (fn : ℕ → ℝ → ℝ)
  (f : ℝ → ℝ)
  (h_cont_fn : ∀ n, ContinuousOn (fn n) (Set.Icc a b))
  (h_cont_f : ContinuousOn f (Set.Icc a b))
  (h_pointwise : ∀ x ∈ Set.Icc a b, Filter.Tendsto (fun n ↦ fn n x) Filter.atTop (nhds (f x)))
  (h_bound : ∃ M > 0, ∀ n, ∀ x ∈ Set.Icc a b, |fn n x| < M)
  (h_equi : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |x - y| < δ → ∀ n, |fn n x - fn n y| < ε) :
  TendstoUniformlyOn fn f Filter.atTop (Set.Icc a b) := by
  sorry



