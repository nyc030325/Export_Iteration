import Mathlib
import Mathlib.Tactic



theorem theorem_549413_problem 
  (EI T k p y₀ L σ ε d : ℝ)
  (w y : ℝ → ℝ)
  (hL : L ≠ 0)
  (hy₀ : y₀ ≠ 0)
  (h_diff_w : ContDiff ℝ 4 w)
  (h_diff_y : ContDiff ℝ 4 y)
  (h_ode : ∀ s, EI * (iteratedDeriv 4 w s) - T * (iteratedDeriv 2 w s) + k * (w s) = p)
  (h_sub : ∀ x, w (L * x) = y₀ * y x)
  (h_param_k : EI / L^4 = k)
  (h_param_sigma : k = σ)
  (h_param_T : y₀ * T / L^2 = 1)
  (h_param_eps : ε^2 = y₀ * σ)
  (h_param_d : d = p) :
  ∀ x, ε^2 * (iteratedDeriv 4 y x + y x) - iteratedDeriv 2 y x = d := by
  sorry



theorem theorem_550058_problem (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
  (h : Nonempty (CompositionSeries (Submodule R M))) :
  IsArtinian R M := by
  sorry



theorem theorem_550007_problem (G : Type*) [Group G] (H K : Subgroup G) 
  (hKH : K ≤ H) : 
  K ≤ H.normalizer := by
  sorry







theorem theorem_550423_problem (A : Type*) [CommRing A] (I : Ideal (PowerSeries A)) :
  ∃ J : Ideal A, (J : Set A) = { a : A | PowerSeries.C A a ∈ I } := by
  sorry







theorem theorem_549194_problem 
  (ε : ℕ → ℝ) 
  (hε : ∀ k, ε k = if Nat.Prime k then 1 else 0) : 
  ¬ Summable (fun k => ε k / k) := by
  sorry







theorem theorem_550968_problem (f : ℝ → ℝ) (r t : ℝ) (hr : r > 0) :
  (1 / (t - (t - r))) * ∫ t' in (t - r)..t, f t' = (1 / r) * ∫ t' in (t - r)..t, f t' := by
  sorry

theorem theorem_550838_problem (I : Set ℝ)
  (h_int : Set.OrdConnected I)
  (h_nontriv : Set.Nontrivial I) :
  Cardinal.mk I = Cardinal.mk ℝ := by
  sorry

theorem theorem_551011_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (A : V →ₗ[K] V)
  (h_sq : Squarefree (minpoly K A))
  (W : Submodule K V)
  (hW : Submodule.map A W ≤ W) :
  ∃ U : Submodule K V, Submodule.map A U ≤ U ∧ IsCompl W U := by
  sorry







theorem theorem_551545_problem
  (n : ℕ)
  (i j : Fin n)
  (PhaseSpace : Type*)
  -- q represents the generalized coordinates q_0, ..., q_{n-1} as functions on the PhaseSpace
  (q : Fin n → PhaseSpace → ℝ)
  -- partial_q k represents ∂/∂q_k, partial_p k represents ∂/∂p_k
  (partial_q : Fin n → (PhaseSpace → ℝ) → (PhaseSpace → ℝ))
  (partial_p : Fin n → (PhaseSpace → ℝ) → (PhaseSpace → ℝ))
  -- Condition: Partial derivatives of q_i w.r.t p_k vanish
  (h_dq_dp : ∀ (idx : Fin n) (k : Fin n), partial_p k (q idx) = 0)
  -- Condition: Partial derivatives of q_i w.r.t q_k are the Kronecker delta
  (h_dq_dq : ∀ (idx : Fin n) (k : Fin n), partial_q k (q idx) = fun _ => if idx = k then 1 else 0)
  -- Definition of the Poisson Bracket
  (poisson_bracket : (PhaseSpace → ℝ) → (PhaseSpace → ℝ) → (PhaseSpace → ℝ))
  (h_bracket_def : ∀ f g, poisson_bracket f g = fun x =>
    ∑ k : Fin n, (partial_q k f x * partial_p k g x - partial_p k f x * partial_q k g x)) :
  poisson_bracket (q i) (q j) = 0 := by
  sorry





theorem theorem_551351_problem
  (p k n : ℕ)
  (hp : p > 0)
  (hk : k > 0)
  (hn : n = p * k)
  (h_exists_m : ∃ m : ℕ, Nat.totient m = k)
  (h_eq : Nat.totient (p * k) / Nat.totient k + 1 = p) :
  p ∣ n := by
  sorry

theorem theorem_550835_problem (a x : ℝ) (ha : 0 < a) (hx : |x| < a) :
  HasDerivAt (fun t => (a^2 + t^2) / 2 * Real.sqrt ((a^2 - t^2) / (a^2 + t^2)) -
    a^2 * Real.arctan (Real.sqrt ((a^2 - t^2) / (a^2 + t^2))))
    (x * Real.sqrt ((a^2 - x^2) / (a^2 + x^2))) x := by
  sorry





theorem theorem_551627_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H')
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [SmoothManifoldWithCorners I' N]
  (A : Set M) (F : M → N) :
  SmoothOn I I' F A ↔
  ∀ p ∈ A, ∃ W, IsOpen W ∧ p ∈ W ∧
    ∃ (F_tilde : M → N), SmoothOn I I' F_tilde W ∧ Set.EqOn F_tilde F (W ∩ A) := by
  sorry

theorem theorem_551331_problem
  (E_U : ℝ → ℝ)
  (E_f : ℝ → ℝ)
  (h1 : ∀ c, E_U c = ∫ x in (0 : ℝ)..(1 : ℝ), (x - c))
  (h2 : ∀ c, E_f c = ∫ x in (0 : ℝ)..(1 : ℝ), (x - c) * (1 / 2 + x)) :
  ∃ c : ℝ, (E_U c < 0 ∧ E_f c > 0) ∨ (E_U c > 0 ∧ E_f c < 0) := by
  sorry

theorem theorem_551693_problem
  (N d : ℕ)
  (hN : 0 < N)
  (X₁ X₂ : Matrix (Fin d) (Fin N) ℝ)
  (w : Matrix (Fin d) (Fin 1) ℝ)
  (h_mean₁ : ∀ i, ∑ j, X₁ i j = 0)
  (h_mean₂ : ∀ i, ∑ j, X₂ i j = 0)
  (v₁ : ℝ) (hv₁ : v₁ = (w.transpose * X₁ * X₁.transpose * w) 0 0)
  (v₂ : ℝ) (hv₂ : v₂ = (w.transpose * X₂ * X₂.transpose * w) 0 0)
  (Var₁ : ℝ) (hVar₁ : Var₁ = (∑ j, ((w.transpose * X₁) 0 j - (∑ k, (w.transpose * X₁) 0 k) / N)^2) / N)
  (Var₂ : ℝ) (hVar₂ : Var₂ = (∑ j, ((w.transpose * X₂) 0 j - (∑ k, (w.transpose * X₂) 0 k) / N)^2) / N) :
  v₁ / v₂ = Var₁ / Var₂ := by
  sorry









theorem theorem_551731_problem
  (v_r v_theta : ℝ → ℝ → ℝ)
  (hat_v_r hat_v_theta : ℝ → ℝ → ℝ)
  (r theta : ℝ)
  (hr : r ≠ 0)
  -- Condition: Relationship between holonomic and normalized components based on scale factors
  -- ||e_r|| = 1 => v^r = hat_v^r
  (h_scale_r : ∀ x y, v_r x y = hat_v_r x y)
  -- ||e_theta|| = r => hat_v^theta = r * v^theta
  (h_scale_theta : ∀ x y, hat_v_theta x y = x * v_theta x y)
  -- Condition: Differentiability needed for partial derivatives
  (h_diff : DifferentiableAt ℝ (fun t => hat_v_r r t) theta)
  -- Condition: Definition of Holonomic Covariant Derivative in Cylindrical Coordinates
  -- Uses Christoffel symbol Γ^r_θθ = -r
  (nabla_holo : ℝ)
  (h_nabla_holo : nabla_holo = deriv (fun t => v_r r t) theta - r * v_theta r theta)
  -- Condition: Definition of Normalized Covariant Derivative
  -- Scaled by 1/||e_theta|| = 1/r
  (nabla_norm : ℝ)
  (h_nabla_norm : nabla_norm = (1 / r) * nabla_holo) :
  -- Conclusion
  nabla_norm = (1 / r) * deriv (fun t => hat_v_r r t) theta - (1 / r) * hat_v_theta r theta := by
  sorry

theorem theorem_551280_problem (P : ℤ → Prop) (a : ℤ)
  (h1 : a ≤ 0)
  (h2 : ∀ n : ℤ, n ≥ a → P n) :
  P 0 := by
  sorry





theorem theorem_552218_problem (a b : ℝ) (f g : ℝ → ℝ)
  (hab : a ≤ b)
  (hf : Measurable f)
  (hg : Measurable g) :
  |∫ x in a..b, f x * g x| ≤ Real.sqrt (∫ x in a..b, (f x)^2) * Real.sqrt (∫ x in a..b, (g x)^2) := by
  sorry









theorem theorem_552529_problem (y : ℝ → ℝ)
  (h : ∀ x : ℝ, HasDerivAt y (-(1 / 3 : ℝ)) x) :
  ∃ C : ℝ, ∀ x : ℝ, y x = -(1 / 3 : ℝ) * x + C := by
  sorry

theorem theorem_552040_problem
  (X Y : Type*)
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  -- Y is embedded in X (representing Y as a subspace)
  (ι : Y →ₗ[ℝ] X)
  (hι_inj : Function.Injective ι)
  (B_XX : Set X)
  (B_YY : Set Y)
  -- B_XX is the convex hull of two subsets
  (h_hull : ∃ S1 S2 : Set X, B_XX = convexHull ℝ (S1 ∪ S2))
  -- The norms are generated by these sets (interpreted as unit balls)
  (h_normX : Metric.closedBall 0 1 = closure B_XX)
  (h_normY : Metric.closedBall 0 1 = B_YY)
  -- Hypothesis: Intersection of the closure of B_XX with Y is B_YY
  (h_inter : closure B_XX ∩ Set.range ι = ι '' B_YY) :
  -- Conclusion: The norm on X induces the norm on Y
  ∀ y : Y, ‖ι y‖ = ‖y‖ := by
  sorry







theorem theorem_552991_problem (p : ℕ) (a : ℤ)
  (hp : Nat.Prime p) (h : ¬ (p : ℤ) ∣ a) :
  a ^ (p - 1) ≡ 1 [ZMOD p] := by
  sorry

theorem theorem_552492_problem 
  (R : (ℝ → ℝ) → (ℝ → ℝ) → Prop)
  (hR : ∀ f g, R f g ↔ ∃ c : ℝ, ∀ x, x > c → f x = g x) :
  Equivalence R ∧ ∀ f, {g | R f g} = {g | ∃ c : ℝ, ∀ x, x > c → f x = g x} := by
  sorry



theorem theorem_552959_problem :
  ∃ (P : Type) (_ : Preorder P) (S : Set P) (u v : P),
    IsLUB S u ∧ IsLUB S v ∧ u ≠ v := by
  sorry









theorem theorem_552573_problem (a11 a12 a13 b1 a21 a22 a23 b2 alpha beta : ℝ) :
  Set.Nonempty ({x : Fin 3 → ℝ | a11 * x 0 + a12 * x 1 + a13 * x 2 ≥ b1} ∩
                {x : Fin 3 → ℝ | a21 * x 0 + a22 * x 1 + a23 * x 2 ≤ b2} ∩
                {x : Fin 3 → ℝ | ∀ i, alpha ≤ x i ∧ x i ≤ beta}) ↔
  ∃ x : Fin 3 → ℝ,
    Matrix.mulVec !![a11, a12, a13; -a21, -a22, -a23] x ≥ ![b1, -b2] ∧
    (∀ i, alpha ≤ x i ∧ x i ≤ beta) := by
  sorry







theorem theorem_553151_problem (p q : ℤ) (hq : q ≠ 0)
  (d : ℕ → ℤ)
  (h₀ : d 0 = 5 * p - 2 * q)
  (h_step : ∀ n, d (n + 1) = if d n < 0 then d n + 3 else if d n > 0 then d n - 1 else d n) :
  ∃ k, d k = 0 := by
  sorry





theorem theorem_553276_problem (n p q : ℕ)
  (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
  (hn : n = p^2 * q^2) :
  (p : ℝ)^2 - (p : ℝ) * (Real.sqrt n - (Nat.totient n : ℝ) / Real.sqrt n + 1) + Real.sqrt n = 0 ∧
  (q : ℝ)^2 - (q : ℝ) * (Real.sqrt n - (Nat.totient n : ℝ) / Real.sqrt n + 1) + Real.sqrt n = 0 := by
  sorry





theorem theorem_553406_problem
  (f : ℝ → ℝ → ℝ)
  (C : ℝ)
  (h_cont : ∀ t, Continuous (fun y ↦ f t y))
  (h_int : ∀ x δ s t, 0 < δ → x ∈ Set.Ioo 0 (1 - δ) → s ≤ t →
    abs (∫ y in Set.Ioc x (x + δ), f t y - f s y) ≤ C * δ * (t - s)) :
  ∀ x ∈ Set.Ioo 0 1, ∀ t s, abs (f t x - f s x) ≤ C * abs (t - s) := by
  sorry









theorem theorem_554409_problem (D : Type*) (P : D → Prop) 
  (h : ∃ x₀ : D, ¬ P x₀) : 
  ¬ (∀ x : D, P x) := by
  sorry

theorem theorem_553498_problem
  (F L : Type*) [Field F] [AddCommGroup L] [Module F L]
  (hL : ∃ S : Set L, Set.Countable S ∧ Submodule.span F S = ⊤)
  (L₀ : Submodule F L) [FiniteDimensional F L₀]
  (f₀ : L₀ →ₗ[F] F) :
  ∃ f : L →ₗ[F] F, ∀ x : L₀, f x = f₀ x := by
  sorry

theorem theorem_554233_problem (X : Type*) [TopologicalSpace X]
  (h_finite : (Set.range (connectedComponent : X → Set X)).Finite) :
  ∀ C ∈ Set.range (connectedComponent : X → Set X), IsClopen C := by
  sorry

theorem theorem_553728_problem (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
  Filter.Tendsto (fun x => ((a ^ x + b ^ x) / 2) ^ (1 / x)) (nhds 0) (nhds (Real.sqrt (a * b))) := by
  sorry

theorem theorem_553889_problem (R z a : ℝ)
  (h : a^2 = R^2 / 2 + z^2)
  (ha : a ≠ 0) :
  ∫ y in -(R / Real.sqrt 2)..(R / Real.sqrt 2), 1 / (a^2 + y^2) ^ ((3 : ℝ) / 2) =
  (R / Real.sqrt 2) / (a^2 * Real.sqrt (a^2 + (R / Real.sqrt 2) ^ 2)) -
  (-R / Real.sqrt 2) / (a^2 * Real.sqrt (a^2 + (-R / Real.sqrt 2) ^ 2)) := by
  sorry



theorem theorem_554488_problem (Statement : Type)
  (derivable : Statement → Statement → Prop)
  (entails : Statement → Statement → Prop)
  (h_sound : ∀ A B : Statement, derivable A B → entails A B)
  (h_complete : ∀ A B : Statement, entails A B → derivable A B)
  (A B : Statement) :
  derivable A B ↔ entails A B := by
  sorry

theorem theorem_553979_problem
  (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (A : Subalgebra ℝ (ContinuousMap X ℝ))
  (h_sep : ∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y) :
  Dense (A : Set (ContinuousMap X ℝ)) := by
  sorry





theorem theorem_554197_problem {D : Type*} (C : D → Prop)
  (h_incomplete : ∃ s1 s2 : D, C s1 ∧ C s2 ∧ s1 ≠ s2) :
  ¬ ∃! s, C s := by
  sorry





theorem theorem_553955_problem (n : ℕ) (h : n ≥ 1) :
  (Nat.fib n)^5 + (Nat.fib (n + 1))^5 =
  (Nat.fib (n + 2)) * (((Nat.fib n) * (Nat.fib (n + 1)) + (Nat.fib (n - 1))^2)^2 +
  (Nat.fib (n - 1))^2 * (Nat.fib n) * (Nat.fib (n + 1))) := by
  sorry



theorem theorem_554875_problem (x : ℝ) (hx : x ≠ 0) :
  let h : ℝ → ℝ := fun x ↦ x + 1 / x
  let f : ℝ → ℝ := fun x ↦ x
  HasDerivAt (fun t ↦ Real.exp (h t) * f t) 
    (Real.exp (h x) * ((1 - 1 / x ^ 2) * f x + 1)) x := by
  sorry



theorem theorem_554435_problem
  {Ω Ω' : Type*}
  (f : Ω → ℝ) (T : Ω → Ω') (g : Ω' → ℝ)
  (n : ℕ)
  (A : Fin n → Set Ω)
  (A' : Fin n → Set Ω')
  (α : Fin n → ℝ)
  (h1 : ∀ i, ∀ x ∈ A i, f x = α i)
  (h2 : ∀ i, ∀ x ∈ A i, T x ∈ A' i)
  (h3 : ∀ i, ∀ x, T x ∈ A' i → g (T x) = α i)
  (h4 : ∀ x, x ∉ (⋃ i, A i) → f x = 0)
  (h5 : ∀ x, T x ∉ (⋃ i, A' i) → g (T x) = 0) :
  ∀ x, f x = g (T x) := by
  sorry

theorem theorem_554578_problem {α : Type*} (B B₁ B₂ : Set α)
  (h₁ : B₁ ⊆ B) (h₂ : B₂ ⊆ B)
  (h_ex : ∃ x ∈ B, x ∉ B₁ ∧ x ∉ B₂) :
  B₁ ∪ B₂ ≠ B := by
  sorry







theorem theorem_554884_problem (N : ℕ) (z : ℂ)
  (h : Complex.abs z = (N : ℝ) + 1 / 2) :
  Complex.abs (Complex.cot (Real.pi * z)) ≤ 1.24 := by
  sorry







