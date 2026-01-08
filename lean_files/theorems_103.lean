import Mathlib
import Mathlib.Tactic





theorem theorem_555136_problem (c : ℝ) (hc : c > 0) :
  ∃! x : ℝ, Real.exp x = c := by
  sorry

theorem theorem_555207_problem (D P Q : ℤ)
  (hD_pos : 0 < D)
  (hD_nonsq : ¬ ∃ n : ℤ, n^2 = D)
  (hQ_nz : Q ≠ 0)
  (h_div : Q ∣ (D - P^2))
  (α : ℝ)
  (h_α : α = (P + Real.sqrt (D : ℝ)) / (Q : ℝ))
  (α1 : ℝ)
  (h_α1 : α1 = 1 / (α - (Int.floor α : ℝ))) :
  ∃ P1 Q1 : ℤ, Q1 ≠ 0 ∧ α1 = (P1 + Real.sqrt (D : ℝ)) / (Q1 : ℝ) := by
  sorry

theorem theorem_555349_problem {A B : Type*} [CommRing A] [CommRing B]
  (φ : A →+* B) (a : Ideal A) :
  (PrimeSpectrum.comap φ) ⁻¹' (PrimeSpectrum.zeroLocus a) =
  PrimeSpectrum.zeroLocus (Ideal.map φ a) := by
  sorry

theorem theorem_555378_problem (a : ℕ → ℝ) (q : ℝ)
  (hq : q > 0)
  (ha : ∀ n, 1 ≤ n → a n ≠ 0)
  (h : ∀ n, 1 ≤ n → |a (n + 1) / a n| < q) :
  ∀ n, 1 ≤ n → |a (n + 1)| ≤ |a 1| * q ^ n := by
  sorry



theorem theorem_553205_problem (k i : ℤ) (h : k + i > 0) :
  Filter.Tendsto (fun n : ℕ => (n.factorial : ℝ) / (((n - (k + i).toNat).factorial : ℝ) * (n : ℝ) ^ (k + i))) Filter.atTop (nhds 1) := by
  sorry



theorem theorem_555718_problem (x y : ℝ) : 
  x^4 + y^4 + 2 ≥ 4 * x * y := by
  sorry





theorem theorem_555972_problem (E : ℤ → Prop) (i0 : ℤ) :
  (fun i => E i) i0 ↔ E i0 := by
  sorry











theorem theorem_556453_problem
  (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (A : Ideal R) (hA : A < ⊤) :
  ∃ γ : K, γ ∉ Set.range (algebraMap R K) ∧
    ∀ a ∈ A, γ * (algebraMap R K a) ∈ Set.range (algebraMap R K) := by
  sorry

theorem theorem_556645_problem (F : ℝ → ℝ) (s : ℝ) (c : ℝ)
  (h : DifferentiableAt ℝ F s) :
  deriv (fun x => x * F x - c) s = F s + s * deriv F s := by
  sorry







theorem theorem_556712_problem (n k : ℕ) (hk : k < n) :
  let vertices : Finset (Fin n × Bool) := Finset.univ
  let is_orthoplex_face (s : Finset (Fin n × Bool)) : Prop :=
    s.card = k + 1 ∧ ∀ i : Fin n, ¬ ((i, true) ∈ s ∧ (i, false) ∈ s)
  (vertices.powerset.filter is_orthoplex_face).card = 2^(k + 1) * Nat.choose n (k + 1) := by
  sorry





theorem theorem_557036_problem {X : Type*} [MetricSpace X] (a : ℕ → X) (x : X) :
  MapClusterPt x atTop a ↔ ∀ ε > 0, ∀ N : ℕ, ∃ n > N, dist (a n) x < ε := by
  sorry











theorem theorem_557716_problem (M α : ℝ)
  (h : ∀ β : ℝ, β ≥ α → M ≤ β) :
  M ≤ α := by
  sorry











theorem theorem_557895_problem (f : ℝ → ℝ) (x₀ y₀ : ℝ)
  (h_diff : ContDiff ℝ 1 f)
  (h_init : f x₀ = y₀) :
  ∀ x : ℝ, f x = y₀ + ∫ t in x₀..x, deriv f t := by
  sorry





theorem theorem_558453_problem (G : Type*) [CommGroup G] [Fintype G]
  (n : ℕ) (h_card : Fintype.card G = n)
  (h_sf : Squarefree n) :
  IsCyclic G := by
  sorry

theorem theorem_558276_problem (n : ℕ) {R : Type*} [CommRing R]
  (A : Matrix (Fin n) (Fin n) R) :
  Matrix.det ((Matrix.det A) • (1 : Matrix (Fin n) (Fin n) R)) = (Matrix.det A) ^ n := by
  sorry

theorem theorem_558075_problem :
  ∫ x in (0 : ℝ)..(2 * Real.pi), 1 / (2 + Real.cos x) = (2 * Real.pi) / Real.sqrt 3 := by
  sorry

theorem theorem_558483_problem
  (G H : Type*) [Group G] [Group H] [Fintype G] [Fintype H]
  (n : ℕ) (hn : n > 0)
  (h_count : (Finset.filter (fun g : G => orderOf g = n) Finset.univ).card ≠
             (Finset.filter (fun h : H => orderOf h = n) Finset.univ).card) :
  ¬ Nonempty (G ≃* H) := by
  sorry

theorem theorem_558393_problem (A : Type*) [Countable A] (h : ∃ x y : A, x ≠ y) :
  ¬ Countable (ℕ → A) := by
  sorry



theorem theorem_558480_problem (ϕ : ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ →+* ℚ) : False := by
  sorry









theorem theorem_558998_problem
  (a : ℕ → ℂ) (b : ℕ → ℝ)
  (h1 : ∃ M, ∀ n, ‖∑ i in Finset.range n, a i‖ ≤ M)
  (h2 : Antitone b)
  (h3 : Filter.Tendsto b Filter.atTop (nhds 0)) :
  Summable (fun n => a n * (b n : ℂ)) := by
  sorry



theorem theorem_558859_problem (a b : ℝ) (x : ℕ → ℝ)
  (h : ∀ n, x n ∈ Set.Icc a b) :
  ∃ L ∈ Set.Icc a b, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (x ∘ φ) Filter.atTop (nhds L) := by
  sorry







theorem theorem_558638_problem (R : Type*) [Ring R] (G : Type*) [Group G] [DecidableEq G] (r : R) (g : G) :
  (MonoidAlgebra.single (1 : G) r) * (MonoidAlgebra.single g (1 : R)) = 
  (MonoidAlgebra.single g (1 : R)) * (MonoidAlgebra.single (1 : G) r) := by
  sorry

theorem theorem_558671_problem
  (u w v₀ v : EuclideanSpace ℝ (Fin 3))
  (u' w' : EuclideanSpace ℝ (Fin 3))
  (c_u c_w : ℝ)
  (h_u_def : u' = u - v₀)
  (h_w_def : w' = w - v₀)
  (h_orth : inner u' w' = (0 : ℝ))
  (h_u_nz : u' ≠ 0)
  (h_w_nz : w' ≠ 0)
  (h_decomp : v - v₀ = c_u • u' + c_w • w') :
  c_u = inner u' (v - v₀) / inner u' u' ∧
  c_w = inner w' (v - v₀) / inner w' w' := by
  sorry



theorem theorem_559401_problem (f : ℝ → ℝ)
  (h : ∀ x, |f x| ≤ |x|) :
  Filter.Tendsto f (nhds 0) (nhds 0) := by
  sorry



theorem theorem_559882_problem (x : ℝ) :
  Filter.Tendsto (fun (n : ℕ) => ((n : ℝ) - 1) / n * (1 - x / n) ^ ((n : ℝ) - 2)) Filter.atTop (nhds (Real.exp (-x))) := by
  sorry







theorem theorem_559646_problem (p : ℕ)
  (hp : Nat.Prime p)
  (h_odd : Odd p)
  (h_div : Odd ((p^2 - 1) / 8)) :
  p ≡ 3 [MOD 8] ∨ p ≡ 5 [MOD 8] := by
  sorry











theorem theorem_559709_problem 
  (Y : Type*) 
  (R_star : Type*) [LinearOrder R_star]
  (IsInternalFun : (Y → R_star) → Prop)
  (IsInternalSet : Set Y → Prop)
  (F : Set (Set Y))
  (g : Y → R_star)
  (hg : IsInternalFun g)
  (hF : ∀ s, s ∈ F ↔ IsInternalSet s)
  (a : R_star) :
  g ⁻¹' (Set.Iic a) ∈ F := by
  sorry







theorem theorem_560139_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (G : E → ℝ) (x : E) (n : E)
  (h_diff : DifferentiableAt ℝ G x)
  (hx : x ≠ 0)
  (hn : n = ‖x‖⁻¹ • x) :
  fderiv ℝ G x n = inner (gradient G x) n := by
  sorry









theorem theorem_560151_problem
  (f : ℝ → ℝ) (hf : Continuous f)
  (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
  (x : ℝ → ℝ)
  (hx : Differentiable ℝ x)
  (h_ode : ∀ t, deriv (fun t => x (β * t)) t = f (α * t) * Real.sin (β * t)) :
  ∀ z, deriv x z = (1 / β) * f ((α / β) * z) * Real.sin z := by
  sorry

theorem theorem_560407_problem (p1 p2 : ℕ)
  (hp1 : Nat.Prime p1) (hp2 : Nat.Prime p2)
  (hneq : p1 ≠ p2) :
  Ideal.span {(p1 : ℤ)} + Ideal.span {(p2 : ℤ)} = ⊤ := by
  sorry





theorem theorem_560208_problem
  {S : Type*}
  (sigma : ℕ → Equiv.Perm S)
  (tau : ℕ → Equiv.Perm S)
  (sigma_lim tau_lim : Equiv.Perm S)
  (h_sigma : ∀ x : S, ∃ N, ∀ n ≥ N, sigma n x = sigma_lim x)
  (h_tau : ∀ x : S, ∃ N, ∀ n ≥ N, tau n x = tau_lim x) :
  ∀ x : S, ∃ N, ∀ n ≥ N, sigma n (tau n x) = sigma_lim (tau_lim x) := by
  sorry







theorem theorem_560820_problem (f : ℝ → ℝ) (a b : ℝ)
  (h_le : a ≤ b)
  (h_cont : ContinuousOn f (Set.Icc a b)) :
  ∃ c ∈ Set.Icc a b, f c = sSup (f '' Set.Icc a b) := by
  sorry



theorem theorem_560789_problem (a b c : ℤ) (n : ℕ)
  (hn : n > 2)
  (h_eq : a^n + b^n = c^n) :
  a = 0 ∨ b = 0 ∨ c = 0 := by
  sorry



theorem theorem_560739_problem :
  AddSubgroup.closure {x : ℝ | 0 < x} = ⊤ := by
  sorry



theorem theorem_560390_problem :
  ∃ f g : ℝ → ℝ, sInf (Set.range (f + g)) ≠ sInf (Set.range f) + sInf (Set.range g) := by
  sorry



theorem theorem_560637_problem 
  (π : ℝ → ℝ) -- The prior PDF of A
  (P_cond : ℝ → ℝ) -- The conditional probability P(X ∉ I | A)
  (Posterior : ℝ → ℝ) -- The posterior PDF
  (P_marginal : ℝ) -- The marginal probability of the event X ∉ I
  -- Condition: The marginal probability is the integral of likelihood * prior
  (h_marginal_def : P_marginal = ∫ x, P_cond x * π x)
  -- Condition: The event is possible (denominator is not zero)
  (h_nonzero : P_marginal ≠ 0)
  -- Condition: Bayes' theorem relates the posterior to the likelihood, prior, and marginal
  (h_bayes : ∀ a, Posterior a = (P_cond a * π a) / P_marginal) :
  -- Conclusion: The explicit formula for the posterior
  ∀ a, Posterior a = (P_cond a * π a) / (∫ x, P_cond x * π x) := by
  sorry



