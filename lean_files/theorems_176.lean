import Mathlib
import Mathlib.Tactic





theorem theorem_967092_problem 
  (a b : ℝ) 
  (k : ℕ) 
  (u v : Fin k → ℝ) 
  (θ : ℝ)
  (h_theta : 0 < θ)
  (h_ab : a ≤ b)
  (h_a_le_u : ∀ i, a ≤ u i)
  (h_v_le_b : ∀ i, v i ≤ b)
  (h_u_le_v : ∀ i, u i ≤ v i)
  (h_v_le_u_next : ∀ (i j : Fin k), (i : ℕ) + 1 = j → v i ≤ u j) :
  ∃ P : List ℝ, 
    P.Sorted (· ≤ ·) ∧
    P.head? = some a ∧
    P.getLast? = some b ∧
    (∀ i, u i ∈ P) ∧
    (∀ i, v i ∈ P) ∧
    P.Chain' (fun x y ↦ y - x < θ) := by
  sorry

theorem theorem_967491_problem (f : ℝ → ℝ)
  (h : ∀ x, f x = (Real.tanh x - 1) / Real.exp (-2 * x)) :
  Filter.Tendsto f Filter.atTop (nhds (-2)) := by
  sorry

theorem theorem_967402_problem
  {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  (f : X → Y) (D : Set X) (a : X) (L : Y)
  (ha : ClusterPt a (nhdsWithin a (D \ {a}))) :
  (∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, 0 < dist x a ∧ dist x a < δ → dist (f x) L < ε) ↔
  (∀ xn : ℕ → X, (∀ n, xn n ∈ D) → (∀ n, xn n ≠ a) →
    Filter.Tendsto xn Filter.atTop (nhds a) →
    Filter.Tendsto (f ∘ xn) Filter.atTop (nhds L)) := by
  sorry

theorem theorem_967581_problem
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (h_inf : ¬ FiniteDimensional ℂ E)
  (T : E →L[ℂ] E)
  (h_quasi : spectrum ℂ T = {0})
  (h_poly : ∃ p : Polynomial ℂ, p ≠ 0 ∧ Polynomial.aeval T p = 0) :
  ∃ n : ℕ, T ^ n = 0 := by
  sorry





theorem theorem_967097_problem (r u v : ℝ)
  (hr : r > 0)
  (x : ℝ) (hx : x = u - u^3 / 3 + u * v^2)
  (y : ℝ) (hy : y = v - v^3 / 3 + v * u^2)
  (z : ℝ) (hz : z = Real.sqrt (r^2 - (x^2 + y^2)))
  (h_domain : r^2 - (x^2 + y^2) ≥ 0) :
  x^2 + y^2 + z^2 = r^2 := by
  sorry

theorem theorem_967975_problem : Real.exp Real.pi > Real.pi ^ (Real.exp 1) := by
  sorry





theorem theorem_967618_problem (n m : ℤ) 
  (x y z w : ℤ)
  (hx : x = 3 * n^2 + 5 * n * m - 5 * m^2)
  (hy : y = 4 * n^2 - 4 * n * m + 6 * m^2)
  (hz : z = 5 * n^2 - 5 * n * m - 3 * m^2)
  (hw : w = 6 * n^2 - 4 * n * m + 4 * m^2) :
  x^3 + y^3 + z^3 = w^3 := by
  sorry

theorem theorem_967685_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (f : E → E)
  (h_lip : ∃ K, LipschitzWith K f)
  (phi1 phi2 : ℝ → E)
  (h_sol1 : ∀ t, HasDerivAt phi1 (f (phi1 t)) t)
  (h_sol2 : ∀ t, HasDerivAt phi2 (f (phi2 t)) t)
  (p : E)
  (h_regions : Set.range phi1 ∩ Set.range phi2 = {p})
  (h_distinct : phi1 ≠ phi2) :
  ¬ ∃ t, phi1 t = p ∧ phi2 t = p := by
  sorry

theorem theorem_967900_problem (ω ω' : ℂ) (hω : ω ≠ 0) (hω' : ω' ≠ 0) (h_indep : (ω / ω').im ≠ 0)
  (Λ : Set ℂ) (hΛ : Λ = {z | ∃ m n : ℤ, z = m * ω + n * ω'})
  (g₂ : ℂ) (hg₂ : g₂ = 60 * ∑' (p : ℤ × ℤ), if p = 0 then 0 else 1 / (p.1 * ω + p.2 * ω') ^ 4)
  (g₃ : ℂ) (hg₃ : g₃ = 140 * ∑' (p : ℤ × ℤ), if p = 0 then 0 else 1 / (p.1 * ω + p.2 * ω') ^ 6)
  (wp : ℂ → ℂ)
  (hwp : ∀ z, wp z = 1 / z ^ 2 + ∑' (w : Λ), if w.1 = 0 then 0 else (1 / (z - w.1) ^ 2 - 1 / w.1 ^ 2))
  (z : ℂ) (hz : z ∉ Λ) :
  (deriv wp z) ^ 2 = 4 * (wp z) ^ 3 - g₂ * (wp z) - g₃ := by
  sorry





theorem theorem_967845_problem
  (k : Type*) [Field k] [IsAlgClosed k]
  (X : Type*) -- Represents the smooth projective curve
  (O_X : Type*) -- Represents the structure sheaf
  (dim_H : ℕ → ℕ) -- Represents dim H^i(X, O_X)
  (p_a : ℤ) -- Arithmetic genus
  -- Condition: X is a curve, so higher cohomology vanishes (i >= 2)
  (h_vanish : ∀ i, i ≥ 2 → dim_H i = 0)
  -- Condition: Standard definition of arithmetic genus p_a = 1 - χ(O_X)
  -- We sum up to some N ≥ 2 to capture the non-zero terms
  (N : ℕ) (hN : N ≥ 2)
  (h_pa_def : p_a = 1 - ∑ i in Finset.range (N + 1), (-1 : ℤ)^i * (dim_H i : ℤ)) :
  p_a = 1 - (dim_H 0 : ℤ) + (dim_H 1 : ℤ) := by
  sorry

theorem theorem_968271_problem (x : ℝ) (N : ℕ)
  (hN_even : Even N) (hN_pos : 0 < N)
  (hx : ∀ m : ℤ, x ≠ 2 * Real.pi * m) :
  ∑ k in Finset.Icc (-(N : ℤ) / 2) ((N : ℤ) / 2), Complex.exp (Complex.I * k * x) =
  Complex.exp (-Complex.I * N * x / 2) *
  ((1 - Complex.exp (Complex.I * (N + 1) * x)) / (1 - Complex.exp (Complex.I * x))) := by
  sorry

theorem theorem_968439_problem (n : ℕ) (hn : n > 0)
  -- We treat the Metric as an abstract type or matrix field
  (Metric : Type)
  -- The Laplacian operator depends on the Metric and acts on smooth functions
  (Laplacian : Metric → ((Fin n → ℝ) → ℝ) → ((Fin n → ℝ) → ℝ))
  -- There exists a distinguished "Euclidean" metric Laplacian (operator only)
  (EuclideanLaplacian : ((Fin n → ℝ) → ℝ) → ((Fin n → ℝ) → ℝ)) :
  -- The theorem asserts the existence of a counter-example configuration
  ∃ (g : Metric) (u v : (Fin n → ℝ) → ℝ),
    let f := EuclideanLaplacian v
    (Laplacian g u = 0) ∧ 
    (Laplacian g (fun x => u x + v x) ≠ f) := by
  sorry











theorem theorem_968948_problem
  (X Y : Set (ℝ × ℝ))
  (hX : X = {p : ℝ × ℝ | p.2 > 0})
  (hY : Y = {p : ℝ × ℝ | -1 < p.2 ∧ p.2 < 1}) :
  ¬ ∃ f : (closure X) ≃ₜ (closure Y),
    f '' (Subtype.val ⁻¹' (frontier X)) = (Subtype.val ⁻¹' (frontier Y)) := by
  sorry















theorem theorem_969152_problem (X₁ X₂ : Set ℝ)
  (h1 : IsConnected X₁) (h2 : IsConnected X₂)
  (h3 : (X₁ ∩ X₂).Nonempty)
  (h4 : BddAbove X₁) (h5 : BddAbove X₂) :
  sSup (X₁ ∩ X₂) = min (sSup X₁) (sSup X₂) := by
  sorry

theorem theorem_969417_problem (a v w : ℝ)
  (ha : 0 < a) (hv : 0 < v) (hw : 0 < w) :
  ∫ t : ℝ, Complex.exp (Complex.I * t * w) * ((a : ℂ) + Complex.I * t) ^ (-(v : ℂ)) =
  ((2 * Real.pi) / Real.Gamma v * w ^ (v - 1) * Real.exp (-w * a) : ℝ) := by
  sorry













theorem theorem_969906_problem (x y : ℝ) (hx : x ≠ 0) :
  Set.Finite {n : ℤ | y = (n : ℝ) * x} := by
  sorry





theorem theorem_971442_problem
  -- Types representing the domain of Propositional Logic
  (Proposition Assignment : Type)
  -- The valuation function v(P)
  (v : Assignment → Proposition → Prop)
  -- Abstract propositions A and B
  (A B : Proposition)
  -- The biconditional connective (A ↔ B)
  (bicond : Proposition → Proposition → Proposition)
  -- Predicates for "logically equivalent" and "is a tautology"
  (logically_equivalent : Proposition → Proposition → Prop)
  (is_tautology : Proposition → Prop)
  -- Condition: Definition of logical equivalence (A is equivalent to B iff v(A) = v(B) for all v)
  (h_equiv_def : logically_equivalent A B ↔ ∀ assign, (v assign A ↔ v assign B))
  -- Condition: Definition of tautology for (A ↔ B) (i.e., v(A ↔ B) = T for all v)
  (h_taut_def : is_tautology (bicond A B) ↔ ∀ assign, v assign (bicond A B))
  -- Condition: Standard semantics of the biconditional (v(A ↔ B) = T iff v(A) = v(B))
  (h_bicond_sem : ∀ assign, v assign (bicond A B) ↔ (v assign A ↔ v assign B)) :
  -- Question: Prove A is logically equivalent to B iff (A ↔ B) is a tautology
  logically_equivalent A B ↔ is_tautology (bicond A B) := by
  sorry









theorem theorem_969623_problem
  (y1 y2 : ℝ → ℝ) (hy1 : ContDiff ℝ ⊤ y1) (hy2 : ContDiff ℝ ⊤ y2) (x : ℝ) :
  let M (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![
    y1 t, y2 t, iteratedDeriv 1 y1 t, iteratedDeriv 1 y2 t;
    iteratedDeriv 1 y1 t, iteratedDeriv 1 y2 t, iteratedDeriv 2 y1 t, iteratedDeriv 2 y2 t;
    iteratedDeriv 2 y1 t, iteratedDeriv 2 y2 t, iteratedDeriv 3 y1 t, iteratedDeriv 3 y2 t;
    iteratedDeriv 3 y1 t, iteratedDeriv 3 y2 t, iteratedDeriv 4 y1 t, iteratedDeriv 4 y2 t]
  let N1 : Matrix (Fin 3) (Fin 3) ℝ := !![
    iteratedDeriv 1 y2 x, iteratedDeriv 2 y1 x, iteratedDeriv 2 y2 x;
    iteratedDeriv 2 y2 x, iteratedDeriv 3 y1 x, iteratedDeriv 3 y2 x;
    iteratedDeriv 3 y2 x, iteratedDeriv 4 y1 x, iteratedDeriv 4 y2 x]
  let N2 : Matrix (Fin 3) (Fin 3) ℝ := !![
    y2 x, iteratedDeriv 2 y1 x, iteratedDeriv 2 y2 x;
    iteratedDeriv 1 y2 x, iteratedDeriv 3 y1 x, iteratedDeriv 3 y2 x;
    iteratedDeriv 3 y2 x, iteratedDeriv 4 y1 x, iteratedDeriv 4 y2 x]
  let N3 : Matrix (Fin 3) (Fin 3) ℝ := !![
    y2 x, iteratedDeriv 1 y2 x, iteratedDeriv 2 y1 x;
    iteratedDeriv 1 y2 x, iteratedDeriv 2 y2 x, iteratedDeriv 3 y1 x;
    iteratedDeriv 3 y2 x, iteratedDeriv 4 y2 x, iteratedDeriv 4 y1 x]
  iteratedDeriv 2 (fun t => (M t).det) x = N1.det - N2.det - N3.det := by
  sorry



theorem theorem_971170_problem (q s : ℝ) (pmf : ℕ → ℝ)
  (hq : 0 < q ∧ q < 1)
  (hs : |s| < 1 / q)
  (h_pmf : ∀ k : ℕ, pmf k = if k = 0 then 0 else -(q ^ k) / ((k : ℝ) * Real.log (1 - q))) :
  ∑' k : ℕ, pmf k * s ^ k = Real.log (1 - q * s) / Real.log (1 - q) := by
  sorry

theorem theorem_970898_problem
  (V : Type*) [Fintype V] [DecidableEq V]
  (G B : Finset V)
  (h_disjoint : Disjoint G B)
  (h_union : G ∪ B = Finset.univ)
  (a : Fin 2 → V → ℕ)
  (h_a_bin : ∀ k n, a k n ≤ 1) :
  let constraints (x : V → ℕ) := (∀ n, x n ≤ 1) ∧ (∀ k, ∑ n, a k n * (1 - x n) ≤ 4);
  let b_rem (x : V → ℕ) := ∑ n in B, (1 - x n);
  let g_rem (x : V → ℕ) := ∑ n in G, (1 - x n);
  ∃ y_star : ℕ,
    IsGreatest {y | ∃ x, constraints x ∧ y ≤ b_rem x ∧ y ≤ g_rem x} y_star ∧
    IsGreatest {z | ∃ x, constraints x ∧ z = min (b_rem x) (g_rem x)} y_star := by
  sorry



theorem theorem_971300_problem
  (X : Type*) [Fintype X] [DecidableEq X]
  (φ : X → ℝ)
  (m s : ℝ)
  (hms : m > s)
  (h_bound : ∀ x, s ≤ φ x ∧ φ x ≤ m) :
  ∃ B : ℝ, ∀ (δ : ℝ) (A : Finset X),
    δ > 0 → (∑ a in A, φ a > 1 - δ) → (m - s) * (A.card : ℝ) ≤ B := by
  sorry

theorem theorem_971345_problem (a b : ℝ) (f : ℝ → ℝ)
  (hf : ContinuousOn f (Set.Icc a b))
  (ε : ℝ) (hε : ε > 0) :
  ∃ N : ℕ, ∃ a_coeff : ℕ → ℝ, ∃ b_coeff : ℕ → ℝ,
    ∀ x ∈ Set.Icc a b,
      abs (f x - (a_coeff 0 + ∑ n in Finset.Icc 1 N, (a_coeff n * Real.cos ((n : ℝ) * x) + b_coeff n * Real.sin ((n : ℝ) * x)))) < ε := by
  sorry



theorem theorem_971942_problem
  {E : Type*} [NormedAddCommGroup E]
  (f : E)
  (n : ℕ)
  (a c : Fin n → ℝ) :
  ‖f‖^2 - 2 * (∑ k, a k * c k) + (∑ k, (a k)^2) =
  ‖f‖^2 - (∑ k, (c k)^2) + (∑ k, (a k - c k)^2) := by
  sorry

theorem theorem_971727_problem (R k d θ : ℝ)
  (hR : 0 < R)
  (hk : 0 ≤ k)
  (hd : R + k / 2 < d)
  (hθ_range : 0 < θ ∧ θ < Real.pi / 2)
  (h_tangency : Real.cos θ = (R + k / 2) / d) :
  θ = Real.arctan (Real.sqrt (d ^ 2 - (R + k / 2) ^ 2) / (R + k / 2)) := by
  sorry

theorem theorem_972004_problem
  (a b m l x : ℝ)
  (h1 : a^2 + b^2 > 0)
  (α : ℝ)
  (hα : α = Real.arctan (b / a))
  (hx1 : Real.cos (x - α) ≠ 0)
  (hx2 : 1 / Real.cos (x - α) + Real.tan (x - α) ≠ 0) :
  deriv (fun t =>
    ((l * Real.cos α - m * Real.sin α) / (a^2 + b^2)) * (1 / Real.cos (t - α)) +
    ((l * Real.sin α + m * Real.cos α) / (a^2 + b^2)) * Real.log (abs (1 / Real.cos (t - α) + Real.tan (t - α)))
  ) x = (l * Real.sin x + m * Real.cos x) / ((a^2 + b^2) * (Real.cos (x - α)) ^ 2) := by
  sorry



theorem theorem_972185_problem (f : ℂ → ℂ) (s : Set ℂ)
  (h_open : IsOpen s)
  (h_ana : AnalyticOn ℂ f s) :
  ∀ z ∈ s, iteratedFDeriv ℝ 2 f z ![1, 1] + iteratedFDeriv ℝ 2 f z ![I, I] = 0 := by
  sorry



theorem theorem_972451_problem :
  FiniteDimensional.finrank ℝ (Matrix (Fin 3) (Fin 3) ℝ) - 1 = 8 := by
  sorry













theorem theorem_972776_problem (x : ℝ) :
  Filter.Tendsto (fun n : ℕ => (1 + x / Real.sqrt n) ^ n * Real.exp (-x * Real.sqrt n))
    Filter.atTop (nhds (Real.exp (-x ^ 2 / 2))) := by
  sorry





theorem theorem_972263_problem
  {K : Type*} [Field K]
  {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {n m : ℕ}
  (bV : Basis (Fin n) K V) (bW : Basis (Fin m) K W)
  (bV' : Basis (Fin n) K V) (bW' : Basis (Fin m) K W)
  (T : V →ₗ[K] W)
  (P : Matrix (Fin n) (Fin n) K) (hP : P = bV.toMatrix bV')
  (Q : Matrix (Fin m) (Fin m) K) (hQ : Q = bW.toMatrix bW') :
  LinearMap.toMatrix bV' bW' T = Q * (LinearMap.toMatrix bV bW T) * P⁻¹ := by
  sorry





theorem theorem_972791_problem (n : ℕ) :
  ∑ k in Finset.range (n + 1), (1 / ((k : ℝ) + 1)) * (Nat.choose n k : ℝ) =
  ((2 : ℝ) ^ (n + 1) - 1) / ((n : ℝ) + 1) := by
  sorry











theorem theorem_972831_problem (x y z : Polynomial ℝ) :
  ∃ F : MvPolynomial (Fin 3) ℝ, F ≠ 0 ∧
  ∀ t : ℝ, MvPolynomial.eval ![x.eval t, y.eval t, z.eval t] F = 0 := by
  sorry

theorem theorem_973601_problem (R rho theta : ℝ)
  (hR : 0 < R) (hrho : 0 < rho) (htheta : 0 < theta) :
  (∫ r in (0)..R, r * (rho * r * theta)) / (∫ r in (0)..R, rho * r * theta) = (2 * R) / 3 := by
  sorry

theorem theorem_973636_problem {G : Type*} [Group G] (a : G) (k d : ℤ)
  (h : a ^ k ∈ Subgroup.zpowers (a ^ d)) :
  Subgroup.zpowers (a ^ k) ≤ Subgroup.zpowers (a ^ d) := by
  sorry



theorem theorem_973847_problem
  (R : Type*) [CommRing R] (I : Ideal R)
  (h : ∀ x y : R, x * y ∈ I → x ∈ I ∨ ∃ n : ℕ, n ≥ 1 ∧ y ^ n ∈ I)
  (x y : R) (h_yx : y * x ∈ I) :
  y ∈ I ∨ ∃ m : ℕ, m ≥ 1 ∧ x ^ m ∈ I := by
  sorry







theorem theorem_974062_problem
  (Data Theta Alpha : Type)
  (p_X_given_theta : Data → Theta → ℝ)
  (p_theta_given_alpha : Theta → Alpha → ℝ)
  (p_X_theta_given_alpha : Data → Theta → Alpha → ℝ)
  (p_X_given_theta_alpha : Data → Theta → Alpha → ℝ)
  -- Condition: The joint distribution given α factorizes into Likelihood(X|θ) * Prior(θ|α).
  -- This encodes the condition that α is not included in the likelihood.
  (h_factorization : ∀ x t a, p_X_theta_given_alpha x t a = p_X_given_theta x t * p_theta_given_alpha t a)
  -- Condition: Definition of conditional probability p(X | θ, α).
  -- Formulated as a product to avoid division by zero: p(X | θ, α) * p(θ | α) = p(X, θ | α)
  (h_cond_def : ∀ x t a, p_X_given_theta_alpha x t a * p_theta_given_alpha t a = p_X_theta_given_alpha x t a)
  -- Condition: The prior density is non-zero (required for algebraic cancellation).
  (h_nonzero : ∀ t a, p_theta_given_alpha t a ≠ 0) :
  -- Goal: Prove p(X | θ, α) = p(X | θ)
  ∀ x t a, p_X_given_theta_alpha x t a = p_X_given_theta x t := by
  sorry



theorem theorem_974642_problem
  (x y : ℝ → ℝ)
  (F : ℝ → ℝ → ℝ)
  (hx_smooth : ContDiff ℝ ⊤ x)
  (hy_smooth : ContDiff ℝ ⊤ y)
  (hx_ne_zero : ∀ t, deriv x t ≠ 0)
  (hy_ne_zero : ∀ t, deriv y t ≠ 0)
  (h_ode : ∀ t, deriv y t / deriv x t = F (x t) (y t)) :
  ∃ φ : ℝ → ℝ, Differentiable ℝ φ ∧ (∀ t, y t = φ (x t)) ∧
  (∀ t, deriv φ (x t) = F (x t) (y t)) := by
  sorry

theorem theorem_973677_problem
  {n : ℕ} {K : Type*} [Field K]
  (A : Matrix (Fin n) (Fin n) K)
  (h : Matrix.trace A = 0) :
  ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P ∧ ∀ i, (P⁻¹ * A * P) i i = 0 := by
  sorry







theorem theorem_973931_problem (S : Prop)
  (Proofs : Type)
  (equiv : Proofs → Proofs → Prop)
  (hequiv : Equivalence equiv) :
  Finite (Quotient (Setoid.mk equiv hequiv)) := by
  sorry

theorem theorem_974183_problem
  (A : Set (lp (fun _ : ℕ => ℝ) 2))
  (hA : A = {x | ‖x‖ ≤ 1}) :
  IsClosed A := by
  sorry



