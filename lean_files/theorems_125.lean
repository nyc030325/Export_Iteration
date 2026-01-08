import Mathlib
import Mathlib.Tactic





theorem theorem_678927_problem {X : Type*} [TopologicalSpace X] (A B : Set X) :
  closure A \ closure B = closure (A \ B) \ closure B := by
  sorry

theorem theorem_678882_problem
  (a b : ℝ) (hab : a ≤ b)
  (f : ℝ → ℝ) (hf : IntervalIntegrable f volume a b)
  (c : ℝ) (hc : c ∈ ({-1, 1} : Set ℝ)) :
  ∫ x in a..b, c * f x ≤ ∫ x in a..b, |f x| := by
  sorry

theorem theorem_678932_problem
  (a b c d : ℝ)
  (u1 u2 u3 : ℝ)
  (ha : a > 0)
  (h_roots : a * u1^3 + b * u1^2 + c * u1 + d = 0 ∧
             a * u2^3 + b * u2^2 + c * u2 + d = 0 ∧
             a * u3^3 + b * u3^2 + c * u3 + d = 0)
  (h_order : u1 > u2 ∧ u2 > u3)
  (h_pos : u2 > 0) :
  u2 < (-b + Real.sqrt (b^2 - 3 * a * c)) / (3 * a) := by
  sorry





theorem theorem_678845_problem (c : ℝ) (p : ℕ → ℝ)
  (h_def : ∀ n, n ≥ 2 → p n = c / ((n : ℝ) * (Real.log n) ^ 2))
  (h_sum : ∑' n, (if n ≥ 2 then p n else 0) = 1) :
  ¬ Summable (fun n ↦ if n ≥ 2 then -p n * Real.logb 2 (p n) else 0) := by
  sorry

theorem theorem_679272_problem (R : Type*) [CommRing R] (c : R) :
  let E_A : R → R → Prop := fun u v ↦ v = u * c
  let E_B : R → R → Prop := fun u v ↦ v = c * (u - c + 1)
  ∃ f : R ≃ R, ∀ u v, E_A u v ↔ E_B (f u) (f v) := by
  sorry







theorem theorem_679235_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  (h_dim : ¬ FiniteDimensional 𝕜 X) :
  ∃ x : ℕ → X, (∀ n, ‖x n‖ = 1) ∧ (∀ n m, n ≠ m → ‖x n - x m‖ ≥ 1) := by
  sorry

theorem theorem_679818_problem
  (y : ℝ → ℝ)
  (hy : Differentiable ℝ y)
  (h : ∀ x, y x * Real.exp (x * y x) + (x * Real.exp (x * y x) + 2 * y x) * deriv y x = 0) :
  ∃ C : ℝ, ∀ x, Real.exp (x * y x) + (y x) ^ 2 = C := by
  sorry



theorem theorem_679726_problem (y : ℝ → ℝ) (h_diff : Differentiable ℝ y)
  (h_ode : ∀ x : ℝ, deriv y x = x ^ 2 * (1 - 2 * y x)) :
  ∃ C : ℝ, ∀ x : ℝ, y x = (1 / 2 : ℝ) * (1 - C * Real.exp (-2 * x ^ 3 / 3)) := by
  sorry



theorem theorem_679696_problem {α : Type*} (P Q : α → Prop)
  (h : (∃ x, P x) ∨ (∃ x, Q x)) :
  ∃ x, P x ∨ Q x := by
  sorry



theorem theorem_680108_problem
  {S1 S2 S3 S4 : Type*} [Fintype S1]
  (p_joint : S1 → S2 → S3 → S4 → ℝ)
  (p1 : S1 → ℝ)
  (p2_1 : S2 → S1 → ℝ)
  (p3_2 : S3 → S2 → ℝ)
  (p4_3 : S4 → S3 → ℝ)
  (h_factor : ∀ (x1 : S1) (x2 : S2) (x3 : S3) (x4 : S4),
    p_joint x1 x2 x3 x4 = p1 x1 * p2_1 x2 x1 * p3_2 x3 x2 * p4_3 x4 x3) :
  ∀ (x2 : S2) (x3 : S3) (x4 : S4),
    ∑ x1 : S1, p_joint x1 x2 x3 x4 =
    ∑ x1 : S1, p1 x1 * p2_1 x2 x1 * p3_2 x3 x2 * p4_3 x4 x3 := by
  sorry











theorem theorem_680416_problem (x : ℕ → ℝ)
  (h1 : ∀ n, x n > 0)
  (h2 : Filter.Tendsto x Filter.atTop (nhds 0)) :
  Filter.Tendsto (fun n => 1 / x n) Filter.atTop Filter.atTop := by
  sorry

















theorem theorem_681066_problem (f : ℝ → ℝ)
  (h : ∀ x, f x = (4 * x) / (4 * x^8 + 1)) :
  MeasureTheory.IntegrableOn f (Set.Ici 0) := by
  sorry

theorem theorem_680921_problem
  (R : Type*) [Ring R] [Nontrivial R]
  (I : Ideal R) (hI : I ≠ ⊤) :
  ∃ M : Ideal R, Ideal.IsMaximal M ∧ I ≤ M := by
  sorry

theorem theorem_680985_problem (a : ℕ → ℝ) 
  (h_bounded : ∃ M, ∀ n, |a n| ≤ M) :
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ l, Filter.Tendsto (a ∘ φ) Filter.atTop (nhds l) := by
  sorry

theorem theorem_678910_problem
  (n k : ℕ)
  (p : Fin k → ℕ)
  (h_sum : ∑ i, p i = n)
  (h_desc : ∀ i j : Fin k, i ≤ j → p j ≤ p i) :
  (∃ A : Matrix (Fin k) (Fin k) ℕ,
    A.IsSymm ∧
    (∀ i j, A i j ≤ 1) ∧
    (∀ i, ∑ j, A i j = p i)) ↔
  (∀ j : Fin k,
    ∑ i in Finset.Iic j, p i ≤
    ∑ y in Finset.Iic j, (Finset.filter (fun x => p x ≥ (y : ℕ) + 1) Finset.univ).card) := by
  sorry







theorem theorem_680879_problem
  (a : ℕ → ℕ → ℝ → ℝ)
  (h_div : ∀ n x, ¬ Summable (fun k => a n k x)) :
  ¬ ∃ h : ℕ → ℝ → ℝ, ∀ n, TendstoUniformly (fun N x => ∑ k in Finset.range N, a n k x) (h n) atTop := by
  sorry











theorem theorem_681642_problem (p : ℕ) [Fact p.Prime]
  (log_p : ℚ_[p] → ℚ_[p]) (C : ℚ_[p])
  (h_series : ∀ x : ℚ_[p], ‖x - 1‖ < 1 → 
    log_p x = ∑' n : ℕ, if n = 0 then 0 else ((-1 : ℚ_[p]) ^ (n + 1) * (x - 1) ^ n) / (n : ℚ_[p]))
  (h_ext : ∀ α : ℚ_[p], α ≠ 0 → 
    log_p α = (Padic.valuation α : ℚ_[p]) * C + log_p (α * (p : ℚ_[p]) ^ (-Padic.valuation α))) :
  ContinuousOn log_p {x | x ≠ 0} := by
  sorry

theorem theorem_681927_problem (a b d e : ℤ) (x y : ℝ)
  (hb : b > 0) (he : e > 0)
  (hx : x = (a : ℝ) / (b : ℝ) * Real.pi)
  (hy : y = (d : ℝ) / (e : ℝ) * Real.pi)
  (hxy_bound : 0 < x ∧ x < 3 ∧ 0 < y ∧ y < 3) :
  ((∃ m n : ℤ, n ≠ 0 ∧ x = (m : ℝ) / (n : ℝ) * Real.pi) ∧
   (∃ k l : ℤ, l ≠ 0 ∧ y = (k : ℝ) / (l : ℝ) * Real.pi)) ↔
  ((3 * y^2 + 1)^2 * (2 * Real.cosh (26 * Real.pi * y / 15) * Real.cosh (x * y) - Real.cosh ((2 * Real.pi - x) * y))) /
  (9 * (y^2 - 1)^2 * Real.cosh ((x + 2 * Real.pi) * y) + 8 * (3 * y^2 - 1) * Real.cosh (x * y)) = 1 := by
  sorry

theorem theorem_681851_problem
  (f : ℝ → ℝ) (I : Set ℝ) (x₀ x₁ x : ℝ)
  (hI : Convex ℝ I)
  (hf : ContDiffOn ℝ 3 f I)
  (hx0 : x₀ ∈ I) (hx1 : x₁ ∈ I) (hx : x ∈ I)
  (h_distinct : x₀ ≠ x₁)
  (hx_between : x ∈ Set.uIcc x₀ x₁) :
  ∃ ξ ∈ Set.Ioo (min x₀ x₁) (max x₀ x₁),
    f x = -((x - x₁) * (x - 2 * x₀ + x₁) / (x₁ - x₀) ^ 2) * f x₀ +
          ((x - x₀) * (x - x₁) / (x₀ - x₁)) * deriv f x₀ +
          ((x - x₀) ^ 2 / (x₁ - x₀) ^ 2) * f x₁ +
          (1 / 6) * (x - x₀) ^ 2 * (x - x₁) * iteratedDeriv 3 f ξ := by
  sorry

theorem theorem_681029_problem 
  (y a b c : ℝ → ℝ)
  (hy : ContDiff ℝ 2 y)
  (ha : Differentiable ℝ a)
  (hb : Differentiable ℝ b)
  (hc : Differentiable ℝ c)
  (h_ode : ∀ x : ℝ, x ≠ 0 → 
    a x * x^4 * (deriv (deriv y) x) + (2 * a x * x^3 - b x * x^2) * (deriv y x) + c x * y x = 0) :
  let z := fun (ζ : ℝ) => y (1 / ζ)
  ∀ ζ : ℝ, ζ ≠ 0 → 
    a (1 / ζ) * ζ^4 * (deriv (deriv z) ζ) + (2 * a (1 / ζ) * ζ^3 - b (1 / ζ) * ζ^2) * (deriv z ζ) + c (1 / ζ) * z ζ = 0 := by
  sorry





theorem theorem_682028_problem (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
  let f : ℝ → ℝ := fun x ↦ 1 / (a^2 * Real.cos x ^ 2 + b^2 * Real.sin x ^ 2)
  let F : ℝ → ℝ := fun x ↦ (1 / (a * b)) * Real.arctan ((b / a) * Real.tan x) + 
                           Real.pi * (Int.floor (x / Real.pi + (1 : ℝ) / 2 * Real.sign x) : ℝ)
  Continuous F ∧ ∀ x, HasDerivAt F (f x) x := by
  sorry







theorem theorem_682421_problem {α : Type*} (A : Set α) (h : A = ∅) :
  ∀ x : α, x ∉ A := by
  sorry



theorem theorem_682503_problem
  (a b : ℕ → ℝ)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  (hb_nonneg : ∀ n, 0 ≤ b n)
  (K : ℝ) (N : ℕ)
  (hK : 0 < K)
  (h_ineq : ∀ n, n > N → a n ≤ K * b n)
  (hb_conv : Summable b) :
  Summable a := by
  sorry

theorem theorem_682488_problem
  (n : ℕ)
  {R : Type*} [CommRing R]
  (A : Matrix (Fin n) (Fin n) R) :
  A.det = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i : Fin n, A i (σ i) := by
  sorry







theorem theorem_682891_problem {R : Type*} [CommRing R] (f g : ℤ → R) (m n : ℤ) (h : m ≤ n) :
  ∑ k in Finset.Icc m n, f k * (g (k + 1) - g k) =
  (f (n + 1) * g (n + 1) - f m * g m) - ∑ k in Finset.Icc m n, g (k + 1) * (f (k + 1) - f k) := by
  sorry







theorem theorem_683221_problem (D : ℝ) 
  (h : 4 * (1 / 3 : ℝ) ^ D = 1) : 
  D = Real.log 4 / Real.log 3 := by
  sorry













theorem theorem_682962_problem (p T C : ℝ) (k : ℕ) (S : ℝ)
  (hp : 0 < p)
  (h_bound : |S - (k : ℝ) / p| ≤ C)
  (h_stop : S < T) :
  (k : ℝ) ≤ p * (T + C) := by
  sorry





theorem theorem_683663_problem (f : ℂ → ℂ)
  (h : ∀ z, f z = (Complex.exp z - Complex.exp (-z)) / 2) (z : ℂ) :
  f (z + 2 * ↑Real.pi * Complex.I) = f z := by
  sorry

theorem theorem_683378_problem (X : Type*) [TopologicalSpace X]
  [FirstCountableTopology X]
  (hKC : ∀ (s : Set X), IsCompact s → IsClosed s) :
  T2Space X := by
  sorry







theorem theorem_683449_problem
  (r : ℝ × ℝ → EuclideanSpace ℝ (Fin 3))
  (u v : ℝ)
  (h_diff : DifferentiableAt ℝ r (u, v))
  -- Definitions of partial derivatives as the differential applied to basis vectors
  (r_u : EuclideanSpace ℝ (Fin 3) := fderiv ℝ r (u, v) (1, 0))
  (r_v : EuclideanSpace ℝ (Fin 3) := fderiv ℝ r (u, v) (0, 1))
  -- Definitions of the First Fundamental Form coefficients
  (E : ℝ := inner r_u r_u)
  (F : ℝ := inner r_u r_v)
  (G : ℝ := inner r_v r_v)
  -- Arbitrary tangent vector components
  (du dv : ℝ) :
  -- The squared norm of the differential applied to (du, dv) equals the quadratic form
  ‖fderiv ℝ r (u, v) (du, dv)‖^2 = E * du^2 + 2 * F * du * dv + G * dv^2 := by
  sorry













theorem theorem_684259_problem (X : Type*) :
  ∃ f : {S : Set X // S ≠ ∅} → X, ∀ S, f S ∈ S.val := by
  sorry







theorem theorem_685040_problem (f : ℝ × ℝ → ℝ) (a b : ℝ)
  (hf : ContDiffAt ℝ 2 f (a, b)) :
  deriv (fun y ↦ deriv (fun x ↦ f (x, y)) a) b = 
  deriv (fun x ↦ deriv (fun y ↦ f (x, y)) b) a := by
  sorry

theorem theorem_684045_problem (c x : ℝ) (hc : 0 < c) (hx : 0 < x ∧ x < c) :
  IsLeast {y | ∃ u v : ℝ, 0 < u ∧ v < 0 ∧ u ^ 2 + v ^ 2 = c ^ 2 ∧ x < u ∧ x / u + y / v = 1}
    (-Real.sqrt ((c ^ (2 / 3 : ℝ) - x ^ (2 / 3 : ℝ)) ^ 3)) := by
  sorry

theorem theorem_684712_problem {α : Type*} [DecidableEq α]
  (n : ℕ) (s : Finset α) (hs : s.card = n)
  (ℱ : Finset (Finset α))
  (h_subset : ∀ F ∈ ℱ, F ⊆ s)
  (h_antichain : ∀ A ∈ ℱ, ∀ B ∈ ℱ, A ⊆ B → A = B) :
  ∑ F in ℱ, (1 : ℝ) / (Nat.choose n F.card) ≤ 1 := by
  sorry







