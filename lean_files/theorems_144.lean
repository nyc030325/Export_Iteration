import Mathlib
import Mathlib.Tactic





theorem theorem_783402_problem (a c u : ℝ) (t x s : ℝ → ℝ)
  (h_metric : (deriv s u)^2 = -(a * t u + c) * (deriv t u)^2 + (deriv x u)^2)
  (h_pos : 0 ≤ deriv s u) :
  deriv s u = Real.sqrt (-(a * t u + c) * (deriv t u)^2 + (deriv x u)^2) := by
  sorry

theorem theorem_783574_problem
  {X : Type*} [MeasurableSpace X]
  (f_seq : ℕ → X → ℝ)
  (f : X → ℝ)
  (h_meas : ∀ n, Measurable (f_seq n))
  (h_lim : ∀ x, Filter.Tendsto (fun n ↦ f_seq n x) Filter.atTop (nhds (f x))) :
  Measurable f := by
  sorry

theorem theorem_783047_problem
  (f : ℝ → ℝ)
  (g : ℝ → ℝ)
  (h_diff : Differentiable ℝ f)
  (h_g : ∀ x, g x = x * f x)
  (h_eq : ∀ x, g (3 * x) = g x + x^2)
  (h_zero : g 0 = 0) :
  ∀ x, f x = x / 8 := by
  sorry



theorem theorem_783282_problem
  (n : ℕ)
  (p : ℝ)
  (x : Fin n → ℝ)
  (i : Fin n)
  (hp : 1 < p)
  (hxi : x i ≠ 0) :
  HasDerivAt (fun t => (∑ j, |(Function.update x i t) j| ^ p) ^ (1 / p))
    (((∑ j, |x j| ^ p) ^ (1 / p)) ^ (1 - p) * |x i| ^ (p - 1) * (x i / |x i|)) (x i) := by
  sorry



theorem theorem_783722_problem
  (CDF : ℤ → ℝ)
  (Quantile : ℝ → ℤ)
  -- The fundamental property of the quantile function (inverse CDF) for the distribution di
  (h_inv : ∀ (x : ℤ) (p : ℝ), 0 ≤ p → p ≤ 1 → (Quantile p ≤ x ↔ p ≤ CDF x))
  (lb ub : ℤ)
  (h_le : lb ≤ ub)
  (fa fb : ℝ)
  (h_fa : fa = CDF (lb - 1))
  (h_fb : fb = CDF ub)
  (h_diff : fa < fb)
  (q : ℝ)
  (hq : 0 ≤ q ∧ q ≤ 1)
  -- Definition of the Quantile function for the truncated distribution as given in the problem
  (Q_trunc : ℝ → ℤ)
  (h_Q : ∀ x, Q_trunc x = Quantile (fa + x * (fb - fa)))
  -- Definition of the CDF of the truncated Zipf distribution implied by the context
  (CDF_trunc : ℤ → ℝ)
  (h_CDF_tr : ∀ x, CDF_trunc x = (CDF x - fa) / (fb - fa)) :
  -- The conclusion that y = Q(q) follows the truncated distribution
  -- is equivalent to matching the CDF condition via the inverse transform equivalence.
  ∀ k, lb ≤ k → k ≤ ub → (Q_trunc q ≤ k ↔ q ≤ CDF_trunc k) := by
  sorry



theorem theorem_784055_problem (x : ℕ → ℝ) (r q : ℝ)
  (hr : 1 < r)
  (h_sum : Summable (fun n => |x n| ^ r))
  (hq : 1 < q)
  (h_conj : 1 / r + 1 / q = 1) :
  Summable (fun n => |x n| / n) := by
  sorry

theorem theorem_783622_problem
  (E : Type*)
  (normX normY normZ : E → ℝ)
  (t : ℝ)
  (ht : 0 ≤ t ∧ t ≤ 1)
  (h_def : ∀ u : E, normZ u = (normX u) ^ t * (normY u) ^ (1 - t)) :
  ∀ u : E, normZ u ≤ (normX u) ^ t * (normY u) ^ (1 - t) := by
  sorry

theorem theorem_783954_problem {α : Type*} (R : Set (FreeGroup α)) :
  Nonempty (PresentedGroup R ≃ (FreeGroup α ⧸ Subgroup.normalClosure R)) := by
  sorry



theorem theorem_783851_problem (A B C D : ℝ) (x y z : ℝ)
  (h_plane : A * x + B * y + C * z = D)
  (hz : z ≠ 0)
  (a b c : ℝ)
  (ha : a = x / z)
  (hb : b = y / z)
  (hc : c = z) :
  A * a + B * b - D / c = - C := by
  sorry

theorem theorem_783857_problem (a b c : ℝ)
  (h1 : a + b + c = 0)
  (h2 : a^2 + b^2 + c^2 = 1) :
  a^4 + b^4 + c^4 = 1 / 2 := by
  sorry



theorem theorem_783892_problem 
  (M : Type*) 
  (SymplecticForm : Type*)
  (ω : SymplecticForm)
  (Surface : Type*)
  (HomologyClass : Type*)
  (homology_class : Surface → HomologyClass)
  (symplectic_area : Surface → SymplecticForm → ℝ)
  (is_symplectic : Surface → SymplecticForm → Prop)
  (S : Surface)
  (h_area : symplectic_area S ω = 0)
  (S' : Surface)
  (h_homologous : homology_class S' = homology_class S) :
  ¬ is_symplectic S' ω := by
  sorry

theorem theorem_784283_problem
  (a b c d : ℂ)
  (h_det : a * d - b * c ≠ 0)
  (z₁ z₂ z₃ : ℂ)
  (h_distinct : z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃)
  (h_f₁ : c * z₁ + d ≠ 0 ∧ (a * z₁ + b) / (c * z₁ + d) = z₁)
  (h_f₂ : c * z₂ + d ≠ 0 ∧ (a * z₂ + b) / (c * z₂ + d) = z₂)
  (h_f₃ : c * z₃ + d ≠ 0 ∧ (a * z₃ + b) / (c * z₃ + d) = z₃) :
  ∀ z : ℂ, c * z + d ≠ 0 → (a * z + b) / (c * z + d) = z := by
  sorry



theorem theorem_783875_problem (A : Type*) [CommRing A]
  (h : ∀ (U : Set (PrimeSpectrum A)), IsOpen U → U.Nonempty →
    ∃ x ∈ U, IsClosed ({x} : Set (PrimeSpectrum A))) :
  Ideal.jacobson (⊥ : Ideal A) ≤ nilradical A := by
  sorry





theorem theorem_784479_problem
  {I J K L M P Q R : Type*}
  [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype M] [Fintype P] [Fintype Q] [Fintype R]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [DecidableEq M] [DecidableEq P] [DecidableEq Q] [DecidableEq R]
  (g : (P → Q → R → ℝ) → (I → J → ℝ))
  (f : (I → J → ℝ) → (K → L → M → ℝ))
  (X : P → Q → R → ℝ)
  (hg : DifferentiableAt ℝ g X)
  (hf : DifferentiableAt ℝ f (g X))
  (k : K) (l : L) (m : M) (p : P) (q : Q) (r : R) :
  let F := f ∘ g
  let basis_X := Pi.single p (Pi.single q (Pi.single r (1 : ℝ)))
  let partial_F_X := fderiv ℝ F X basis_X k l m
  let RHS := ∑ i : I, ∑ j : J,
    (fderiv ℝ f (g X) (Pi.single i (Pi.single j (1 : ℝ))) k l m) *
    (fderiv ℝ g X basis_X i j)
  partial_F_X = RHS := by
  sorry

theorem theorem_783207_problem
  (V : Type*) [AddCommGroup V] [Module ℂ V]
  (h : V → V → ℂ)
  -- Linearity and Hermitian properties of h
  (h_lin1 : ∀ (c : ℂ) (v w : V), h (c • v) w = c * h v w)
  (h_clin2 : ∀ (c : ℂ) (v w : V), h v (c • w) = star c * h v w)
  (h_herm : ∀ (v w : V), h w v = star (h v w)) :
  -- Definitions
  let J : V → V := λ v ↦ I • v
  let ω : V → V → ℝ := λ v w ↦ (h v w).im
  -- Setup for "Type (1,1)" definition via complexification V_C = V x V
  let Vc := V × V
  -- Extension of J to Vc
  let J_ext : Vc → Vc := λ z ↦ (J z.1, J z.2)
  -- Multiplication by the "complexification i" (denoted I_ext here)
  let I_ext : Vc → Vc := λ z ↦ (-z.2, z.1) 
  -- Eigenspaces V^{1,0} and V^{0,1}
  let V10 := {z : Vc | J_ext z = I_ext z}
  let V01 := {z : Vc | J_ext z = - I_ext z}
  -- Complex bilinear extension of ω
  let Omega : Vc → Vc → ℂ := λ z1 z2 ↦ 
    (ω z1.1 z2.1 - ω z1.2 z2.2 : ℂ) + I * (ω z1.1 z2.2 + ω z1.2 z2.1)
  -- Definition of type (1,1)
  let is_type_1_1 := 
    (∀ u v : Vc, u ∈ V10 → v ∈ V10 → Omega u v = 0) ∧ 
    (∀ u v : Vc, u ∈ V01 → v ∈ V01 → Omega u v = 0)
  -- The statement
  is_type_1_1 ↔ ∀ v w : V, ω (J v) (J w) = ω v w := by
  sorry

theorem theorem_784088_problem
  {X : Type*}
  (h1 h2 : X → ℝ)
  (u : ℝ)
  (hu : u > 0)
  (x : X) :
  Real.sqrt ((h1 x)^2 + (h2 x)^2) ≤ u ↔
  ∃ b1 b2 : ℝ, b1 = h1 x ∧ b2 = h2 x ∧ Real.sqrt (b1^2 + b2^2) ≤ u := by
  sorry



theorem theorem_783171_problem (n : ℕ)
  (h_odd : Odd n)
  (h_composite : ¬ Nat.Prime n)
  (h_gt1 : n > 1) :
  jacobiSym (-1) n = (-1) ^ ((n - 1) / 2) := by
  sorry

theorem theorem_784282_problem
  (x : ℝ)
  (n : ℕ)
  (hx : x ≠ 0)
  (T_mul : ℝ → ℝ → ℝ)
  (h_mul : ∀ a b, T_mul a b = a * b)
  (T_plus : List ℝ → ℝ)
  (h_plus : ∀ l, T_plus l = l.sum)
  (copies : List ℝ)
  (h_copies : copies = List.replicate n x)
  (S : ℝ)
  (h_S : S = T_plus (copies.map (fun xi => T_mul xi x))) :
  S = n * x^2 := by
  sorry



theorem theorem_785116_problem
  {K : Type*} [Field K]
  (n : ℕ) (a : ℕ → K) (β : K)
  (hn : n > 0)
  (h_coeffs : ∀ i < n, a i ≠ 0)
  (h_root : β ^ n + (∑ i in Finset.range n, a i * β ^ i) = 0) :
  β⁻¹ = -(1 / a 0) * (β ^ (n - 1) + ∑ i in Finset.range (n - 1), a (i + 1) * β ^ i) := by
  sorry









theorem theorem_785373_problem
  (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X]
  (f : ℕ → C(X, ℝ))
  (h_cauchy : ∀ ε > 0, ∃ N, ∀ n m : ℕ, N ≤ n → N ≤ m → ∀ x : X, |f n x - f m x| < ε) :
  ∃ g : C(X, ℝ), ∀ ε > 0, ∃ N, ∀ n : ℕ, N ≤ n → ∀ x : X, |f n x - g x| < ε := by
  sorry





theorem theorem_784354_problem (qs : List (Quaternion ℝ)) (v : Quaternion ℝ)
  (hv : v.re = 0) (hqs : ∀ q ∈ qs, q ≠ 0) :
  List.foldr (fun q acc => q * acc * q⁻¹) v qs = qs.prod * v * qs.prod⁻¹ := by
  sorry

theorem theorem_784838_problem (n : ℕ) (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
  let d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun u v => Real.sqrt (∑ i, (u i - v i)^2)
  let ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun u v => ⨆ i, |u i - v i|
  let B_d := {y | d x y < ε}
  let B_ρ := {y | ρ x y < ε}
  B_d ⊆ B_ρ := by
  sorry





theorem theorem_785634_problem
  {S : Type*}
  [LinearOrder S]
  [IsWellOrder S (· < ·)]
  (zero : S)
  (h_min : ∀ x : S, zero ≤ x)
  (h_dense : ∀ x : S, x ≠ zero → ∃ y : S, y < x)
  (φ : S → Prop)
  (h1 : φ zero)
  (h2 : ∀ x : S, (∀ u : S, u < x → φ u) → φ x) :
  ∀ u : S, φ u := by
  sorry





theorem theorem_785949_problem
  (f : ℝ → ℝ)
  (hf : Continuous f)
  (x h : ℝ)
  (h_pos : h > 0) :
  f x + (1 / h) * ∫ t in x..(x + h), (f t - f x) = (1 / h) * ∫ t in x..(x + h), f t := by
  sorry









theorem theorem_786243_problem (f : ℕ →. ℕ) (hf : Partrec f) :
  ∃ T : ℕ →. Unit, Partrec T ∧ ∀ x, x ∈ f.Dom ↔ x ∈ T.Dom := by
  sorry

theorem theorem_785689_problem 
  (g : ℝ → ℝ) 
  (hg : ConvexOn ℝ Set.univ g)
  (f : ℝ × ℝ → ℝ)
  (hf : ∀ x y, 0 < y → f (x, y) = y * g (x / y)) :
  ConvexOn ℝ {p : ℝ × ℝ | 0 < p.2} f := by
  sorry

theorem theorem_786051_problem
  {α : Type*}
  (v : ℕ → α → ℝ)
  (M : ℕ → ℝ)
  (hM_nonneg : ∀ n, 0 ≤ M n)
  (h_bound : ∃ N, ∀ n ≥ N, ∀ x, |v n x| ≤ M n)
  (h_conv : Summable M) :
  ∃ f : α → ℝ, TendstoUniformly (fun n x ↦ ∑ i in Finset.range n, v i x) f Filter.atTop := by
  sorry

theorem theorem_785724_problem (r : ℝ) (hr : 0 < r ∧ r < 1) :
  StrictAntiOn (fun x => x ^ r + r ^ x) (Set.Iio 0) := by
  sorry

theorem theorem_786109_problem (n m k : ℕ) (h_eq : n = m * k) (hk : k ≥ 1) :
  (Fintype.card {f : Fin n → Fin k // ∀ i : Fin k, Fintype.card {x // f x = i} = m} : ℝ) / 
  (Fintype.card (Fin n → Fin k) : ℝ) =
  (n.factorial : ℝ) / ((m.factorial : ℝ) ^ k * (k : ℝ) ^ n) := by
  sorry







theorem theorem_786405_problem
  (f : ℝ → ℝ) (x : ℝ → ℝ) (a b : ℝ)
  (ha : a ≠ 0) (hb : b ≠ 0)
  (hf : Differentiable ℝ f)
  (hx : Differentiable ℝ x)
  (h_eq : ∀ c, c ≠ 0 → f (a * x c + b) = f c)
  (h_diff_ne : ∀ c, c ≠ 0 → deriv f (a * x c + b) ≠ 0) :
  ∀ c, c ≠ 0 → deriv x c = 1 / a := by
  sorry











theorem theorem_786629_problem (a s t : ℕ → ℝ)
  (h_nonneg : ∀ n, 0 ≤ a n)
  (h_s : ∀ n, s n = ∑ i in Finset.range n, a i)
  (h_t_unbounded : ¬ BddAbove (Set.range t))
  (h_rel : ∀ k, ∃ n, t k ≤ 2 * s n)
  (h_summable : Summable a) :
  BddAbove (Set.range s) := by
  sorry











theorem theorem_787299_problem
  (a b c p q r : ℝ)
  (f g : ℝ → ℝ)
  (hf : ∀ x, f x = a * x^2 + b * x + c)
  (hg : ∀ x, g x = p * x^2 + q * x + r)
  (h_bound : ∃ M : ℝ, ∀ x : ℝ, |f x - g x| ≤ M) :
  a = p ∧ b = q := by
  sorry





theorem theorem_787114_problem (n : ℕ) (hn : n > 0) :
  ∑ k in Finset.Icc 1 n, (k : ℚ)^4 = 
  (n * (n + 1) * (2 * n + 1) * (3 * (n : ℚ)^2 + 3 * n - 1)) / 30 := by
  sorry

theorem theorem_787362_problem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] (A B : H →L[ℂ] H)
  (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hAB : Commute A B) :
  ∃ (ι : Type) (_ : Fintype ι) (b : OrthonormalBasis ι ℂ H),
    (∀ i, ∃ μ : ℂ, A (b i) = μ • b i) ∧
    (∀ i, ∃ ν : ℂ, B (b i) = ν • b i) := by
  sorry



theorem theorem_786730_problem 
  (θ c C' : ℝ) 
  (hθ : 0 < θ) (hc : 0 < c) (hC' : 0 < C')
  (V : Type*) 
  (norm_H10 : V → ℝ) -- Represents the H_0^1(U) norm, defined as ||Du||_{L^2} in the problem context
  (norm_L2 : V → ℝ)  -- Represents the L^2(U) norm
  -- The constant C' is identified in the solution context as the Poincaré constant satisfying this inequality
  (h_poincare : ∀ u : V, norm_L2 u ≤ C' * norm_H10 u)
  (u : V)
  (β γ : ℝ)
  (hβ : β = (θ / 4) * (1 + c / C' ^ 2))
  (hγ : γ = (c * θ) / (4 * C' ^ 2)) :
  (θ / 2) * (norm_H10 u) ^ 2 ≥ β * (norm_H10 u) ^ 2 - γ * (norm_L2 u) ^ 2 := by
  sorry

theorem theorem_787109_problem :
  ∃ (G : Type*) (V : Type*)
    (_ : TopologicalSpace G) (_ : Group G) (_ : TopologicalGroup G)
    (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (_ : CompleteSpace V)
    (ρ : Representation ℂ G V),
    (¬ FiniteDimensional ℂ V) ∧
    (∀ (v w : V), Continuous (fun g => inner (ρ g v) w : G → ℂ)) ∧
    ¬ (∀ (v : V), ∃ (U : Set G), IsOpen U ∧ 1 ∈ U ∧ ∀ g ∈ U, ρ g v = v) := by
  sorry

theorem theorem_787160_problem
  {G : Type*} [Group G]
  (Gi Hi : ℕ → Subgroup G)
  (h_sub : ∀ i, Hi i ≤ Gi i)
  (h_mono_G : Monotone Gi)
  (h_mono_H : Monotone Hi) :
  (⨆ i, Hi i).relindex (⨆ i, Gi i) ≤ ⨆ i, (Hi i).relindex (Gi i) := by
  sorry



theorem theorem_787642_problem (a : ℕ → ℝ) 
  (h : Summable (fun n ↦ a (n + 1))) : 
  Summable a := by
  sorry

theorem theorem_787636_problem
  -- Define abstract types for Distributions and Test Functions
  (Distribution TestFunction : Type*)
  -- Define the pairing/integral operation <T, φ>
  (pairing : Distribution → TestFunction → ℝ)
  -- The Dirac Delta distribution δ
  (delta : Distribution)
  -- The test function φ
  (phi : TestFunction)
  -- The integer k
  (k : ℕ)
  -- Derivative operators for Distribution and Test Function
  (derivD : Distribution → Distribution)
  (derivF : TestFunction → TestFunction)
  -- Condition: The definition of the derivative of a distribution
  -- <T', φ> = -<T, φ'>
  (h_deriv_def : ∀ (T : Distribution) (f : TestFunction),
    pairing (derivD T) f = - pairing T (derivF f)) :
  -- The integration identity to prove
  pairing (derivD^[k] delta) phi = (-1 : ℝ)^k * pairing delta (derivF^[k] phi) := by
  sorry



theorem theorem_786814_problem (x y z : ℕ) (hx : x > 0) (hy : y > 0) (hz : z > 0) :
  5^x * 7^y + 4 ≠ 3^z := by
  sorry

theorem theorem_787750_problem (p : ℕ) [Fact (Nat.Prime p)] :
  ¬ Nonempty (Module (PadicInt p) ℤ) := by
  sorry



theorem theorem_787575_problem
  (f g : ℝ → ℝ) (a : ℝ)
  (hg : DifferentiableAt ℝ g a)
  (hf : DifferentiableAt ℝ f (g a))
  (h_cond : deriv g a = 0) :
  deriv (f ∘ g) a = 0 := by
  sorry

theorem theorem_788110_problem (a : ℕ → ℝ)
  (h_even : ∀ n : ℕ, n ≠ 0 → a (2 * n) = 1 / (2 * n : ℝ))
  (h_odd : ∀ n : ℕ, a (2 * n + 1) = 1 / ((2 * n + 1 : ℝ) ^ 2)) :
  Filter.Tendsto a Filter.atTop (nhds 0) := by
  sorry



theorem theorem_787620_problem 
  {Div : Type*} [AddCommGroup Div]
  (pull : Div →+ Div)
  (m : ℕ) (hm : m > 0)
  (T O : Div)
  (div_f div_g : Div)
  (h_f : div_f = m • T - m • O)
  (h_g : div_g = pull T - pull O)
  (h_eq : pull div_f = m • div_g) :
  pull T - pull O = m • T - m • O := by
  sorry



theorem theorem_787869_problem
  (a : ℕ → ℝ)
  (h_a : ∀ n, a n = 2 / ((Nat.factorial n : ℝ) * (Nat.factorial (n + 2) : ℝ)))
  (f : PowerSeries ℝ)
  (h_f : f = PowerSeries.mk a) :
  f ^ 2 = PowerSeries.mk (fun n => 4 / ((Nat.factorial (n + 2) : ℝ) ^ 2) * (Nat.choose (2 * n + 4) n : ℝ)) := by
  sorry

theorem theorem_788544_problem
  (n m d : ℕ)
  (hn : 0 < n)
  (x : Fin n → Fin m → ℝ)
  (μ : Fin m → ℝ)
  (hμ : μ = (n : ℝ)⁻¹ • (∑ i : Fin n, x i))
  (V : Matrix (Fin m) (Fin d) ℝ)
  (β : Fin n → Fin d → ℝ)
  (hβ : ∀ k, β k = Matrix.mulVec V.transpose (x k - μ)) :
  ∑ k : Fin n, β k = 0 := by
  sorry



theorem theorem_788363_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : ℕ}
  (v : Basis (Fin n) K V)
  (w : Basis (Fin n) K V)
  (form : V →ₗ[K] V →ₗ[K] K)
  (h_sym : ∀ x y, form x y = form y x)
  (A B P : Matrix (Fin n) (Fin n) K)
  (hA : ∀ i j, A i j = form (v i) (v j))
  (hB : ∀ i j, B i j = form (w i) (w j))
  (hP : ∀ j, w j = ∑ i, (P i j) • (v i)) :
  B = P.transpose * A * P := by
  sorry

theorem theorem_788287_problem :
  ∃ (a b : ℤ → ℝ),
    Set.Infinite {n | n < 0 ∧ a n ≠ 0} ∧
    Set.Infinite {n | n < 0 ∧ b n ≠ 0} ∧
    ∃ k : ℤ, ¬ Summable (fun n ↦ a n * b (k - n)) := by
  sorry





theorem theorem_788372_problem (d k : ℕ) (h : d > 0) :
  ∑ i in Finset.range (k + 1), Nat.choose (d + i - 1) (d - 1) = Nat.choose (d + k) k := by
  sorry



