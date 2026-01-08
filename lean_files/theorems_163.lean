import Mathlib
import Mathlib.Tactic

theorem theorem_887587_problem (a h p : ℝ) (ha : 0 < a) (hh : 0 < h) :
  ∫ x : ℝ, Complex.exp (-I * (p : ℂ) * (x : ℂ) / (h : ℂ)) / ((x : ℂ) ^ 2 + (a : ℂ) ^ 2) =
  ((π / a) * Real.exp (- (|p| * a) / h) : ℂ) := by
  sorry

theorem theorem_887847_problem (lt : ℂ → ℂ → Prop)
  (h1 : ∀ x y : ℂ, (x = y ∧ ¬lt x y ∧ ¬lt y x) ∨ (x ≠ y ∧ lt x y ∧ ¬lt y x) ∨ (x ≠ y ∧ ¬lt x y ∧ lt y x))
  (h2 : ∀ x y z : ℂ, lt x y → lt y z → lt x z)
  (h3 : ∀ x y z : ℂ, lt x y → lt (x + z) (y + z))
  (h4 : ∀ x y z : ℂ, lt 0 x → lt x y → lt 0 z → lt (x * z) (y * z)) :
  False := by
  sorry

theorem theorem_887647_problem
  (V₁ V₂ E₁ E₂ : Type*)
  [Fintype E₁] [Fintype E₂]
  [DecidableEq V₁] [DecidableEq V₂]
  [DecidableEq E₁] [DecidableEq E₂]
  (inc₁ : E₁ → Sym2 V₁)
  (inc₂ : E₂ → Sym2 V₂)
  (m₁ : V₁ → V₁ → ℕ)
  (m₂ : V₂ → V₂ → ℕ)
  (h₁ : ∀ u v, m₁ u v = Fintype.card {e : E₁ // inc₁ e = Sym2.mk (u, v)})
  (h₂ : ∀ u v, m₂ u v = Fintype.card {e : E₂ // inc₂ e = Sym2.mk (u, v)}) :
  (∃ (f : V₁ ≃ V₂) (g : E₁ ≃ E₂), ∀ e, inc₂ (g e) = (inc₁ e).map f) ↔
  (∃ (f : V₁ ≃ V₂), ∀ u v, m₁ u v = m₂ (f u) (f v)) := by
  sorry

theorem theorem_887374_problem (k : ℕ) (a : ℝ) (h : 1 < a) :
  ∑' n : ℕ, (-1 : ℝ) ^ n * (n.choose k) * (a - 1) ^ (n - k) = (-1 : ℝ) ^ k * a ^ (-(k + 1 : ℤ)) := by
  sorry









theorem theorem_888231_problem (n : ℕ) (a b x : ℝ)
  (hn : 0 < n)
  (hx : x ∈ Set.Icc a b) :
  ∏ i in Finset.range (n + 1), |x - (a + (i : ℝ) * (b - a)) / n| ≤
  (n.factorial : ℝ) * (b - a) ^ (n + 1) / (4 * (n : ℝ) ^ (n + 1)) := by
  sorry



theorem theorem_888413_problem
  {X : Type*} [TopologicalSpace X]
  (f : X → Set.Icc (0 : ℝ) 1)
  (hf : Continuous f)
  (U : Set (Set.Icc (0 : ℝ) 1))
  (hU : IsOpen U) :
  IsOpen (f ⁻¹' U) := by
  sorry







theorem theorem_888199_problem
  (S : ℕ → ℝ)
  (z : ℝ)
  (hS : ∀ n, S n = ∑ k in Finset.Icc 1 n, (k : ℝ)^2)
  (hz : |z| < 1) :
  ∑' n, S n * z^n = (z * (1 + z)) / (1 - z)^4 := by
  sorry









theorem theorem_888767_problem (x y : ℕ) :
  (2 : ℤ) ^ x - (3 : ℤ) ^ y = 1 ↔ (x = 2 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  sorry



theorem theorem_889305_problem (f : ℝ → ℝ)
  (h : ∀ x y : ℝ, f x - f y = 2 * (x - y)) :
  ∃ c : ℝ, ∀ x : ℝ, f x = 2 * x + c := by
  sorry







theorem theorem_888012_problem
  -- Abstract types for geometric objects
  (Surface Curve Point : Type*)
  -- Abstract predicates and functions representing geometric properties
  (is_smooth : Surface → Prop)
  (is_curve_on : Curve → Surface → Prop)
  (is_point_on : Point → Curve → Prop)
  (arithmetic_genus : Curve → ℤ)
  (order_of_vanishing : Curve → Point → ℕ)
  -- Relation representing "X_tilde is blow-up of X at p AND C_tilde is strict transform of C"
  (is_blowup_strict_transform : Surface → Surface → Curve → Curve → Point → Prop)
  -- Variables
  (X X_tilde : Surface)
  (C C_tilde : Curve)
  (p : Point)
  (m : ℕ)
  -- Conditions
  (h_smooth : is_smooth X)
  (h_curve : is_curve_on C X)
  (h_point : is_point_on p C)
  (h_m : m = order_of_vanishing C p)
  (h_setup : is_blowup_strict_transform X X_tilde C C_tilde p) :
  arithmetic_genus C_tilde = arithmetic_genus C - (m : ℤ) * ((m : ℤ) - 1) / 2 := by
  sorry

theorem theorem_888985_problem (k : ℝ) (P : ℕ → ℝ)
  (h_k : 2 * k + 1 > 0)
  (h_rec : ∀ n : ℕ, 0 < n → P (2 * n) = (2 * k + 1) / (2 * n) * (P n) ^ 2) :
  Filter.Tendsto (fun m ↦ P (2 ^ m)) Filter.atTop (nhds 0) := by
  sorry





theorem theorem_889480_problem (P : ℕ) (hP : P > 0) : 
  ∃ p, Nat.Prime p ∧ p > P := by
  sorry



theorem theorem_889364_problem (x y x' y' θ : ℝ)
  (f : ℝ → ℝ)
  (h_f : ∀ t, f t = -5 * (10 : ℝ) ^ (-(6 : ℤ)) * t^3 + 0.0004 * t^2 + 0.0582 * t - 0.4397)
  (h_tan : Real.tan θ = 0.0222)
  (h_x' : x' - 10 = Real.cos θ * (x - 10) - Real.sin θ * (y - 0.1773))
  (h_y' : y' - 0.1773 = Real.sin θ * (x - 10) + Real.cos θ * (y - 0.1773)) :
  y' = f x' ↔ 
  0.1773 + Real.sin θ * (x - 10) + Real.cos θ * (y - 0.1773) = 
  f (10 + Real.cos θ * (x - 10) - Real.sin θ * (y - 0.1773)) := by
  sorry

theorem theorem_889594_problem (ε : ℝ) (y : ℝ → ℝ)
  (h_diff_y : DifferentiableOn ℝ y (Set.Ioi 0))
  (h_y_nonzero : ∀ x, 0 < x → y x ≠ 0)
  (h_diff_quot : DifferentiableOn ℝ (fun x => deriv y x / y x) (Set.Ioi 0))
  (h_ode : ∀ x, 0 < x → deriv (fun x => deriv y x / y x) x + ε / x^2 = 0) :
  ∃ c₁ c₂ : ℝ, ∀ x, 0 < x → y x = c₂ * Real.exp (ε * Real.log x + c₁ * x) := by
  sorry



theorem theorem_889434_problem (x y z a b c k : ℝ)
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (h : x / a = k ∧ y / b = k ∧ z / c = k) :
  x = a * k ∧ y = b * k ∧ z = c * k := by
  sorry

theorem theorem_889854_problem (r₁ r₂ θ₁ θ₂ : ℝ)
  (hr₁ : r₁ > 0) (hr₂ : r₂ > 0)
  (z₁ z₂ : ℂ)
  (hz₁ : z₁ = r₁ * Complex.exp (θ₁ * Complex.I))
  (hz₂ : z₂ = r₂ * Complex.exp (θ₂ * Complex.I)) :
  z₁ * z₂ = (r₁ * r₂) * Complex.exp ((θ₁ + θ₂) * Complex.I) := by
  sorry

theorem theorem_890008_problem
  (a : ℕ → ℝ)
  (h1 : Summable a)
  (h2 : Summable (fun n ↦ |a n|))
  (h3 : ∑' n, a n = ∑' n, |a n|) :
  ∀ n, a n ≥ 0 := by
  sorry









theorem theorem_890428_problem {G : Type*} [Group G] {X : Type*}
  (T : G →* Equiv.Perm X) (g : G) (x : X) :
  (T g)⁻¹ x = T (g⁻¹) x := by
  sorry













theorem theorem_890498_problem :
  ¬ ∃ (I : Type) (_ : DecidableEq I) (p : I → ℕ) (_ : ∀ i, Nat.Prime (p i)),
    Nonempty ((ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)) ≃+ DirectSum I (fun i => ZMod (p i))) := by
  sorry



theorem theorem_889655_problem
  (D : Set (ℝ × ℝ))
  (f : ℝ × ℝ → ℝ)
  (c : ℝ → ℝ)
  (hf : ConvexOn ℝ D f)
  (h_bound : ∀ x y, (x, y) ∈ D → f (x, y) ≤ c y) :
  let S := {y : ℝ | ∃ x, (x, y) ∈ D}
  let g := fun y ↦ sSup {z | ∃ x, (x, y) ∈ D ∧ z = f (x, y)}
  ConvexOn ℝ S g := by
  sorry





theorem theorem_890727_problem
  (h : ℂ → ℂ) (c : ℂ) (S : Set ℂ)
  (h_anal : Differentiable ℂ h)
  (h_non_iso : ∃ z, AccPt z (Filter.principal S))
  (h_on_S : ∀ z ∈ S, h z = c) :
  ∀ z, h z = c := by
  sorry

theorem theorem_890919_problem
  (j n r : ℕ)
  (hj : 2 ≤ j)
  (hjn : j ≤ n)
  (hn : 2 ≤ n)
  (hr : 0 < r) :
  (j * (j - 1) : ℝ) / (2 * n) ≥ (j ^ 2 : ℝ) / (4 * n * r) := by
  sorry

theorem theorem_891127_problem
  (s_seq t_seq : ℕ → ℝ)
  (s t : ℝ)
  (h₁ : Filter.Tendsto s_seq Filter.atTop (nhds s))
  (h₂ : Filter.Tendsto t_seq Filter.atTop (nhds t)) :
  Filter.Tendsto (fun n ↦ s_seq n * t_seq n) Filter.atTop (nhds (s * t)) := by
  sorry

theorem theorem_891248_problem (n : ℕ) (K : ℕ → ℝ)
  (hK_pos : ∀ i, 1 ≤ i ∧ i ≤ n → 0 < K i)
  (h_exist_C : ∃ C > 0, ∀ i j, 1 ≤ i ∧ i ≤ n → 1 ≤ j ∧ j ≤ n → K j ≤ C * K i) :
  ∃ C_star > 0, ∀ i j, 1 ≤ i ∧ i ≤ n → 1 ≤ j ∧ j ≤ n → K j ≤ C_star * K i := by
  sorry

theorem theorem_891759_problem (f : ℂ → ℂ)
  (h_entire : Differentiable ℂ f)
  (h_bounded : ∃ M : ℝ, ∀ z : ℂ, Complex.abs (f z) ≤ M) :
  ∃ c : ℂ, ∀ z : ℂ, f z = c := by
  sorry

theorem theorem_891070_problem (θ : ℝ) (n : ℕ) (hn : n > 0) (z : ℂ)
  (hz : z = ↑(Real.cos θ) + Complex.I * ↑(Real.sin θ)) :
  ∑ k in Finset.range n, Real.sin ((2 * (k : ℝ) + 1) * θ) =
  ((1 - z ^ (2 * n + 1)) / (1 - z)).im - ((1 - z ^ (2 * n + 2)) / (1 - z ^ 2)).im := by
  sorry

theorem theorem_891298_problem
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (h_rank : A.rank = n)
  (x_star : Fin n → ℝ)
  (h_normal : Matrix.mulVec A.transpose (Matrix.mulVec A x_star - b) = 0)
  (e : Fin m → ℝ)
  (he : e = Matrix.mulVec A x_star - b) :
  ∀ u : Fin n → ℝ, Matrix.dotProduct e (Matrix.mulVec A u) = 0 := by
  sorry







theorem theorem_891244_problem
  (expIterative : ℝ → ℕ → ℝ)
  (h_exp : ∀ (x : ℝ) (n : ℕ), expIterative x n = x ^ n)
  (doubleExpRecursive : ℝ → ℕ → ℝ)
  (h_base : ∀ (x : ℝ) (n : ℕ), n ≤ 4 → doubleExpRecursive x n = expIterative x n)
  (h_step : ∀ (x : ℝ) (n : ℕ), n > 4 →
    doubleExpRecursive x n = doubleExpRecursive x (n / 2) * doubleExpRecursive x ((n + 1) / 2)) :
  ∀ (x : ℝ) (n : ℕ), doubleExpRecursive x n = x ^ n := by
  sorry





theorem theorem_891965_problem
  {n m : Type*} [NormedAddCommGroup n] [InnerProductSpace ℝ n]
  [NormedAddCommGroup m] [InnerProductSpace ℝ m]
  (f : m → ℝ) (Sf : Set m)
  (A : n →L[ℝ] m) (b : m) (c : n) (d : ℝ)
  (h : n → ℝ) (D : Set n)
  (h_dom_pos : ∀ x ∈ D, 0 < inner c x + d)
  (h_map : ∀ x ∈ D, (inner c x + d)⁻¹ • (A x + b) ∈ Sf)
  (h_eq : ∀ x ∈ D, h x = (inner c x + d) * f ((inner c x + d)⁻¹ • (A x + b)))
  (hD_convex : Convex ℝ D)
  (hf_convex : ConvexOn ℝ Sf f) :
  ConvexOn ℝ D h := by
  sorry







theorem theorem_891075_problem (a b c d : ℝ) (n q : ℤ)
  (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
  (hq : n = 2 * q) :
  (q : ℝ) * (a * c + n * b * d)^2 + (n : ℝ) * (a * d - q * b * c)^2 =
  (a^2 + (n : ℝ) * q * b^2) * ((q : ℝ) * c^2 + (n : ℝ) * d^2) := by
  sorry

theorem theorem_892093_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [SmoothManifoldWithCorners I' N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P] [SmoothManifoldWithCorners I'' P]
  (f : M → N) (g : N → P) (p : M)
  (hf : Smooth I I' f) (hg : Smooth I' I'' g) :
  ∀ X : TangentSpace I p,
  mfderiv I I'' (g ∘ f) p X = mfderiv I' I'' g (f p) (mfderiv I I' f p X) := by
  sorry











theorem theorem_892746_problem {α : Type*} (E : ℕ → Set α) :
  (⋃ n, ⋂ k ≥ n, E k) ⊆ (⋂ n, ⋃ k ≥ n, E k) := by
  sorry

theorem theorem_892387_problem (V : Type*) [Fintype V] (E : V → V → Prop)
  (h_tournament : ∀ u v : V, u ≠ v → (E u v ∨ E v u) ∧ ¬(E u v ∧ E v u)) :
  ∃ l : List V, l.Nodup ∧ (∀ v : V, v ∈ l) ∧ l.Chain' E := by
  sorry

theorem theorem_892894_problem
  (C M x0 : ℝ)
  (hC : 0 < C)
  (hM : 1 < M)
  (hx0 : 0 < x0)
  (u : ℝ → ℝ)
  (T : ℝ)
  (hT : 0 < T)
  (h_diff : DifferentiableOn ℝ u (Set.Ico 0 T))
  (h_ode : ∀ t ∈ Set.Ico 0 T, deriv u t = C * (u t) ^ M)
  (h_init : u 0 = x0)
  (h_pos : ∀ t ∈ Set.Ico 0 T, 0 < u t)
  (h_blowup : Filter.Tendsto u (nhdsWithin T (Set.Iio T)) Filter.atTop) :
  T ≥ (x0 ^ (-(M - 1))) / (C * (M - 1)) := by
  sorry













theorem theorem_893442_problem
  (P Q : ℝ → ℝ → ℝ)
  (R : Set (ℝ × ℝ))
  -- Abstract function representing the line integral around curve C
  (line_integral_C : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ)
  -- Abstract function representing the double integral over a region
  (double_integral : Set (ℝ × ℝ) → (ℝ → ℝ → ℝ) → ℝ)
  -- Condition: Green's Theorem holds for the curve C and region R given the smoothness of P and Q
  (h_green : line_integral_C P Q = double_integral R (fun x y ↦ deriv (fun x' ↦ Q x' y) x - deriv (fun y' ↦ P x y') y))
  -- Condition: The curl of the vector field is zero throughout R
  (h_curl_zero : ∀ x y, (x, y) ∈ R → deriv (fun x' ↦ Q x' y) x - deriv (fun y' ↦ P x y') y = 0)
  -- Condition: The integral of zero over R is zero
  (h_int_zero : double_integral R (fun _ _ ↦ 0) = 0) :
  line_integral_C P Q = 0 := by
  sorry



theorem theorem_892521_problem (a b t p s : ℤ)
  (X Y Z Q R : ℤ)
  (hX : X = 2 * p^2 + 2 * (a + b + t) * p * s + (a * b + a * t + b * t) * s^2)
  (hY : Y = 2 * p^2 + 2 * (b + t - a) * p * s + (b * t - a^2) * s^2)
  (hZ : Z = 2 * p^2 + 2 * (a + t - b) * p * s + (a * t - b^2) * s^2)
  (hQ : Q = 2 * p^2 + 2 * (a + b - t) * p * s + (a * b - t^2) * s^2)
  (hR : R = 4 * p^2 + 2 * (a + b + t) * p * s + (a^2 + b^2 + t^2) * s^2) :
  X^2 + Y^2 + Z^2 + Q^2 = R^2 := by
  sorry





theorem theorem_893256_problem
  {X : Type*}
  (f g : Set X → Set X)
  (hf : ∀ A, f A = Set.univ)
  (hg : ∀ A, g A = Set.univ) :
  let rel_inv_f : Set X → Set X → Prop := λ A B ↦ A ⊆ f B
  let rel_g : Set X → Set X → Prop := λ A B ↦ B ⊆ g A
  let comp : Set X → Set X → Prop := λ A B ↦ ∃ C, rel_inv_f A C ∧ rel_g C B
  ∀ A B : Set X, comp A B := by
  sorry



theorem theorem_893283_problem (x : ℝ)
  (h1 : Real.cos x ≠ 0)
  (h2 : x * Real.sin x + Real.cos x ≠ 0) :
  deriv (fun x => - (x / Real.cos x) * (1 / (x * Real.sin x + Real.cos x)) + Real.tan x) x =
  x^2 / (x * Real.sin x + Real.cos x)^2 := by
  sorry



theorem theorem_893541_problem (p s : ℝ)
  (hp : 0 ≤ p ∧ p ≤ 1)
  (P : ℕ → ℝ)
  (hP : ∀ k, P k = (1 / 5 : ℝ) * (if k = 0 then 1 else 0) + 
                   (4 / 5 : ℝ) * (Nat.choose 3 k : ℝ) * p^k * (1 - p)^(3 - k)) :
  ∑' k, P k * s^k = 1 / 5 + 4 / 5 * (p * s + (1 - p))^3 := by
  sorry



theorem theorem_893975_problem
  {D C : Type*} [Monoid D] [GroupWithZero C]
  (f : D → C)
  (h_mult : ∀ a b, f (a * b) = f a * f b)
  (h_nzero : ∃ a, f a ≠ 0) :
  f 1 = 1 := by
  sorry

theorem theorem_893674_problem (m n : ℤ) (x : ℝ)
  (hn : n > 1) (hx : Real.sin x ≠ 0) :
  HasDerivAt (fun y => - (Real.cos y ^ (m - 1)) / ((n - 1 : ℝ) * Real.sin y ^ (n - 1)))
    (Real.cos x ^ m / Real.sin x ^ n + ((m - 1 : ℝ) / (n - 1 : ℝ)) * (Real.cos x ^ (m - 2) / Real.sin x ^ (n - 2)))
    x := by
  sorry



