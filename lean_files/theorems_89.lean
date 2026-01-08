import Mathlib
import Mathlib.Tactic

theorem theorem_477997_problem (n : ℕ) (x y : Fin n → ℝ) (p q : ℝ)
  (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
  (hx : ∑ i, |x i| ^ p ≠ 0) (hy : ∑ i, |y i| ^ q ≠ 0) :
  (∑ i, (1 / p) * (|x i| ^ p / (∑ j, |x j| ^ p))) +
  (∑ i, (1 / q) * (|y i| ^ q / (∑ j, |y j| ^ q))) ≤ 1 / p + 1 / q := by
  sorry

theorem theorem_478302_problem (r x : ℝ) (hr : 0 < r) (z : ℂ)
  (hz : z = (r : ℂ) * Complex.exp ((x : ℂ) * Complex.I)) :
  ∃! β : ℂ, Complex.abs β = 1 ∧ β * z = (r : ℂ) := by
  sorry





theorem theorem_478480_problem
  (F : Type*) [Field F]
  (nrm nrm_inf : F → ℝ)
  (β : ℝ) (hβ : 0 < β)
  (h_nrm_nonneg : ∀ x, 0 ≤ nrm x)
  (h_nrm_inf_nonneg : ∀ x, 0 ≤ nrm_inf x)
  (h_nrm_zero : nrm 0 = 0)
  (h_nrm_inf_zero : nrm_inf 0 = 0)
  (h_rel : ∀ x : F, x ≠ 0 → nrm x = (nrm_inf x) ^ β) :
  ∀ x : ℕ → F,
    (∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m → nrm (x n - x m) < ε) ↔
    (∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m → nrm_inf (x n - x m) < ε) := by
  sorry

theorem theorem_478599_problem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (T : V →ₗ[K] V)
  (h1 : LinearMap.ker T ≤ LinearMap.range T)
  (h2 : LinearMap.range T ≤ LinearMap.ker T) :
  T ^ 2 = 0 := by
  sorry

theorem theorem_478358_problem (r_x1y r_x2y r_x1x2 beta_x1 beta_x2 : ℝ)
  (h1 : beta_x1 + r_x1x2 * beta_x2 = r_x1y)
  (h2 : r_x1x2 * beta_x1 + beta_x2 = r_x2y)
  (h3 : 1 - r_x1x2 ^ 2 ≠ 0) :
  beta_x1 = (r_x1y - r_x2y * r_x1x2) / (1 - r_x1x2 ^ 2) := by
  sorry

theorem theorem_478771_problem
  (X : Type*) [TopologicalSpace X]
  (h_closed : ∀ (s : Set X), IsClosed s ↔ s.Finite ∨ s = Set.univ)
  (A : Set X) (h_inf : A.Infinite) :
  closure A = Set.univ := by
  sorry



theorem theorem_478183_problem 
  (m₁ m₂ g ρ₀ : ℝ)
  (ρ₁ ρ₂ θ : ℝ → ℝ)
  (h_diff_ρ₁ : ContDiff ℝ 2 ρ₁)
  (h_diff_ρ₂ : ContDiff ℝ 2 ρ₂)
  (h_diff_θ : ContDiff ℝ 2 θ)
  (h_constraint : ∀ t, ρ₁ t + ρ₂ t = ρ₀)
  (T₁ : ℝ → ℝ := fun t ↦ (1/2) * m₁ * (deriv ρ₁ t)^2)
  (U₁ : ℝ → ℝ := fun t ↦ -ρ₁ t * m₁ * g)
  (T₂ : ℝ → ℝ := fun t ↦ (1/2) * m₂ * ((deriv ρ₂ t)^2 + (ρ₂ t)^2 * (deriv θ t)^2))
  (U₂ : ℝ → ℝ := fun t ↦ 0)
  (E : ℝ → ℝ := fun t ↦ T₁ t + U₁ t + T₂ t + U₂ t)
  -- The following hypotheses represent the condition that "conservation of energy principle holds provided no external forces act"
  -- (i.e., the system follows the Euler-Lagrange equations derived from L = T - U).
  (h_eom_ρ2 : ∀ t, (m₁ + m₂) * deriv (deriv ρ₂) t - m₂ * (ρ₂ t) * (deriv θ t)^2 + m₁ * g = 0)
  (h_eom_θ : ∀ t, deriv (fun t ↦ m₂ * (ρ₂ t)^2 * (deriv θ t)) t = 0) :
  ∀ t, deriv E t = 0 := by
  sorry

theorem theorem_478854_problem
  (n : ℕ)
  {K : Type*} [Field K]
  (A : Matrix (Fin n) (Fin n) K)
  (T : Matrix (Fin n) (Fin n) K →ₗ[K] Matrix (Fin n) (Fin n) K)
  (hT : ∀ X, T X = A * X - X * A) :
  (LinearMap.ker T : Set (Matrix (Fin n) (Fin n) K)) = { X | A * X = X * A } := by
  sorry

theorem theorem_478624_problem (f : ℝ → ℝ)
  (h_add : ∀ x y : ℝ, f (x + y) = f x + f y)
  (h_cont : Continuous f) :
  ∃ c : ℝ, ∀ x : ℝ, f x = c * x := by
  sorry



theorem theorem_479022_problem (y : ℝ → ℝ)
  (h_diff : DifferentiableOn ℝ y (Set.Ici 0))
  (h_ode : ∀ t, 0 ≤ t → deriv y t = (3 * t) / (1 + 2 * Real.exp (y t))) :
  Filter.Tendsto y Filter.atTop Filter.atTop := by
  sorry





theorem theorem_478707_problem (P Q : Polynomial ℂ)
  (hQ : Q ≠ 0) (hCoprime : IsCoprime P Q) :
  ∃! (data : Polynomial ℂ × (ℂ → ℕ → ℂ)),
    let h := data.1
    let c := data.2
    (∀ r k, c r k ≠ 0 → r ∈ Q.roots ∧ 1 ≤ k ∧ k ≤ Q.rootMultiplicity r) ∧
    (P : RatFunc ℂ) / (Q : RatFunc ℂ) =
      (h : RatFunc ℂ) +
      ∑ r in Q.roots.toFinset,
        ∑ k in Finset.Icc 1 (Q.rootMultiplicity r),
          ((Polynomial.C (c r k)) : RatFunc ℂ) / ((X - (Polynomial.C r : RatFunc ℂ)) ^ k) := by
  sorry

theorem theorem_478613_problem (U : Type*) [MetricSpace U]
  (h_nontriv : ∃ x y : U, x ≠ y)
  (beta : U → U → ℝ)
  (gamma : U → U)
  (h_beta : ∀ z w, beta z w = Real.sqrt (dist z w))
  (h_gamma : ∀ x, gamma x = x) :
  ∃ x : ℕ → U, Filter.Tendsto (fun n => ∑ i in Finset.range n, beta (gamma (x (i + 1))) (gamma (x i))) Filter.atTop Filter.atTop := by
  sorry





theorem theorem_479404_problem
  (a b ε : ℝ)
  (ha : 0 < a)
  (hb : a < b)
  (hε_pos : 0 < ε)
  (hε_small : ε < a^5) :
  ∫ x in a..b, 1 / (x^5 + ε) =
  ∑' k : ℕ, (-1 : ℝ)^k * ε^k * ∫ x in a..b, 1 / x^(5 * (k + 1)) := by
  sorry



theorem theorem_479531_problem
  (A : Set (Set.Icc (0 : ℝ) 1 → ℝ))
  (hA : A = { f | StrictMono f }) :
  ¬ IsClosed A := by
  sorry

theorem theorem_478585_problem
  (n : ℕ)
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (hB : B.PosDef)
  (h : ∀ (α β : ℝ),
    let S := α • (A * B + B * A.transpose) + β • B
    Matrix.trace (A.transpose * S) = 0) :
  A.transpose = -A := by
  sorry



theorem theorem_479865_problem
  (div_a : ℝ → ℝ → ℝ → ℝ)
  (T : Set (ℝ × ℝ × ℝ))
  (h1 : ∀ x y z, div_a x y z = x + y + z)
  (h2 : T = { p : ℝ × ℝ × ℝ | ∃ ρ φ z,
    0 ≤ ρ ∧ ρ ≤ 1 ∧
    0 ≤ φ ∧ φ ≤ 2 * Real.pi ∧
    0 ≤ z ∧ z ≤ Real.sqrt 2 ∧
    p.1 = ρ * Real.cos φ ∧
    p.2.1 = ρ * Real.sin φ ∧
    p.2.2 = z }) :
  ∫ p in T, div_a p.1 p.2.1 p.2.2 =
  ∫ φ in (0)..(2 * Real.pi),
    ∫ ρ in (0)..(1),
      ∫ z in (0)..(Real.sqrt 2),
        (ρ * Real.cos φ + ρ * Real.sin φ + z) * ρ := by
  sorry

theorem theorem_479973_problem (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  Summable (fun n : ℕ => a ^ (1 / (n : ℝ)) - (b ^ (1 / (n : ℝ)) + c ^ (1 / (n : ℝ))) / 2) ↔ a ^ 2 = b * c := by
  sorry



theorem theorem_480230_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (m n : ℕ)
  (a : Fin m → V)
  (q : Fin n → V)
  (c : Fin n → Fin m → F)
  (hq : ∀ j, q j = ∑ i, c j i • a i)
  (d : Fin n → F)
  (v : V)
  (hv : v = ∑ j, d j • q j) :
  v = ∑ i, (∑ j, d j * c j i) • a i := by
  sorry















theorem theorem_480276_problem (z z' s : ℝ) (h : 0 < s) :
  -Real.log (z - z' + Real.sqrt ((z - z')^2 + s^2)) =
  Real.log (Real.sqrt ((z - z')^2 + s^2) + z' - z) - Real.log (s^2) := by
  sorry

theorem theorem_480661_problem (N : ℕ) (hN : 0 < N) :
  ∑ x in (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun x ↦ x.1 ≠ x.2), (x.1 * x.2 : ℚ) =
  ((N * (N + 1) : ℚ) / 2) ^ 2 - (N * (N + 1) * (2 * N + 1) : ℚ) / 6 := by
  sorry







theorem theorem_480714_problem (p q : ℤ) (h : Int.gcd p q = 1) (n : ℤ) :
  ∃ a b : ℤ, n = a * p + b * q := by
  sorry

theorem theorem_480303_problem (theta_1 theta_2 : ℝ → ℝ)
  (h1 : ∀ t, deriv theta_2 t = 2 * Real.pi + Real.sin (theta_1 t - theta_2 t))
  (h2 : ∀ t, deriv theta_1 t = 2 * Real.pi + Real.sin (theta_2 t - theta_1 t)) :
  ∀ t, deriv theta_2 t - deriv theta_1 t = -2 * Real.sin (theta_2 t - theta_1 t) := by
  sorry

theorem theorem_480343_problem (g : ℂ → ℂ → ℂ)
  (hg : Continuous (fun p : ℂ × ℂ ↦ g p.1 p.2)) :
  ∫ (θ : ℝ) in (0)..2 * Real.pi, g (Complex.cos ↑θ) (Complex.sin ↑θ) =
  circleIntegral (fun z ↦ g ((z + z⁻¹) / 2) ((z - z⁻¹) / (2 * Complex.I)) / (Complex.I * z)) 0 1 := by
  sorry



theorem theorem_480841_problem (n m r : ℕ) :
  ∑ k in Finset.Icc n (n + m), Nat.choose k r = Nat.choose (n + m + 1) (r + 1) - Nat.choose n (r + 1) := by
  sorry

theorem theorem_480700_problem
  (f : ℂ → ℂ) (U : Set ℂ) (a : ℂ) (n : ℕ)
  (hU : IsOpen U) (ha : a ∈ U)
  (hf : DifferentiableOn ℂ f U)
  (hn : (∀ k < n, iteratedDeriv k f a = 0) ∧ iteratedDeriv n f a ≠ 0) :
  ∃ R > 0, Metric.ball a R ⊆ U ∧
    ∀ r, 0 < r → r < R →
    (2 * Real.pi * I)⁻¹ * circleIntegral (fun z ↦ deriv f z / f z) a r = n := by
  sorry









theorem theorem_481178_problem (z : ℂ) (h : z^2 = Complex.I) :
  z = (1 + Complex.I) / (Real.sqrt 2 : ℂ) ∨ 
  z = -((1 + Complex.I) / (Real.sqrt 2 : ℂ)) := by
  sorry

theorem theorem_480873_problem (a b c : ℤ) (p : ℕ) (hp : p.Prime)
  (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
  padicValNat p (Int.gcd a c * Int.gcd b c) =
  min (padicValNat p a.natAbs + padicValNat p b.natAbs)
    (min (padicValNat p a.natAbs + padicValNat p c.natAbs)
      (min (padicValNat p b.natAbs + padicValNat p c.natAbs)
        (2 * padicValNat p c.natAbs))) := by
  sorry



theorem theorem_480485_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (A B : Matrix n n ℂ)
  (p : ℕ)
  (hA : A.IsHermitian)
  (hB : B.IsHermitian)
  (hp : p > 0) :
  Complex.abs (Matrix.trace ((A * B) ^ (2 * p))) ≤
  Complex.abs (Matrix.trace (A ^ (2 * p))) * Complex.abs (Matrix.trace (B ^ (2 * p))) := by
  sorry





theorem theorem_481454_problem (m : ℤ) (n : ℕ) (hm : m > 0) :
  Int.gcd (((m + 1) ^ n - 1) / m) m = Int.gcd (n : ℤ) m := by
  sorry







theorem theorem_482118_problem
  {X Y : Type*}
  (S : Finset (X × Y))
  (f : X × Y → ℝ) :
  ∃ C : ℝ, C > 0 ∧ ∀ x y, (x, y) ∈ S → f (x, y) ≤ C := by
  sorry

theorem theorem_481574_problem
  (T : ℕ → ℤ)
  (hT0 : T 0 = 0)
  (hT1 : T 1 = 1)
  (hT2 : T 2 = 1)
  (hTn : ∀ n, T (n + 3) = T (n + 2) + T (n + 1) + T n)
  (a_plus a_minus b : ℝ)
  (ha_plus : a_plus = (19 + 3 * Real.sqrt 33) ^ (1 / 3 : ℝ))
  (ha_minus : a_minus = (19 - 3 * Real.sqrt 33) ^ (1 / 3 : ℝ))
  (hb : b = (586 + 102 * Real.sqrt 33) ^ (1 / 3 : ℝ)) :
  ∀ n : ℕ, T n = ⌊3 * b / (b ^ 2 - 2 * b + 4) * ((a_plus + a_minus + 1) / 3) ^ n + 1 / 2⌋ := by
  sorry







theorem theorem_481957_problem (g : ℝ → ℝ) (a b L : ℝ)
  (h_ab : a < b)
  (h_L : L > 0)
  (h_lip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |g x - g y| ≤ L * |x - y|)
  (h_cond : |g b - g a| = L * (b - a)) :
  ∀ x ∈ Set.Icc a b, g x = g a + (g b - g a) / (b - a) * (x - a) := by
  sorry

theorem theorem_482561_problem {G : Type*} [CommGroup G] [Group.FG G] (H : Subgroup G)
  (h : ∃ S : Set G, S.Finite ∧ Subgroup.closure S = H ∧ ∀ x ∈ S, IsOfFinOrder x) :
  Finite H := by
  sorry

theorem theorem_482614_problem
  (D : Set ℂ)
  (h_open : IsOpen D)
  (h_conn : IsConnected D)
  (h_nonempty : D.Nonempty)
  (h_zero : 0 ∈ D) :
  let z : C(D, ℂ) := ⟨fun w ↦ (w : ℂ), continuous_subtype_val⟩
  let z_bar : C(D, ℂ) := ⟨fun w ↦ star (w : ℂ), continuous_star.comp continuous_subtype_val⟩
  let I : Set C(D, ℂ) := {g | ∃ f : C(D, ℂ), g = f * z}
  z_bar ∉ I := by
  sorry

theorem theorem_482603_problem
  (n : ℕ)
  (F : (Fin n → ℝ) → (Fin n → ℝ))
  (c : ℝ → ℝ)
  (x : ℝ → (Fin n → ℝ))
  (u : ℝ → ℝ)
  (y : ℝ → (Fin n → ℝ))
  (I : Set ℝ)
  (hI : IsOpen I)
  (hc_pos : ∀ t ∈ I, 0 < c t)
  (hu_deriv : ∀ t ∈ I, deriv u t = c t)
  (hx_sol : ∀ t ∈ I, deriv x t = c t • F (x t))
  (hy_def : ∀ t ∈ I, y (u t) = x t)
  (hu_diff : DifferentiableOn ℝ u I)
  (hx_diff : DifferentiableOn ℝ x I)
  (hy_diff : DifferentiableOn ℝ y (u '' I)) :
  ∀ s ∈ u '' I, deriv y s = F (y s) := by
  sorry

theorem theorem_481865_problem
  (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
  (h_proj : Module.Projective A (Derivation k A A)) :
  ∀ (D₁ D₂ : Derivation k A A) (a : A),
    ⁅D₁, a • D₂⁆ = a • ⁅D₁, D₂⁆ + (D₁ a) • D₂ := by
  sorry

theorem theorem_482720_problem (f : ℝ → ℝ → ℝ) (x y : ℝ → ℝ)
  (hf : ∀ a b, f a b = a^2 - b)
  (hx : ∀ t, x t = t)
  (hy : ∀ t, y t = t^2) :
  ∫ t in (0)..2, f (x t) (y t) * Real.sqrt ((deriv x t)^2 + (deriv y t)^2) = 0 := by
  sorry









theorem theorem_482450_problem
  (X : Type*) [TopologicalSpace X] [T1Space X]
  (Y : Set X) (hY : Y.Nonempty) :
  T1Space Y := by
  sorry



theorem theorem_482420_problem
  {F : Type*} [Field F]
  {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (e : Basis ι F V)
  (f : Basis κ F W)
  (B : V →ₗ[F] W →ₗ[F] F) :
  ∃! g : ι → κ → F, ∀ (v : V) (w : W),
    B v w = ∑ i, ∑ j, g i j * (e.coord i v) * (f.coord j w) := by
  sorry



theorem theorem_482691_problem (f : ℝ × ℝ → ℝ) (h_cont : Continuous f) :
  ¬ Function.Injective f := by
  sorry





theorem theorem_482788_problem
  {A B C : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  (hA : AddMonoid.IsTorsionFree A)
  (hB : AddMonoid.IsTorsionFree B)
  (f : A →+ B)
  (h_coker_torsion : AddMonoid.IsTorsion (B ⧸ AddMonoidHom.range f))
  (h_coker_nontrivial : Nontrivial (B ⧸ AddMonoidHom.range f))
  (hC : AddMonoid.IsTorsionFree C)
  (g : B →+ C)
  (h_comp : g.comp f = 0) :
  g = 0 := by
  sorry





theorem theorem_483304_problem
  (x : PNat → ℝ)
  (h_finite : Set.Finite {n | x n ≠ 0}) :
  let A : (PNat → ℝ) → (PNat → ℝ) := fun y n ↦ (n : ℝ) * y n
  let norm1 : (PNat → ℝ) → ℝ := fun y ↦ ∑' n, |y n|
  norm1 (A x) ≥ norm1 x := by
  sorry





theorem theorem_482203_problem
  (n : ℕ)
  (d r : Fin n → ℝ)
  (s₀ s₁ : ℝ)
  (h_denom : ∀ i, s₁ * d i + s₀ ≠ 0)
  (S₁ : ℝ := ∑ i, 1 / (s₁ * d i + s₀))
  (S₂ : ℝ := ∑ i, d i / (s₁ * d i + s₀))
  (S₃ : ℝ := ∑ i, (d i)^2 / (s₁ * d i + s₀))
  (T₁ : ℝ := ∑ i, r i / (s₁ * d i + s₀))
  (T₂ : ℝ := ∑ i, (d i * r i) / (s₁ * d i + s₀))
  (J : ℝ → ℝ → ℝ := fun m₀ m₁ => ∑ i, (r i - m₀ - m₁ * d i)^2 / (s₁ * d i + s₀))
  (m₀_hat : ℝ := (S₂ * T₂ - T₁ * S₃) / (S₂^2 - S₁ * S₃))
  (m₁_hat : ℝ := (T₁ * S₂ - S₁ * T₂) / (S₂^2 - S₁ * S₃))
  (h_det : S₂^2 - S₁ * S₃ ≠ 0) :
  ∀ m₀ m₁ : ℝ, J m₀_hat m₁_hat ≤ J m₀ m₁ := by
  sorry

theorem theorem_482883_problem {K : Type*} [Field K] {n : ℕ}
  (A : Matrix (Fin n) (Fin n) K)
  (h : ∀ D : Matrix (Fin n) (Fin n) K, A * D = D * A) :
  ∃ a : K, A = a • (1 : Matrix (Fin n) (Fin n) K) := by
  sorry

theorem theorem_482926_problem (a : ℂ) (h : a.re > 0) :
  ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) * Complex.exp (-a * t) = 1 / a ^ 2 := by
  sorry



theorem theorem_483217_problem (z : ℂ) (c : ℕ → ℂ)
  (h_nz : z ≠ 0)
  (ω : ℂ) (hω : ω = Complex.exp (2 * ↑Real.pi * Complex.I / 3))
  (f : ℂ → ℂ) (hf : ∀ w, f w = w * Complex.cot (↑Real.pi * w))
  (S : ℂ → ℂ) (hS : ∀ w, S w = (↑Real.pi / w ^ 3) * (f w + f (ω * w) + f (ω ^ 2 * w)) / 3)
  (h_series : ∀ w, w ∈ ({z, ω * z, ω ^ 2 * z} : Set ℂ) → HasSum (fun k => c k * w ^ k) (f w)) :
  HasSum (fun k => c (3 * k) * z ^ (3 * k)) (z ^ 3 / ↑Real.pi * S z) := by
  sorry

theorem theorem_482993_problem :
  Cardinal.mk ℝ = Cardinal.mk (ℕ → Fin 2) := by
  sorry





theorem theorem_483518_problem (X : Type*) [MetricSpace X] (x y z : X) :
  dist x z ≤ max (dist x y) (dist y z) := by
  sorry

theorem theorem_483530_problem
  (n : ℕ)
  {R : Type*} [CommRing R]
  (A : Matrix (Fin n) (Fin n) R) :
  A.det = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * ∏ i : Fin n, A i (σ i) := by
  sorry

theorem theorem_483775_problem
  (a b : ℝ)
  (f : ℝ → ℝ)
  (lam : ℝ → ℝ)
  (hf : DifferentiableOn ℝ f (Set.Icc a b))
  (hlam : Differentiable ℝ lam)
  (h_deriv : ∀ x ∈ Set.Icc a b, deriv (lam ∘ f) x = 0) :
  ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, (lam ∘ f) x = (lam ∘ f) y := by
  sorry

