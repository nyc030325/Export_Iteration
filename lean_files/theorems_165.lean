import Mathlib
import Mathlib.Tactic



theorem theorem_899639_problem
  (G : Type*) [Group G]
  (H : Subgroup G) [H.Normal]
  (g : G)
  (h : orderOf (↑g : G ⧸ H) = 0) :
  orderOf g = 0 := by
  sorry



theorem theorem_898859_problem
  {R : Type*} [Ring R]
  {F : Type*} [AddCommGroup F] [Module R F]
  {I : Type*}
  (e : Basis I R F)
  (n : ℕ)
  (x : Fin n → F) :
  ∃ ν : F →ₗ[R] F, ∀ i, ν (x i) = x i := by
  sorry





theorem theorem_899310_problem (G : ℝ)
  (hG : G = ∑' n : ℕ, (-1 : ℝ) ^ n / ((2 * (n : ℝ) + 1) ^ 2)) :
  (∫ x in (0 : ℝ)..1, (Real.log (1 + x)) ^ 2 / (1 + x ^ 2)) -
  (∫ x in (0 : ℝ)..1, (Real.log (1 + x) * Real.log (1 + x ^ 2)) / (1 + x ^ 2)) =
  - (3 * Real.pi / 16) * (Real.log 2) ^ 2 + (G * Real.log 2) / 2 := by
  sorry



theorem theorem_900140_problem (n : ℕ) (x y : ℕ → ℝ)
  (h : ∀ i ∈ Finset.Icc 1 n, x i ≥ y i) :
  ∑ i in Finset.Icc 1 n, x i ≥ ∑ i in Finset.Icc 1 n, y i := by
  sorry







theorem theorem_900534_problem (s l p q : ℝ)
  (h1 : s ≠ l) (h2 : 2 * s ≠ l)
  (t : ℝ) (ht : t = (s - l) / (2 * s - l))
  (p' : ℝ) (hp' : p' = (1 - p) / t)
  (q' : ℝ) (hq' : q' = (1 - q) / t)
  (M : Matrix (Fin 2) (Fin 2) ℝ)
  (hM : M = !![s + t * p' + (1 - t) * q', p';
               q', s + t * q' + (1 - t) * p']) :
  M.det = (s + t * p' + (1 - t) * q') * (s + t * q' + (1 - t) * p') - p' * q' := by
  sorry

theorem theorem_900327_problem (x : ℝ) (h : x ≠ 0) :
  HasDerivAt (fun t => Real.log (abs t)) (1 / x) x := by
  sorry

theorem theorem_900514_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (R r : ℝ) (c1 c2 P : V)
  (hR : R > 0)
  (hr : r > 0)
  (h_center : dist c1 c2 = r)
  (h_on_C1 : dist P c1 = R)
  (h_on_C2 : dist P c2 = r) :
  inner (P - c1) (P - c2) ≠ (0 : ℝ) := by
  sorry













theorem theorem_901202_problem {P : Type*} [PartialOrder P]
  (h : ∀ (C : Set P), IsChain (· ≤ ·) C → ∃ u : P, ∀ z ∈ C, z ≤ u) :
  ∃ m : P, ∀ x : P, m ≤ x → m = x := by
  sorry

theorem theorem_901070_problem (p : ℕ → ℝ)
  (h_prob : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
  (h_lim : Filter.Tendsto p Filter.atTop (nhds 1)) :
  ∀ ε > 0, ∃ N, ∀ n ≥ N, p n > 1 - ε := by
  sorry

theorem theorem_901245_problem
  (f : ℝ × ℝ → ℝ)
  (R R' : Set (ℝ × ℝ))
  (h_map : R = polar_map '' R')
  (h_cont : ContinuousOn f R)
  (h_r : ∀ p ∈ R', 0 ≤ p.1) :
  ∫ p in R, f p = ∫ p in R', f (polar_map p) * p.1 := by
  sorry







theorem theorem_901672_problem
  (B' : Type*) [TopologicalSpace B']
  (K : Set ℝ)
  (hK : K = Set.Ioc 0 1 ∨ K = Set.univ)
  (d : B' × B' → ℝ)
  (hd : Continuous d)
  (p₀ : B')
  (d₀ : B' → ℝ)
  (hd₀_def : ∀ p, d₀ p = d (p, p₀))
  (hd₀_codom : ∀ p, d₀ p ∈ K)
  (t : ℝ)
  (B'_t : Set B')
  (hB'_t : B'_t = {p : B' | d₀ p ∈ Set.Iic t ∩ K}) :
  IsClosed B'_t := by
  sorry

theorem theorem_900973_problem (a x : ℝ) (h : a^2 > x^2) :
  HasDerivAt (fun x => (a^2 + x^2) / 2 * Real.sqrt ((a^2 - x^2) / (a^2 + x^2)) - 
    a^2 * Real.arctan (Real.sqrt ((a^2 - x^2) / (a^2 + x^2))))
    (x * Real.sqrt ((a^2 - x^2) / (a^2 + x^2))) x := by
  sorry







theorem theorem_902031_problem (n : ℕ) (y : ℕ → ℝ → ℝ)
  (h_diff : ∀ k, ContDiff ℝ 2 (y k))
  (h_eq : ∀ x, deriv (fun t => deriv (y n) t - t * y n t) x + x * (deriv (y n) x - x * y n x) = -2 * (n + 1 : ℝ) * y n x) :
  ∀ x, deriv (fun t => deriv (y n) t - t * y n t) x + x * (deriv (y n) x - x * y n x) = -2 * (n + 1 : ℝ) * y n x := by
  sorry





theorem theorem_901528_problem (a t : ℝ)
  (v1 v2 : ℝ × ℝ)
  (hv1 : v1 = (3, 1))
  (hv2 : v2 = (2, 1))
  (x : ℝ × ℝ)
  (hx : x = (a * Real.cos (2 * t)) • v1 - (a * Real.cos t) • v2)
  (u v : ℝ × ℝ)
  (hu : u = -(a * Real.cos (2 * t)) • v1 + (a * Real.cos t) • v2)
  (hv : v = -(2 * a * Real.cos (2 * t)) • v1 + (2 * a * Real.cos t) • v2) :
  u = x - 2 • x ∧ v = x - 3 • x := by
  sorry

theorem theorem_902084_problem
  (n : ℕ) (A B C D : EuclideanSpace ℝ (Fin n)) :
  FiniteDimensional.finrank ℝ (affineSpan ℝ ({A, B, C, D} : Set (EuclideanSpace ℝ (Fin n)))).direction ≤ 2 ↔
  Matrix.det !![0, 1, 1, 1, 1;
                1, 0, dist A B ^ 2, dist A C ^ 2, dist A D ^ 2;
                1, dist A B ^ 2, 0, dist B C ^ 2, dist B D ^ 2;
                1, dist A C ^ 2, dist B C ^ 2, 0, dist C D ^ 2;
                1, dist A D ^ 2, dist B D ^ 2, dist C D ^ 2, 0] = 0 := by
  sorry





theorem theorem_901944_problem (n : ℕ) (z : ℕ → ℂ) (ω : ℂ)
  (hn : n ≥ 3)
  (hω : ω = Complex.exp ((2 * Real.pi * Complex.I) / n))
  (hz : ∃ c w : ℂ, w ≠ 0 ∧ ∀ k ∈ Finset.Icc 1 n, z k = c + w * ω ^ (k - 1)) :
  ∑ k in Finset.Icc 1 n, z k * ω ^ k = 0 := by
  sorry









theorem theorem_902343_problem (x : ℝ) (hx : 0 < x) :
  HasDerivAt (fun t => (1 / Real.sqrt 2) * Real.arctan ((t - 1 / t) / Real.sqrt 2))
    ((1 + x^2) / (1 + x^4)) x := by
  sorry







theorem theorem_903225_problem (f : Polynomial ℤ) (n : ℕ) (p : ℕ)
  (hp : Nat.Prime p)
  (hn : f.natDegree = n)
  (h1 : ∀ i < n, (p : ℤ) ∣ f.coeff i)
  (h2 : ¬ (p : ℤ) ∣ f.coeff n)
  (h3 : ¬ ((p : ℤ) ^ 2) ∣ f.coeff 0) :
  Irreducible (f.map (Int.castRingHom ℚ)) := by
  sorry

theorem theorem_903272_problem : Irrational (Real.exp 1) := by
  sorry





theorem theorem_903101_problem (x : ℕ → ℝ × ℝ)
  (h_even : ∀ n, x (2 * n) = (1, 0))
  (h_odd : ∀ n, x (2 * n + 1) = (0, 1)) :
  {a | MapClusterPt a atTop x} = {(1, 0), (0, 1)} := by
  sorry

theorem theorem_902785_problem
  (n m : ℕ)
  (d : Fin n → ℝ)
  (F : Matrix (Fin m) (Fin n) ℝ)
  (B : Fin m → ℝ)
  (t : Fin n → ℝ) :
  -- The component-wise optimization problem described in the text
  ((∀ j : Fin m, ∑ i : Fin n, F j i * t i ≤ B j) ∧
   (∀ i : Fin n, 0 ≤ t i) ∧
   (∀ t' : Fin n → ℝ,
     (∀ j : Fin m, ∑ i : Fin n, F j i * t' i ≤ B j) →
     (∀ i : Fin n, 0 ≤ t' i) →
     ∑ i : Fin n, d i * t' i ≤ ∑ i : Fin n, d i * t i)) ↔
  -- Is equivalent to the Linear Programming matrix formulation
  (F.mulVec t ≤ B ∧
   0 ≤ t ∧
   ∀ t' : Fin n → ℝ,
     F.mulVec t' ≤ B →
     0 ≤ t' →
     Matrix.dotProduct d t' ≤ Matrix.dotProduct d t) := by
  sorry







theorem theorem_902960_problem : Function.Bijective f := by
  sorry



theorem theorem_902799_problem
  (G : Type*) [Group G] [Fintype G] [IsSimpleGroup G]
  (p : ℕ) (hp : Nat.Prime p) (h_mersenne : Nat.Prime (2^p - 1)) :
  Fintype.card G ≠ 2^(p - 1) * (2^p - 1) := by
  sorry

theorem theorem_903501_problem
  {K : Type*} [Field K]
  {U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {κ : Type*} [Fintype κ] [DecidableEq κ]
  (T : U →ₗ[K] V)
  (B : Basis ι K U)
  (C : Basis κ K V) :
  Matrix.rank (LinearMap.toMatrix B C T) = FiniteDimensional.finrank K (LinearMap.range T) := by
  sorry

theorem theorem_903666_problem (n : ℕ) (M : Type*) [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
  ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
  ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧
  Nonempty (U ≃ₜ V) := by
  sorry

theorem theorem_903167_problem
  {X : Type*} [TopologicalSpace X]
  {x₀ x₁ : X}
  (α γ : Path x₀ x₁)
  (h : Path.Homotopic α γ) :
  Path.Homotopic (α.trans γ.symm) (Path.refl x₀) := by
  sorry









theorem theorem_904154_problem (f : ℕ → ℕ)
  (h : ∀ x, f (f x) + f x = 2 * x + 15) :
  ∀ x, f x = x + 5 := by
  sorry

theorem theorem_904342_problem
  (a b c d e k : ℝ)
  (ha : a ≠ 0)
  (he_pos : e > 0)
  (he_sq : e = k^2)
  (f : ℝ → ℝ)
  (hf : ∀ x, f x = a * x^4 + b * x^3 + c * x^2 + d * x + e) :
  ∃ t : ℝ, (fun u ↦ f (u + t)) 0 = k^2 := by
  sorry





theorem theorem_904491_problem
  (theta : ℝ → ℝ)
  (omega0 : ℝ)
  (h_diff : ContDiff ℝ 2 theta)
  (h_eqn : ∀ t, deriv (deriv theta) t + omega0 ^ 2 * Real.sin (theta t) = 0) :
  ∃ K : ℝ, ∀ t, (1 / 2 : ℝ) * (deriv theta t) ^ 2 - omega0 ^ 2 * Real.cos (theta t) = K := by
  sorry





theorem theorem_904481_problem (a b : EuclideanSpace ℝ (Fin 3)) :
  ‖crossProduct a b‖ ^ 2 + (inner a b) ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  sorry

theorem theorem_904271_problem
  (τ : ℂ) (hτ : 0 < τ.im)
  (L : Set ℂ) (hL : L = {z | ∃ m n : ℤ, z = ↑m * τ + ↑n})
  (f : ℂ ≃ ℂ)
  (h_sub : f '' L ⊆ L) :
  ∀ z ∈ L, f z ∈ L := by
  sorry

theorem theorem_904042_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (g : Matrix n n ℝ)
  (v : Matrix n n ℝ)
  (f_cov : n → ℝ)
  (hg_symm : g.IsSymm)
  (hv_symm : v.IsSymm)
  (hg_inv : Invertible g) :
  let g_inv := ⅟g
  let v_raised : Matrix n n ℝ := λ i j => ∑ p, ∑ q, g_inv i p * g_inv j q * v p q
  let f_contra : n → ℝ := λ i => ∑ k, g_inv i k * f_cov k
  ∑ i, ∑ j, v_raised i j * f_cov i * f_cov j =
  ∑ i, ∑ j, v i j * f_contra i * f_contra j := by
  sorry

theorem theorem_904438_problem :
  ∃ (n : ℕ) (P₁ P₂ : Matrix (Fin n) (Fin n) ℝ),
    (P₁ * P₁ = P₁) ∧ (P₁.transpose = P₁) ∧
    (P₂ * P₂ = P₂) ∧ (P₂.transpose = P₂) ∧
    (P₁ ≠ P₂) ∧
    (P₁ * P₂ ≠ P₂ * P₁) := by
  sorry

theorem theorem_904657_problem
  (D : Type*)
  (Loves : D → D → Prop)
  (Knows : D → Prop → Prop)
  (KnowsLove : D → D → D → Prop)
  (h_def : ∀ (x y z : D), KnowsLove x y z ↔ Knows x (Loves y z))
  (h_factivity : ∀ (x : D) (p : Prop), Knows x p → p) :
  ∀ (a b c : D), KnowsLove a b c → Loves b c := by
  sorry

theorem theorem_904695_problem 
  (V : Type*) 
  [Membership V V] 
  (theta : V → Prop) :
  (∀ A : V, ∃ B : V, (∀ x : V, x ∈ B → x ∈ A) ∧ (∀ x : V, x ∈ B ↔ (x ∈ A ∧ theta x))) ↔ 
  (∀ A : V, ∃ B : V, ∀ x : V, x ∈ B ↔ (x ∈ A ∧ theta x)) := by
  sorry



theorem theorem_904718_problem (R θ : ℝ) (z : ℂ)
  (hR : 0 < R)
  (hR_neq : R ≠ 1)
  (hθ : 0 ≤ θ ∧ θ ≤ Real.pi)
  (hz : z = R * Complex.exp (Complex.I * θ)) :
  Complex.abs (1 / (1 + z ^ 2)) ≤ 1 / |R ^ 2 - 1| := by
  sorry

theorem theorem_904648_problem (F E L : Type*) [Field F] [Field E] [Field L]
  [Algebra F E] (h_alg : Algebra.IsAlgebraic F E)
  [IsAlgClosed L] (σ : F →+* L) :
  ∃ σ' : E →+* L, ∀ x : F, σ' (algebraMap F E x) = σ x := by
  sorry





theorem theorem_904772_problem (c : GaussianInt) (m n : ℤ)
  (h_norm : c.norm = m * n)
  (h_m_gt : m > 1)
  (h_n_gt : n > 1)
  (h_m_sum : ∃ x1 y1 : ℤ, m = x1^2 + y1^2)
  (h_n_sum : ∃ x2 y2 : ℤ, n = x2^2 + y2^2) :
  ¬ Prime c := by
  sorry





theorem theorem_905275_problem (n d : ℕ) (p : Fin (n + 1) → (Fin d → ℝ))
  (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
  (∑ k : Fin (n + 1), ((n.choose k : ℝ) * t ^ (k : ℕ) * (1 - t) ^ (n - (k : ℕ))) • p k) ∈
    convexHull ℝ (Set.range p) := by
  sorry

theorem theorem_905158_problem (u : ℝ) (h : 0 ≤ u) :
  (1 + u) ^ (3 / 2 : ℝ) ≤ 1 + 3 / 2 * u + 3 / 8 * u ^ 2 + 2 / 3 := by
  sorry







theorem theorem_905278_problem
  (p m : ℤ)
  (q : ℤ) (hq : q = (Int.gcd p m : ℤ))
  (hq_gt_1 : q > 1)
  (q_1 q_2 q_3 : ℤ) (hq_factor : q = q_1 * q_2 * q_3)
  (r_1 r_2 : ℤ)
  (hr1 : Int.gcd r_1 (m / q) = 1)
  (hr2 : Int.gcd r_2 (m / q) = 1)
  (r_3 : ℤ)
  (hr3 : r_3 * (r_1 * r_2) ≡ (p / q) [ZMOD (m / q)])
  (a : ℤ) (ha : a = q_1 * r_1)
  (b : ℤ) (hb : b = q_2 * r_2)
  (c : ℤ) (hc : c = q_3 * r_3) :
  a * b * c ≡ p [ZMOD m] := by
  sorry





theorem theorem_906062_problem
  (n : ℕ)
  (g : (Fin n → ℝ) × Set.Icc (0 : ℝ) 1 → (Fin n → ℝ))
  (hg_cont : Continuous g)
  (x₀ : Fin n → ℝ)
  (hx₀ : g (x₀, ⟨0, by norm_num⟩) = 0)
  (hg_bdd : Bornology.IsBounded (Set.range g))
  (H : (Fin n → ℝ) × Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 → (Fin n → ℝ))
  (hH_def : ∀ (x : Fin n → ℝ) (t : Set.Icc (0 : ℝ) 1) (s : Set.Icc (0 : ℝ) 1),
    H (x, t, s) = (1 - (s : ℝ)) • g (x, ⟨0, by norm_num⟩) + (s : ℝ) • g (x, t))
  (hH_proper : IsProperMap H) :
  ∃ x₁ : Fin n → ℝ, g (x₁, ⟨1, by norm_num⟩) = 0 := by
  sorry







