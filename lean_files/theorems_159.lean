import Mathlib
import Mathlib.Tactic







theorem theorem_864047_problem 
  (k : Type*) [Field k] [IsAlgClosed k]
  (Variety : Type*) 
  (Hypersurface : Variety → Prop)
  (Birational : Variety → Variety → Prop)
  (SingularSet : Variety → Variety)
  (Proper : Variety → Prop)
  (X Y : Variety)
  (h_hyp : Hypersurface Y)
  (h_birat : Birational X Y)
  (h_singY_proper : Proper (SingularSet Y)) :
  Proper (SingularSet X) := by
  sorry

theorem theorem_865177_problem {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]
  (P : Matrix n n K) (h_proj : P ^ 2 = P) (h_neq_I : P ≠ 1) :
  ¬ IsUnit P := by
  sorry

theorem theorem_864986_problem (a b : ℕ → ℝ) (A B : ℝ)
  (h1 : Filter.Tendsto a Filter.atTop (nhds A))
  (h2 : A ≠ 0)
  (h3 : Filter.Tendsto (fun n => a n * b n) Filter.atTop (nhds (A * B))) :
  Filter.Tendsto b Filter.atTop (nhds B) := by
  sorry

theorem theorem_864776_problem
  {R : Type*} [CommRing R]
  (p : ℕ)
  (n : Fin p → ℕ)
  (a : (i : Fin p) → Fin (n i) → R)
  (N : ℕ)
  (hN : N = ∏ i, n i)
  (idx : ((i : Fin p) → Fin (n i)) ≃ Fin N)
  (vec_outer : Fin N → R)
  (kron_rev : Fin N → R)
  (h1 : ∀ (f : (i : Fin p) → Fin (n i)),
    vec_outer (idx f) = (List.ofFn (fun i => a i (f i))).prod)
  (h2 : ∀ (f : (i : Fin p) → Fin (n i)),
    kron_rev (idx f) = (List.ofFn (fun i => a i (f i))).reverse.prod) :
  vec_outer = kron_rev := by
  sorry



theorem theorem_865544_problem {P : Type*} [HeytingAlgebra P] :
  (∀ A : P, A = ((A ⇨ ⊥) ⇨ ⊥)) ↔ (∀ A : P, ((A ⇨ ⊥) ⇨ ⊥) ≤ A) := by
  sorry



theorem theorem_864886_problem (x y : ℝ) (z : ℂ)
  (hz : z = (x : ℂ) + (y : ℂ) * Complex.I)
  (h : Complex.cos z = Real.sqrt 2) :
  ∃ n : ℤ, z = 2 * (n : ℂ) * Real.pi + Complex.I * Real.log (Real.sqrt 2 + 1) ∨
           z = 2 * (n : ℂ) * Real.pi - Complex.I * Real.log (Real.sqrt 2 + 1) := by
  sorry











theorem theorem_865714_problem
  (n m p : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (B : Matrix (Fin n) (Fin m) ℝ)
  (C : Matrix (Fin p) (Fin n) ℝ)
  (D : Matrix (Fin p) (Fin m) ℝ)
  (s : ℂ)
  (X : Matrix (Fin n) Unit ℂ)
  (U : Matrix (Fin m) Unit ℂ)
  (Y : Matrix (Fin p) Unit ℂ)
  (h_inv : IsUnit (s • (1 : Matrix (Fin n) (Fin n) ℂ) - A.map (algebraMap ℝ ℂ)))
  (h_state : s • X = (A.map (algebraMap ℝ ℂ)) * X + (B.map (algebraMap ℝ ℂ)) * U)
  (h_output : Y = (C.map (algebraMap ℝ ℂ)) * X + (D.map (algebraMap ℝ ℂ)) * U) :
  Y = ((C.map (algebraMap ℝ ℂ)) * (s • (1 : Matrix (Fin n) (Fin n) ℂ) - A.map (algebraMap ℝ ℂ))⁻¹ * (B.map (algebraMap ℝ ℂ)) + (D.map (algebraMap ℝ ℂ))) * U := by
  sorry



theorem theorem_866022_problem {K : Type*} [Field K] (P_i : Polynomial K) 
  (h_ne_zero : P_i ≠ 0) (h_irred : Irreducible P_i) : 
  IsField (Polynomial K ⧸ Ideal.span {P_i}) := by
  sorry









theorem theorem_866115_problem (x₁ y₁ x₂ y₂ x₃ y₃ S x y : ℝ) (hS : 0 < S) :
  Complex.abs (Complex.mk x y - Complex.mk x₁ y₁) +
  Complex.abs (Complex.mk x y - Complex.mk x₂ y₂) +
  Complex.abs (Complex.mk x y - Complex.mk x₃ y₃) = S ↔
  Real.sqrt ((x - x₁) ^ 2 + (y - y₁) ^ 2) +
  Real.sqrt ((x - x₂) ^ 2 + (y - y₂) ^ 2) +
  Real.sqrt ((x - x₃) ^ 2 + (y - y₃) ^ 2) = S := by
  sorry



theorem theorem_866099_problem (P Q : LaurentSeries ℝ) (k : ℤ) :
  (P * Q).coeff k = ∑ᶠ p : {p : ℤ × ℤ // p.1 + p.2 = k}, (P.coeff p.val.1) * (Q.coeff p.val.2) := by
  sorry

theorem theorem_866073_problem (p : ℝ → ℝ) (hp : Differentiable ℝ p) (r θ : ℝ) (hr : r > 0)
  (h_indep : deriv (fun t => p (r * Real.cos t) * p (r * Real.sin t)) θ = 0) :
  0 = r * Real.cos θ * p (r * Real.cos θ) * deriv p (r * Real.sin θ) - 
      r * Real.sin θ * p (r * Real.sin θ) * deriv p (r * Real.cos θ) := by
  sorry

theorem theorem_865873_problem
  (n : ℕ)
  (α : Fin (n + 1) → ℝ) (hα : α (Fin.last n) ≠ 0)
  (f : (Fin (n + 1) → ℝ) → ℝ) (hf : Differentiable ℝ f)
  (h_pde : ∀ x : Fin (n + 1) → ℝ, fderiv ℝ f x α = 0) :
  ∃ Φ : (Fin n → ℝ) → ℝ,
    Differentiable ℝ Φ ∧
    ∀ x : Fin (n + 1) → ℝ,
      f x = Φ (fun i : Fin n =>
        α (Fin.last n) * x (Fin.castSucc i) - α (Fin.castSucc i) * x (Fin.last n)) := by
  sorry

theorem theorem_866303_problem
  (θ : ℝ)
  (hθ : Irrational (θ / Real.pi)) :
  ¬ ∃ (A : Set circle), IsClosed A ∧ A.Nonempty ∧ A ≠ univ ∧
    (fun z ↦ expMapCircle θ * z) '' A = A := by
  sorry























theorem theorem_866442_problem
  {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (hG_conn : G.Connected)
  (v0 : V)
  (I : ℕ → Set V)
  (hI : ∀ t, I t = {v | G.dist v0 v = t})
  (T : ℕ)
  (hT : T = Finset.sup Finset.univ (fun v ↦ ENat.toNat (G.dist v0 v))) :
  ∀ t, t > T → I t = ∅ := by
  sorry







theorem theorem_866786_problem (S : Type*) (h1 : Countable S) (h2 : Infinite S) :
  ¬ Countable (Set S) := by
  sorry





theorem theorem_867149_problem
  (X : Type*) [TopologicalSpace X] [CompactSpace X]
  (F : ℕ → C(X, ℝ))
  (f : C(X, ℝ))
  (h_pointwise : ∀ x : X, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x)))
  (A B : Set X)
  (h_union : A ∪ B = Set.univ)
  (hA : IsCompact A)
  (hB : IsCompact B)
  (h_inc : ∀ x ∈ A, Monotone (fun n => F n x))
  (h_dec : ∀ x ∈ B, Antitone (fun n => F n x)) :
  TendstoUniformly (fun n x => F n x) f Filter.atTop := by
  sorry

theorem theorem_867070_problem (f : ℝ → ℝ) (a L : ℝ) :
  Filter.Tendsto f (nhdsWithin a {x | x ≠ a}) (nhds L) ↔
  (∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε) := by
  sorry

theorem theorem_867225_problem
  {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  (p : X → Y → ℝ)
  (hp_nonneg : ∀ x y, 0 ≤ p x y)
  (hp_sum : ∑ x, ∑ y, p x y = 1) :
  let p_x := λ x => ∑ y, p x y
  let p_y_given_x := λ y x => if p_x x = 0 then 0 else p x y / p_x x
  let H_Y_given_X_eq_x := λ x => - ∑ y, (p_y_given_x y x) * Real.log (p_y_given_x y x)
  let H_Y_given_X := ∑ x, (p_x x) * H_Y_given_X_eq_x x
  H_Y_given_X ≥ 0 := by
  sorry

theorem theorem_866717_problem (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
  n * (n + 1) ∣ Nat.factorial (k + 1) * ∑ x in Finset.Icc 1 n, x ^ k := by
  sorry





theorem theorem_867367_problem
  (f : ℝ × ℝ → ℝ)
  (h_diff : ContDiff ℝ 2 f)
  (h_strict_convex : StrictConvexOn ℝ Set.univ f)
  (h_hess_pos_def : ∀ x : ℝ × ℝ, ∀ v : ℝ × ℝ, v ≠ 0 → fderiv ℝ (fderiv ℝ f) x v v > 0) :
  ∃! p : ℝ × ℝ, ∀ q : ℝ × ℝ, f p ≤ f q := by
  sorry



theorem theorem_867396_problem
  (X b C Y : ℕ → ℝ)
  (hY : ∀ t, t ≥ 1 → Y t = X t * b (t - 1))
  (hRec : ∀ t, t ≥ 1 → Y t - Y (t - 1) = C (t - 1))
  (hb : ∀ t, t ≥ 1 → b (t - 1) ≠ 0) :
  ∀ t, t ≥ 1 → X t = (Y 0 + ∑ k in Finset.range t, C k) / b (t - 1) := by
  sorry







theorem theorem_867747_problem (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
  (hX : DiscreteTopology X)
  (hY : ∃ (s : ℕ → Y) (y : Y), Filter.Tendsto s Filter.atTop (nhds y) ∧ y ∉ Set.range s) :
  ¬ Nonempty (Y ≃ₜ X) := by
  sorry





theorem theorem_868087_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (A E : H →L[ℂ] H)
  (hA : IsStarNormal A) :
  spectrum ℂ (A + E) ⊆ {z : ℂ | Metric.infDist z (spectrum ℂ A) ≤ ‖E‖} := by
  sorry

theorem theorem_867721_problem (n : ℕ) (hn : 0 < n) :
  (∃ x y : ℤ, (n : ℤ) = x^2 - 2 * y^2) ↔
  (∀ p : ℕ, Nat.Prime p → p ≠ 2 → (p % 8 = 3 ∨ p % 8 = 5) → Even (padicValNat p n)) := by
  sorry

theorem theorem_867726_problem
  (k : Type*) [Field k] [Infinite k]
  (n : ℕ) (hn : n ≥ 1) :
  ∀ p : MvPolynomial (Fin n) k,
  (∀ x : Fin n → k, MvPolynomial.eval x p = 0) →
  p = 0 := by
  sorry





theorem theorem_868152_problem (n : ℕ) :
  Continuous (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) := by
  sorry



theorem theorem_868319_problem
  (y : ℝ → ℝ)
  (h1 : Differentiable ℝ y)
  (h2 : Differentiable ℝ (deriv y))
  (h3 : ∀ x, (y x)^3 - 2 * x * (y x) + 4 = 0) :
  ∀ x, (3 * (y x)^2 - 2 * x) * (deriv (deriv y) x) =
       (4 - 6 * (y x) * (deriv y x)) * (deriv y x) := by
  sorry

theorem theorem_868510_problem (n : ℕ) (hn : n > 1)
  (U V : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
  (hU_open : IsOpen U)
  (hV_open : IsOpen V)
  (h_cover : U ∪ V = Set.univ)
  (hU_conn : IsConnected U)
  (hV_conn : IsConnected V) :
  IsConnected (U ∩ V) := by
  sorry





theorem theorem_868501_problem (a : ℕ → ℕ → ℝ)
  (h_mono : ∀ k, Antitone (fun n ↦ a n k)) :
  (⨅ n, Filter.liminf (fun k ↦ (a n k : EReal)) Filter.atTop) ≥
  Filter.liminf (fun k ↦ ⨅ n, (a n k : EReal)) Filter.atTop := by
  sorry



theorem theorem_868678_problem (R : Type*) [Ring R] (c : Rˣ) (n : ℤ) :
  ((c * c⁻¹) ^ n : Rˣ) = c ^ n * c ^ (-n) := by
  sorry

theorem theorem_869134_problem (V E F g : ℕ) (χ : ℤ)
  (h_chi : χ = (V : ℤ) - E + F)
  (h_surface : χ = 2 - 2 * (g : ℤ)) :
  (g : ℚ) = 1 - (χ : ℚ) / 2 := by
  sorry

theorem theorem_868086_problem
  (a b : ℕ → ℝ)
  (p q : ℝ)
  (ha : ∀ k, 0 ≤ a k)
  (hb : ∀ k, 0 ≤ b k)
  (hp : 1 < p)
  (hq : 1 < q)
  (hpq : 1 / p + 1 / q = 1)
  (F : ℕ → ℝ)
  (hF : ∀ n, F n = (∑ k in Finset.Icc 1 n, a k ^ p) ^ (1 / p) * (∑ k in Finset.Icc 1 n, b k ^ q) ^ (1 / q)) :
  ∀ n, F n ≤ F (n + 1) := by
  sorry

theorem theorem_868307_problem
  {X : Type*} [TopologicalSpace X] [T2Space X]
  (D : Set X)
  (h_dense : Dense D)
  (h_loc_compact : LocallyCompactSpace D) :
  IsOpen D := by
  sorry



theorem theorem_868582_problem (α β : ℝ)
  (hα : 0 < α ∧ α < 1)
  (hβ : 0 < β ∧ β < 1)
  (P : Matrix (Fin 2) (Fin 2) ℝ)
  (hP : P = !![1 - α, α; β, 1 - β])
  (π : Fin 2 → ℝ)
  (h_stat : Matrix.vecMul π P = π)
  (h_norm : ∑ i, π i = 1) :
  π 0 = β / (α + β) ∧ π 1 = α / (α + β) := by
  sorry





theorem theorem_869115_problem
  (m p : ℕ)
  (hm_pos : m > 0)
  (h_m_solvable : ∀ (G : Type*) [Group G], Nat.card G = m → IsSolvable G)
  (hp_prime : p.Prime)
  (h_ineq : Real.sqrt (2 * m + 1) < p) :
  ∀ (G : Type*) [Group G], Nat.card G = m * p → IsSolvable G := by
  sorry



theorem theorem_869182_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (m : ℕ)
  (e : Basis (Fin m) K V)
  (IP : V →ₗ[K] V →ₗ[K] K)
  (x y : V)
  (xc yc : Fin m → K)
  (hx : x = ∑ i, xc i • e i)
  (hy : y = ∑ j, yc j • e j)
  (g : Fin m → Fin m → K)
  (hg : ∀ i j, g i j = IP (e i) (e j)) :
  IP x y = ∑ i : Fin m, ∑ j : Fin m, g i j * xc i * yc j := by
  sorry









theorem theorem_869685_problem (a b : ℝ) (f g : ℝ → ℝ)
  (hab : a ≤ b)
  (hf : ContinuousOn f (Set.Icc a b))
  (hg : ∀ x ∈ Set.Icc a b, g x = ∫ t in a..x, f t) :
  ∀ x ∈ Set.Icc a b, HasDerivWithinAt g (f x) (Set.Icc a b) x := by
  sorry



theorem theorem_868952_problem (N : ℝ) (hN : 2 < N)
  (f : ℂ → ℝ) (hf : ∀ u, f u = (Complex.abs u) ^ (4 / (N - 2))) :
  ∃ C, ∀ u v : ℂ, u ≠ 0 → v ≠ 0 →
    ‖gradient f u - gradient f v‖ ≤ C * Complex.abs (u - v) *
    ((Complex.abs u) ^ ((6 - N) / (N - 2)) + (Complex.abs v) ^ ((6 - N) / (N - 2))) := by
  sorry





theorem theorem_869553_problem (f : ℝ → ℝ) (c : ℝ) 
  (h : DifferentiableAt ℝ f c) : 
  ContinuousAt f c := by
  sorry

theorem theorem_869688_problem (x : ℕ → ℝ)
  (h : ∀ n m : ℕ, 1 ≤ m → m < n → |x n - x m| = ∑ k in Finset.Ioc m n, ((k : ℝ) / (2 * k + 1 : ℝ)) ^ k) :
  CauchySeq x := by
  sorry







