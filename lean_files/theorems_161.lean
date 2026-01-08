import Mathlib
import Mathlib.Tactic

theorem theorem_876163_problem
  (f : ℝ → ℝ → ℝ → ℝ)
  (F : ℝ → ℝ → ℝ)
  (h_diff : ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ ↦ f p.1 p.2.1 p.2.2))
  (h_pde : ∀ x y t : ℝ, deriv (fun t' ↦ f x y t') t + deriv (fun x' ↦ f x' y t) x + deriv (fun y' ↦ f x y' t) y = 0)
  (h_ic : ∀ x y : ℝ, f x y 0 = F x y) :
  ∀ x y t : ℝ, f x y t = F (x - t) (y - t) := by
  sorry













theorem theorem_876662_problem (n : ℕ) (p : Fin n → ℕ) (x : ℝ) :
  ∑ i in Finset.range ((∑ j, p j) + 1), ((∑ j, p j).choose i : ℝ) * x ^ i =
  ∏ j, (∑ k in Finset.range (p j + 1), ((p j).choose k : ℝ) * x ^ k) := by
  sorry





theorem theorem_876055_problem {X : Type*} [TopologicalSpace X] (Y : Set X) :
  derivedSet Y = {x : X | ∀ U : Set X, IsOpen U → x ∈ U → (U ∩ (Y \ {x})).Nonempty} := by
  sorry



theorem theorem_877018_problem (f : ℝ → ℝ) (x : ℝ)
  (hf : Differentiable ℝ f)
  (hx : 1 + Real.cos x ≠ 0) :
  deriv (fun t => (f t * Real.sin t) / (1 + Real.cos t)) x =
  (f x + deriv f x * Real.sin x) / (1 + Real.cos x) := by
  sorry



theorem theorem_877095_problem (A : Set ℝ) (h : IsPathConnected A) :
  Set.OrdConnected A := by
  sorry







theorem theorem_877293_problem (c : ℝ) (h : c > 0) :
  Filter.Tendsto (fun x => (Real.exp (-Real.sqrt x) * Real.sinh (c * x)) / x) Filter.atTop Filter.atTop := by
  sorry

theorem theorem_877287_problem (h : ℝ → ℝ) (c : ℝ)
  (h_diff : Differentiable ℝ h)
  (h_deriv : ∀ x, deriv h x = c) :
  ∃ q : ℝ, ∀ x, h x = c * x + q := by
  sorry



theorem theorem_877585_problem 
  {X : Type*} 
  (f_n : ℕ → X → ℝ) 
  (f : X → ℝ) 
  (h_unif : TendstoUniformly f_n f Filter.atTop) :
  Filter.Tendsto (fun n ↦ sSup (Set.range (f_n n))) Filter.atTop (nhds (sSup (Set.range f))) := by
  sorry





theorem theorem_877326_problem
  (n m : ℕ)
  (f : Fin m → MvPolynomial (Fin n) ℤ)
  (T : Type*) [CommRing T] :
  Nonempty ((MvPolynomial (Fin n) ℤ ⧸ Ideal.span (Set.range f) →+* T) ≃
    { a : Fin n → T // ∀ i : Fin m, MvPolynomial.eval₂ (Int.castRingHom T) a (f i) = 0 }) := by
  sorry

theorem theorem_876939_problem (N : ℕ) 
  (h_range : 10 ≤ N ∧ N ≤ 99) 
  (h_digitsum : 170 ∣ (Nat.digits 10 (10^N - N)).sum) : 
  N = 20 ∨ N = 39 ∨ N = 58 ∨ N = 77 ∨ N = 96 := by
  sorry

theorem theorem_877743_problem (α t : ℝ) (hα : 0 < α) (ht : α ≤ t) :
  let H : ℝ → ℝ := fun x ↦ if x < 0 then 0 else 1
  let f : ℝ → ℝ := fun τ ↦ (τ / Real.sqrt (τ^2 - α^2)) * H (τ - α)
  ∫ τ in (0)..t, f τ = ∫ τ in α..t, τ / Real.sqrt (τ^2 - α^2) := by
  sorry



theorem theorem_877407_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (π : X → X)
  (hπ : ∀ x, π x ∈ Metric.closedBall (0 : X) 1 ∧
        ∀ y ∈ Metric.closedBall (0 : X) 1, ‖x - π x‖ ≤ ‖x - y‖)
  (a b : X)
  (ha : 1 ≤ ‖a‖)
  (hb : 1 ≤ ‖b‖) :
  ‖π a - π b‖ ≤ ‖a - b‖ := by
  sorry

theorem theorem_877513_problem (S : Set ℕ) (h : S.Nonempty) :
  ∃ n ∈ S, ∀ k ∈ S, n ≤ k := by
  sorry

theorem theorem_877582_problem (d x_A : ℝ) (h_d : 0 < d) :
  let A : ℝ × ℝ := (x_A, 0)
  let B : ℝ × ℝ := (x_A + d / Real.sqrt 3, -d)
  let C : ℝ × ℝ := (x_A, -2 * d)
  let D : ℝ × ℝ := (x_A - Real.sqrt 3 * d, -d)
  let dist_sq (p1 p2 : ℝ × ℝ) := (p1.1 - p2.1)^2 + (p1.2 - p2.2)^2
  dist_sq A C = dist_sq A D ∧ dist_sq A D = dist_sq C D := by
  sorry

theorem theorem_877503_problem (f : ℂ → ℂ)
  (h_holo : DifferentiableOn ℂ f (Metric.ball 0 1))
  (h_zero : ∀ ζ ∈ Metric.sphere 0 1, ∃ z : ℕ → ℂ, (∀ n, z n ∈ Metric.ball 0 1) ∧
    Filter.Tendsto z Filter.atTop (nhds ζ) ∧
    Filter.Tendsto (fun n => f (z n)) Filter.atTop (nhds 0))
  (h_inf : ∀ ζ ∈ Metric.sphere 0 1, ∃ z : ℕ → ℂ, (∀ n, z n ∈ Metric.ball 0 1) ∧
    Filter.Tendsto z Filter.atTop (nhds ζ) ∧
    Filter.Tendsto (fun n => Complex.abs (f (z n))) Filter.atTop Filter.atTop) :
  ∀ ζ ∈ Metric.sphere 0 1,
    ¬ (∃ (g : ℂ → ℂ) (r : ℝ), 0 < r ∧ DifferentiableOn ℂ g (Metric.ball ζ r) ∧
        Set.EqOn f g (Metric.ball ζ r ∩ Metric.ball 0 1)) ∧
    ¬ (Filter.Tendsto (fun z => Complex.abs (f z)) (nhdsWithin ζ (Metric.ball 0 1)) Filter.atTop) := by
  sorry



theorem theorem_877220_problem (r theta : ℝ) (h : r ≥ 1) :
  (1 - r * Real.cos theta) / (1 + r^2 - 2 * r * Real.cos theta) ≤ 
  1 / 2 + 1 / 4 * (r - 1) ^ 2 := by
  sorry

theorem theorem_878665_problem (A B C : Prop) :
  ((A ∧ B) → C) ↔ (A → (B → C)) := by
  sorry

theorem theorem_878576_problem (G : Type*) [Group G] (H : Subgroup G) (g : G)
  (h_cond : ∀ h ∈ H, g * h * g⁻¹ ∈ H) :
  Set.image (fun h ↦ g * h * g⁻¹) H ⊆ H := by
  sorry



theorem theorem_878511_problem {X Y : Type*} [Nonempty X] [Nonempty Y]
  (F : X → Set Y) (h : ∀ x, (F x).Nonempty) :
  ∃ f : X → Y, ∀ x, f x ∈ F x := by
  sorry









theorem theorem_878598_problem (R : Type*) [CommRing R]
  (h : (⊤ : Ideal R) ^ 2 = ⊤)
  (M : Ideal R) (hM : M.IsMaximal) :
  M.IsPrime := by
  sorry







theorem theorem_878089_problem
  (G : Type*) [Group G]
  (A B : Subgroup G)
  (h_disjoint : Disjoint A B)
  (h_sup : A ⊔ B = ⊤)
  (h_comm : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
  (φ : A →* B)
  (hφ : ∀ a, φ a ∈ Subgroup.center B)
  (C : Subgroup G)
  (hC : ∀ x, x ∈ C ↔ ∃ a : A, x = (a : G) * (φ a : G)) :
  Nonempty (G ≃* C × B) := by
  sorry

theorem theorem_878334_problem (a b c : ℝ)
  (ha_ne : a ≠ 0) (hb_ne : b ≠ 0) (hc_ne : c ≠ 0)
  (h_sum_sq : a^2 + b^2 + c^2 ≠ 0)
  (z₁ z₂ : ℂ)
  (hz₁ : z₁ = a + c * Complex.I)
  (hz₂ : z₂ = a - c * Complex.I)
  (ha : a > 0) (hc : c > 0) :
  (1 / 2 : ℂ) * Complex.I * Complex.log (z₁ / z₂) = ↑(Real.arctan (a / c)) := by
  sorry



theorem theorem_878919_problem
  (n : ℕ)
  (birth_rate : Fin n → (Fin n → ℤ) → ℝ)
  (death_rate : Fin n → (Fin n → ℤ) → ℝ)
  (P : (Fin n → ℤ) → ℝ → ℝ)
  (dPdt : (Fin n → ℤ) → ℝ → ℝ)
  (e : Fin n → (Fin n → ℤ))
  (he : ∀ i, e i = Pi.single i 1)
  (h_pos_birth : ∀ i x, birth_rate i x > 0)
  (h_pos_death : ∀ i x, death_rate i x > 0)
  (h_dynamics : ∀ (x : (Fin n → ℤ)) (t : ℝ),
    dPdt x t =
      (∑ i : Fin n, birth_rate i (x - e i) * P (x - e i) t) +
      (∑ i : Fin n, death_rate i (x + e i) * P (x + e i) t) -
      (P x t * ∑ i : Fin n, (birth_rate i x + death_rate i x))) :
  ∀ (x : (Fin n → ℤ)) (t : ℝ),
    dPdt x t =
      (∑ i : Fin n, (birth_rate i (x - e i) * P (x - e i) t - birth_rate i x * P x t)) +
      (∑ i : Fin n, (death_rate i (x + e i) * P (x + e i) t - death_rate i x * P x t)) := by
  sorry

theorem theorem_878600_problem :
  let G : Set ℂ := {z | Complex.abs z < 1 ∧ 0 < z.im}
  let D : Set ℂ := {z | Complex.abs z < 1}
  let f1 : ℂ → ℂ := fun z ↦ Complex.I * (z⁻¹ + z)
  let f2 : ℂ → ℂ := fun z ↦ (z - 1) / (z + 1)
  let f : ℂ → ℂ := f2 ∘ f1
  ∃ φ : G ≃ₜ D, ∀ z : G, (φ z : ℂ) = f z := by
  sorry







theorem theorem_879245_problem :
  Filter.Tendsto (fun x : ℝ => (x + 1) ^ (1 / x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp 1)) := by
  sorry

theorem theorem_879276_problem (n : ℕ) (x y : ℕ → ℝ) :
  ∑ k in Finset.Ico 1 (n + 1), x (k - 1) * (y k - y (k - 1)) =
  x n * y n - x 0 * y 0 -
  (∑ k in Finset.Ico 1 (n + 1), y (k - 1) * (x k - x (k - 1))) -
  ∑ k in Finset.Ico 1 (n + 1), (y k - y (k - 1)) * (x k - x (k - 1)) := by
  sorry



theorem theorem_879516_problem (R S : Type*)
  [ConditionallyCompleteLinearOrderedField R]
  [ConditionallyCompleteLinearOrderedField S] :
  Nonempty (R ≃+*o S) := by
  sorry







theorem theorem_880102_problem : ¬ Summable (fun n : ℕ => |Real.sin n| / n) := by
  sorry



theorem theorem_879896_problem
  {n a : Type*} [Fintype n] [Fintype a] [DecidableEq n] [DecidableEq a]
  {K : Type*} [Field K]
  (Z X : Matrix n a K) (Y : Matrix n (Fin 1) K)
  (h1 : Invertible (Z.transpose * X))
  (h2 : Invertible (Z.transpose * Z)) :
  let num := (Z.transpose * Z)⁻¹ * (Z.transpose * Y)
  let den := (Z.transpose * Z)⁻¹ * (Z.transpose * X)
  den⁻¹ * num = (Z.transpose * X)⁻¹ * (Z.transpose * Y) := by
  sorry





theorem theorem_880000_problem (R : Type*) [CommRing R] [IsNoetherianRing R]
  (n : ℕ) (hn : n ≠ 0) :
  Set.Finite {I : Ideal R | Nat.card (R ⧸ I) = n} := by
  sorry















theorem theorem_880722_problem
  (a b c d : ℂ)
  (h_det : a * d - b * c ≠ 0)
  (f : ℂ → ℂ)
  (h_f : ∀ z, f z = (a * z + b) / (c * z + d))
  (h_defined : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, c * z + d ≠ 0)
  (h_maps : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, f z ∈ Metric.closedBall (0 : ℂ) 1) :
  ∃ z ∈ Metric.closedBall (0 : ℂ) 1, f z = z := by
  sorry



theorem theorem_880422_problem
  (w : ℕ)
  (h_odd : Odd w)
  (State : Type)
  (initial_state : State)
  (mass : State → ℕ)
  (capacity : ℕ)
  (next_state : State → ℕ → State)
  (is_loss : State → Prop)
  -- Condition derived from w being odd and pieces being 2x2:
  -- Lines cannot be cleared, so mass increases by the piece size (4) at every step.
  (h_step_mass : ∀ (s : State) (c : ℕ), mass (next_state s c) = mass s + 4)
  -- Condition: Exceeding capacity results in a loss.
  (h_loss_cond : ∀ (s : State), mass s > capacity → is_loss s) :
  -- Conclusion: There exists a finite sequence length n such that any strategy leads to loss.
  ∃ n : ℕ, ∀ (moves : List ℕ), moves.length = n →
    is_loss (moves.foldl next_state initial_state) := by
  sorry

theorem theorem_880544_problem
  (s t : ℕ → ℝ)
  (h1 : ∀ n k, n < 2^k → s n ≤ t k)
  (h2 : ∀ n k, n > 2^k → 2 * s n ≥ t k) :
  Bornology.IsBounded (Set.range s) ↔ Bornology.IsBounded (Set.range t) := by
  sorry





theorem theorem_881010_problem
  {K : Type*} [Field K]
  {D : Type*}
  {n : ℕ}
  (f : Fin n → D → K)
  (h : ∀ (c : Fin n → K), (∀ x : D, ∑ i : Fin n, c i * f i x = 0) → ∀ i : Fin n, c i = 0) :
  LinearIndependent K f := by
  sorry

theorem theorem_880811_problem (f : ℝ → ℝ) (c : ℝ)
  (h : DifferentiableAt ℝ f c) : ContinuousAt f c := by
  sorry

theorem theorem_879936_problem (f : Polynomial (ZMod 5)) (h : f = X ^ 4 - 3) :
  Irreducible f := by
  sorry







theorem theorem_881315_problem
  (P : Set {x : ℚ // 0 ≤ x ∧ x ≤ 1} → ℝ)
  (c : ℝ)
  (h_range : ∀ s, 0 ≤ P s ∧ P s ≤ 1)
  (h_total : P Set.univ = 1)
  (h_unif : ∀ q, P {q} = c)
  (h_pos : c > 0)
  (h_add : ∀ f : ℕ → Set {x : ℚ // 0 ≤ x ∧ x ≤ 1},
    Pairwise (Disjoint on f) → HasSum (fun i ↦ P (f i)) (P (⋃ i, f i))) :
  False := by
  sorry

theorem theorem_881174_problem (n : ℕ) (a b : Fin n → ℝ) (c₁ c₂ : ℝ)
  (h_indep : LinearIndependent ℝ ![a, b]) :
  ∃ (S : AffineSubspace ℝ (Fin n → ℝ)),
    (S : Set (Fin n → ℝ)) = {x | Matrix.dotProduct a x = c₁} ∩ {x | Matrix.dotProduct b x = c₂} ∧
    FiniteDimensional.finrank ℝ S.direction = n - 2 := by
  sorry



theorem theorem_881242_problem (n : ℕ) (hn : 0 < n) :
  let P : ℝ := (n + 1 : ℝ) ^ 2
  let Q : ℝ := ((n + 1 : ℝ) * (n + 2 : ℝ)) / 2
  let H : ℝ := ∑ k in Finset.Icc 1 (n + 1), (1 : ℝ) / k
  ∑ r in Finset.Icc 1 n, ∑ k in Finset.Icc 1 r, ((2 * r + 1 : ℝ) / k) = P * H - Q := by
  sorry



theorem theorem_881450_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
  A.trace = (Matrix.charpoly A).roots.sum := by
  sorry

theorem theorem_881855_problem
  (R : Type*) [CommRing R]
  (x : R)
  (f : R →ₗ[R] R)
  (h : ∀ r, f r = r * x) :
  Nonempty ((R ⧸ LinearMap.range f) ≃ₗ[R] (R ⧸ Ideal.span {x})) := by
  sorry





theorem theorem_882036_problem (S : ZFSet)
  (hS : ∅ ∈ S ∧ ∀ x ∈ S, insert x x ∈ S) :
  ∃! z, z ∈ S ∧ ∀ w, w ∉ z := by
  sorry

theorem theorem_881886_problem :
  0.527 ≤ A_f ∧ A_f ≤ 0.537 := by
  sorry

theorem theorem_881693_problem (p : ℕ) (hp : Nat.Prime p) :
  Set.ncard { g : (ZMod p)ˣ | Subgroup.closure {g} = ⊤ } = Nat.totient (p - 1) := by
  sorry



theorem theorem_881899_problem (y : ℝ → ℝ)
  (h : ∀ x, deriv (deriv y) x - 6 * deriv y x + 13 * y x = Real.rpow 3 x) :
  ∃ c₁ c₂ : ℝ, ∀ x, y x = Real.exp (3 * x) * (c₁ * Real.cos (2 * x) + c₂ * Real.sin (2 * x)) +
  (1 / ((Real.log 3) ^ 2 - 6 * Real.log 3 + 13)) * Real.rpow 3 x := by
  sorry

