import Mathlib
import Mathlib.Tactic

theorem theorem_738528_problem
  -- Abstract types for differential forms and vector fields
  (Ω0 Ω1 Ω2 Ω3 : Type)
  (R_vec : Type)
  -- Operators
  (d : Ω1 → Ω2)
  (wedge_1_2 : Ω1 → Ω2 → Ω3)
  (wedge_1_1 : Ω1 → Ω1 → Ω2)
  (ι_1 : R_vec → Ω1 → Ω0)
  (ι_2 : R_vec → Ω2 → Ω1)
  (ι_3 : R_vec → Ω3 → Ω2)
  (smul : Ω0 → Ω2 → Ω2)
  (sub : Ω2 → Ω2 → Ω2)
  -- Constants
  (one : Ω0)
  (zero_1 : Ω1)
  (zero_2 : Ω2)
  -- Variables
  (β : Ω1)
  (R : R_vec)
  (Pos : Ω2 → Prop)
  -- Algebraic Axioms (Properties of the Manifold/Forms)
  (h_leibniz : ι_3 R (wedge_1_2 β (d β)) = sub (smul (ι_1 R β) (d β)) (wedge_1_1 β (ι_2 R (d β))))
  (h_smul_one : ∀ ω, smul one ω = ω)
  (h_wedge_zero : ∀ ω, wedge_1_1 ω zero_1 = zero_2)
  (h_sub_zero : ∀ ω, sub ω zero_2 = ω)
  -- Conditions
  (h_reeb_1 : ι_1 R β = one)
  (h_reeb_2 : ι_2 R (d β) = zero_1)
  (h_open_book : Pos (d β)) :
  Pos (ι_3 R (wedge_1_2 β (d β))) := by
  sorry







theorem theorem_738683_problem
  (a b c d p A B C : ℝ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hp : 0 < p)
  (hA : A = a / b) (hB : B = c / d) (hC : C = 1 / p)
  (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) :
  (1 / (b * d * p)) * ∫ x in Set.Ioi 0, 1 / ((A + x) * (B + x) * (C + x)) =
  (1 / (b * d * p)) * ((- Real.log A) / ((A - B) * (A - C)) +
                      (- Real.log B) / ((B - A) * (B - C)) +
                      (- Real.log C) / ((C - A) * (C - B))) := by
  sorry











theorem theorem_738878_problem (x y z : ℕ)
  (h : x.factorial + y.factorial = z.factorial) :
  (x = 0 ∧ y = 0 ∧ z = 2) ∨
  (x = 0 ∧ y = 1 ∧ z = 2) ∨
  (x = 1 ∧ y = 0 ∧ z = 2) ∨
  (x = 1 ∧ y = 1 ∧ z = 2) := by
  sorry



theorem theorem_738641_problem (p : Polynomial ℤ) 
  (h : p = X^8 + 3 * X^3 - 1) : 
  Irreducible p := by
  sorry

theorem theorem_738815_problem
  -- Let X_n be a Markov process. We represent the probability distributions
  -- at step n and n-1 as functions from state (ℕ) to probability (ℝ).
  (P_n P_n_minus_1 : ℕ → ℝ)
  -- The indicator function 1_{x=k/d} defined in the problem
  -- defined as 1 if x = k/d and d divides k, 0 otherwise.
  -- Note: In ℕ, (x = k/d ∧ d ∣ k) is equivalent to (x * d = k).
  (indicator : ℕ → ℕ → ℕ → ℝ)
  (h_indicator : ∀ x k d, indicator x k d = if x * d = k then 1 else 0)
  -- The transition probabilities defined as P(X_{n+1}=k|X_n=x)
  (trans_prob : ℕ → ℕ → ℝ)
  (h_trans_prob : ∀ x k, trans_prob x k =
    (indicator x k 2) / 2 + (indicator x k 3) / 3 + (indicator x k 6) / 6)
  -- The probability at step n is derived from step n-1 via the
  -- Chapman–Kolmogorov equation (law of total probability)
  (h_total_prob : ∀ k, P_n k = ∑' x, trans_prob x k * P_n_minus_1 x) :
  -- Prove the recursive formula for P(X_n = k)
  ∀ k, P_n k =
    (if 2 ∣ k then (1 : ℝ) else 0) / 2 * P_n_minus_1 (k / 2) +
    (if 3 ∣ k then (1 : ℝ) else 0) / 3 * P_n_minus_1 (k / 3) +
    (if 6 ∣ k then (1 : ℝ) else 0) / 6 * P_n_minus_1 (k / 6) := by
  sorry



theorem theorem_739801_problem
  (p q y₁ y₂ : ℝ → ℝ)
  (hp : Differentiable ℝ p)
  (hy₁ : Differentiable ℝ y₁)
  (hpy₁ : Differentiable ℝ (λ x => p x * deriv y₁ x))
  (hp_ne : ∀ x, p x ≠ 0)
  (hy₁_ne : ∀ x, y₁ x ≠ 0)
  (h_ode₁ : ∀ x, deriv (λ x => p x * deriv y₁ x) x + q x * y₁ x = 0)
  (h_y₂ : ∃ v : ℝ → ℝ, (∀ x, deriv v x = 1 / (p x * (y₁ x)^2)) ∧ (∀ x, y₂ x = y₁ x * v x)) :
  ∀ x, deriv (λ x => p x * deriv y₂ x) x + q x * y₂ x = 0 := by
  sorry

theorem theorem_739976_problem (a : ℕ → ℂ) :
  Summable a ↔ CauchySeq (fun N ↦ ∑ n in Finset.range (N + 1), a n) := by
  sorry







theorem theorem_739925_problem :
  ∃ f : ℝ → ℝ, Differentiable ℝ f ∧ Monotone f ∧
  ∀ ε > 0, ¬ ∃ L : ℝ, Filter.Tendsto (fun x ↦ deriv f x / x ^ (1 + ε)) Filter.atTop (nhds L) := by
  sorry



theorem theorem_740353_problem (α β T : ℝ) (hT : T > 0) :
  ∫ t in (-T)..T, (Real.cos (t * α) - Real.cos (t * β)) / t = 0 := by
  sorry





theorem theorem_740578_problem (n m₁ m_neg1 : ℕ) (k : ℤ)
  (h1 : m₁ + m_neg1 = n)
  (h2 : (m₁ : ℤ) - (m_neg1 : ℤ) = k) :
  let S := {f : Fin n → ℤ | (Finset.univ.filter (fun i => f i = 1)).card = m₁ ∧ 
                            (Finset.univ.filter (fun i => f i = -1)).card = m_neg1}
  Nat.card S = n.factorial / (m₁.factorial * m_neg1.factorial) := by
  sorry

theorem theorem_740564_problem (a b : ℝ) (f : ℝ → ℂ) (α : ℝ)
  (hf : IntervalIntegrable f volume a b) :
  |((Complex.exp (Complex.I * (α : ℂ))) * ∫ x in a..b, f x).re| =
  |∫ x in a..b, ((Complex.exp (Complex.I * (α : ℂ))) * f x).re| := by
  sorry

theorem theorem_740210_problem 
  (x₁ y₁ x₂ y₂ x₃ y₃ : ℝ)
  (AD BD CD : ℝ)
  (h_triangle : (x₂ - x₁) * (y₃ - y₁) ≠ (x₃ - x₁) * (y₂ - y₁)) :
  ∀ (xD yD xD' yD' : ℝ),
    ((xD - x₁)^2 + (yD - y₁)^2 = AD^2) →
    ((xD - x₂)^2 + (yD - y₂)^2 = BD^2) →
    ((xD - x₃)^2 + (yD - y₃)^2 = CD^2) →
    ((xD' - x₁)^2 + (yD' - y₁)^2 = AD^2) →
    ((xD' - x₂)^2 + (yD' - y₂)^2 = BD^2) →
    ((xD' - x₃)^2 + (yD' - y₃)^2 = CD^2) →
    xD = xD' ∧ yD = yD' := by
  sorry

theorem theorem_740588_problem :
  ∀ M : ℝ, ∃ a b c : ℝ,
    a > 0 ∧ b > 0 ∧ c > 0 ∧
    (2 * a) / (3 * a + b) + (2 * b) / (3 * b + c) + (2 * c) / (3 * c + a) = 1 ∧
    ((2 * a) / (3 * a + b)) * Real.sqrt (3 * a + b) +
    ((2 * b) / (3 * b + c)) * Real.sqrt (3 * b + c) +
    ((2 * c) / (3 * c + a)) * Real.sqrt (3 * c + a) > M := by
  sorry

theorem theorem_740287_problem (α N q_k : ℝ)
  (hN : N ≠ 0)
  (h_denom : 1 / N ≠ q_k)
  (P_Y_Ck : ℝ)
  (h_total_prob : P_Y_Ck = α * (1 / N) + (1 - α) * q_k) :
  α = (P_Y_Ck - q_k) / (1 / N - q_k) := by
  sorry

theorem theorem_740793_problem (p m : ℕ)
  (hp : Nat.Prime p)
  (hm : m > 0)
  (n : ℕ)
  (hn : n = p^m - 1)
  (G : Type*) [Group G] [Fintype G] [IsCyclic G]
  (hG : Fintype.card G = n) :
  Fintype.card { g : G // orderOf g = n } = Nat.totient n := by
  sorry



theorem theorem_741009_problem
  {n : ℕ} {α R : Type*}
  (T : (Fin n → α) → R)
  (ρ : Equiv.Perm (Fin n)) :
  ∃! T' : (Fin n → α) → R, ∀ (i : Fin n → α), T' (i ∘ ρ) = T i := by
  sorry



theorem theorem_740343_problem (N U₁ U₂ : ℝ) (hN : N ≠ 0) :
  (fun T : ℝ => (1 / (N - U₁ / T + U₂ / (2 * T ^ 2))) -
    (1 / N + (1 / N ^ 2) * (U₁ - U₂ / (2 * T)) * (1 / T))) =O[atTop] fun T => 1 / T ^ 3 := by
  sorry

theorem theorem_740874_problem
  (D : Type*)
  (F G : D → D)
  (X : Set D)
  (D_seq : ℕ → Set D)
  (h_D0 : D_seq 0 = X)
  (h_D_succ : ∀ n, D_seq (n + 1) = (F '' (D_seq n)) ∪ (G '' (D_seq n)))
  (D_infty : Set D)
  (h_D_infty : D_infty = ⋃ n, D_seq n)
  (D_infty' : Set D)
  (h_D_infty' : D_infty' = ⋂₀ {S : Set D | X ⊆ S ∧ F '' S ⊆ S ∧ G '' S ⊆ S}) :
  D_infty = D_infty' := by
  sorry

theorem theorem_737960_problem
  (X : Type*) [MetricSpace X]
  (A : Type*)
  (K : A → Set X)
  (h_compact : ∀ α, IsCompact (K α))
  (h_finite_inter : ∀ (S : Finset A), (⋂ α ∈ S, K α).Nonempty) :
  (⋂ α, K α).Nonempty := by
  sorry



theorem theorem_740950_problem (a : ℕ → ℕ → ℝ)
  (h1 : ∀ n, Summable (fun k => ‖a n k‖))
  (h2 : Summable (fun n => ∑' k, ‖a n k‖)) :
  (∑' n, ∑' k, a n k) = (∑' k, ∑' n, a n k) := by
  sorry









theorem theorem_741474_problem (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  (L₁ L₂ : List R)
  (h₁ : ∀ x ∈ L₁, Irreducible x)
  (h₂ : ∀ x ∈ L₂, Irreducible x)
  (h_prod : L₁.prod = L₂.prod) :
  Multiset.Rel Associated (L₁ : Multiset R) (L₂ : Multiset R) := by
  sorry



theorem theorem_741582_problem (n : ℕ) (x : ℝ) (f : ℝ → ℝ)
  (hf : f = fun x ↦ 1 - 1 / (x + 1))
  (hn : 1 ≤ n)
  (hx : x ≠ -1) :
  iteratedDeriv n f x = ((-1 : ℝ)^(n + 1) * (Nat.factorial n : ℝ)) / (x + 1)^(n + 1) := by
  sorry











theorem theorem_741499_problem (f : ℝ → ℝ) 
  (h_diff : ContDiff ℝ 2 f)
  (h_cond : ∀ x, deriv (deriv f) x = -1) :
  ∃ a b : ℝ, ∀ x, f x = -(1/2) * x^2 + a * x + b := by
  sorry



theorem theorem_741601_problem (n : ℕ) (x p : Fin n → ℝ) (phi : ℝ → ℝ)
  (h_pos : ∀ i, 0 < p i)
  (h_sum : ∑ i, p i = 1)
  (h_convex : ConvexOn ℝ Set.univ phi) :
  phi (∑ i, p i * x i) ≤ ∑ i, p i * phi (x i) := by
  sorry

theorem theorem_741847_problem (n : ℕ) (hn : n > 0)
  (f : ℝ → ℝ → ℝ → ℝ) (hf : ∀ x y z, f x y z = (x + y + z) ^ n) :
  deriv (fun z => deriv (fun y => deriv (fun x => f x y z) 1) 1) 1 =
  (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * 3 ^ (n - 3) := by
  sorry





theorem theorem_741881_problem {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module R P] :
  Module.Projective R P ↔ 
  ∃ (I : Type v) (x : I → P) (f : I → P →ₗ[R] R), 
    ∀ p : P, ∃ (s : Finset I), (∀ i, i ∉ s → f i p = 0) ∧ s.sum (fun i ↦ (f i p) • x i) = p := by
  sorry







theorem theorem_740359_problem 
  (A B : GL (Fin 2) ℂ)
  (hA : (A : Matrix (Fin 2) (Fin 2) ℂ) = !![1/2, 1/2; 1/2, -1/2])
  (hB : (B : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, Complex.exp (Complex.I * Real.pi / 2)])
  (G : Subgroup (GL (Fin 2) ℂ))
  (hG : G = Subgroup.closure {A, B}) : 
  Nat.card G = 192 := by
  sorry

theorem theorem_741870_problem :
  (IntermediateField.adjoin (IntermediateField.adjoin ℚ {Real.sqrt 5}) {Real.sqrt 7}).restrictScalars ℚ =
  IntermediateField.adjoin ℚ {Real.sqrt 5, Real.sqrt 7} := by
  sorry

theorem theorem_741918_problem (r₁ r₂ : ℝ)
  (h : Irrational (r₂ / r₁)) :
  Dense {x : ℝ | ∃ a₁ a₂ : ℤ, x = (a₁ : ℝ) * r₁ + (a₂ : ℝ) * r₂} := by
  sorry

theorem theorem_741762_problem
  (q : ℝ → Quaternion ℝ)
  (ω : ℝ → Quaternion ℝ)
  (t : ℝ)
  (h_unit : ‖q t‖ = 1)
  (h_pure : (ω t).re = 0)
  (h_omega_def : HasDerivAt (fun h ↦ q (t + h) * (q t)⁻¹) ((1 / 2 : ℝ) • ω t) 0) :
  deriv q t = (1 / 2 : ℝ) • (ω t * q t) := by
  sorry







theorem theorem_742098_problem (a1 a2 b1 b2 x1 y1 : ℝ) 
  (h_distinct : a1 ≠ b1)
  (m : ℝ) (hm : m = (b2 - a2) / (b1 - a1)) :
  ∀ x y : ℝ, (y - y1 = m * (x - x1)) ↔ 
  ((x ≠ x1 → (y - y1) / (x - x1) = m) ∧ (x = x1 → y = y1)) := by
  sorry

theorem theorem_741935_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  (T : X ≃L[𝕜] Y)
  (b : ℕ → Y)
  (hb : Summable b) :
  T.symm (∑' k, b k) = ∑' k, T.symm (b k) := by
  sorry

theorem theorem_742211_problem (n : ℕ) (c : Fin n → ℝ)
  (hc : ∀ i, 0 < c i)
  (f : (Fin n → ℝ) → ℝ)
  (hf : ∀ y, f y = ∑ i, Real.log (1 + c i * Real.exp (y i))) :
  ConvexOn ℝ Set.univ f := by
  sorry

theorem theorem_741746_problem (n : ℕ) (c₂ : ℝ) (hn : n > 0) :
  let X : ℝ → ℝ := fun x ↦ 300 + 100 * x + c₂ * Real.sin (n * Real.pi * x / 4)
  X 0 = 300 ∧ X 4 = 700 := by
  sorry







theorem theorem_742650_problem (Tu Tp : TopologicalSpace ℝ)
  (hTu : Tu = TopologicalSpace.generateFrom {s : Set ℝ | ∃ a b : ℝ, s = Set.Ioo a b})
  (hTp : Tp = TopologicalSpace.generateFrom {s : Set ℝ | ∃ a b : ℝ, Irrational a ∧ Irrational b ∧ s = Set.Ioo a b}) :
  Tu = Tp := by
  sorry

theorem theorem_742700_problem
  (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (z : Matrix (Fin n) (Fin 1) ℝ)
  [Invertible A]
  (h : (1 : ℝ) - (z.transpose * ⅟A * z) 0 0 ≠ 0) :
  (⅟A + ((1 : ℝ) - (z.transpose * ⅟A * z) 0 0)⁻¹ • (⅟A * z * z.transpose * ⅟A)) * (A - z * z.transpose) = 1 := by
  sorry







theorem theorem_743047_problem (n : ℕ) (f : (Fin n → ℂ) → (Fin n → ℂ))
  (h_poly : ∃ P : Fin n → MvPolynomial (Fin n) ℂ, ∀ x, f x = fun i => MvPolynomial.eval x (P i))
  (h_inj : Function.Injective f) :
  Function.Surjective f := by
  sorry





theorem theorem_742548_problem (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
  let M : ℕ := m.natAbs
  let k : ℕ := m.gcd n
  let m' : ℕ := M / k
  let H := AddMonoidHom.range (AddMonoidHom.mulLeft (n : ZMod M))
  Nonempty (H ≃+ ZMod m') := by
  sorry









theorem theorem_742470_problem (a b : ℕ) (c : ℝ) :
  let f : ℝ × ℝ → ℝ := fun p ↦
    if p = 0 then 0
    else (p.1 ^ a * p.2 ^ b) / (p.1 ^ 2 + p.2 ^ 2) ^ c
  ContDiffAt ℝ 1 f 0 ↔ (a : ℝ) + b ≥ 2 * c + 2 := by
  sorry



theorem theorem_742698_problem (a p s r x y : ℝ)
  (h_pos : 0 < a)
  (h_inside_x : 0 < x ∧ x < a)
  (h_inside_y : 0 < y ∧ y < a)
  (h_p : p^2 = x^2 + y^2)
  (h_s : s^2 = (a - x)^2 + y^2)
  (h_r : r^2 = x^2 + (a - y)^2) :
  a = Real.sqrt ((s^2 + r^2) / 2 + Real.sqrt (p^2 * (s^2 + r^2) - p^4 - (s^2 - r^2)^2 / 4)) := by
  sorry









theorem theorem_743526_problem 
  (a b : ℝ) (f : ℝ → ℝ) (ξ : ℝ)
  (hab : a < b)
  (hf : ContDiffOn ℝ 1 f (Set.Icc a b))
  (hξ : ξ ∈ Set.Icc a b)
  (hroot : f ξ = 0)
  (hderiv : ∀ x ∈ Set.Icc a b, x ≠ ξ → deriv f x ≠ 0) :
  ∃ δ > 0, ∀ x₀ ∈ Set.Icc a b, |x₀ - ξ| < δ →
    ∀ xn : ℕ → ℝ, xn 0 = x₀ → 
    (∀ n, xn (n + 1) = xn n - f (xn n) / deriv f (xn n)) →
    Filter.Tendsto xn Filter.atTop (nhds ξ) := by
  sorry



theorem theorem_743752_problem
  (F : ℝ → ℝ → ℝ → ℝ)
  (x y z : ℝ)
  (x_fun : ℝ → ℝ → ℝ) -- x as a function of y, z
  (y_fun : ℝ → ℝ → ℝ) -- y as a function of x, z
  (z_fun : ℝ → ℝ → ℝ) -- z as a function of x, y
  -- F is smooth (ContDiff) implies differentiability
  (h_smooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2))
  -- Implicit function definitions satisfying F = 0
  (h_imp_x : ∀ y' z', F (x_fun y' z') y' z' = 0)
  (h_imp_y : ∀ x' z', F x' (y_fun x' z') z' = 0)
  (h_imp_z : ∀ x' y', F x' y' (z_fun x' y') = 0)
  -- Consistency at the specific point (x,y,z)
  (h_pt_x : x_fun y z = x)
  (h_pt_y : y_fun x z = y)
  (h_pt_z : z_fun x y = z)
  -- Differentiability of implicit functions
  (h_diff_x : DifferentiableAt ℝ (fun y' => x_fun y' z) y)
  (h_diff_y : DifferentiableAt ℝ (fun z' => y_fun x z') z)
  (h_diff_z : DifferentiableAt ℝ (fun x' => z_fun x' y) x)
  -- Non-vanishing partial derivatives of F at the point (required for the implicit derivatives to be well-defined)
  (h_Fx_ne_0 : deriv (fun x' => F x' y z) x ≠ 0)
  (h_Fy_ne_0 : deriv (fun y' => F x y' z) y ≠ 0)
  (h_Fz_ne_0 : deriv (fun z' => F x y z') z ≠ 0) :
  deriv (fun y' => x_fun y' z) y * deriv (fun z' => y_fun x z') z * deriv (fun x' => z_fun x' y) x = -1 := by
  sorry



theorem theorem_744073_problem : riemannZeta (-1) = -1 / 12 := by
  sorry

