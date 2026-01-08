import Mathlib
import Mathlib.Tactic



theorem theorem_538861_problem (a b : ℝ)
  (h : (a + b)^3 * (a^2 - a * b + b^2)^3 ≠ 0) :
  a^3 - b^3 = ((a - b) * (a + b)^3 * (a^2 - a * b + b^2)^3 * (a^2 + a * b + b^2)) /
    ((a + b)^3 * (a^2 - a * b + b^2)^3) := by
  sorry





theorem theorem_538995_problem
  {X Y J : Type*} [TopologicalSpace X] [Zero Y]
  (K : Set X) (hK : IsCompact K)
  (ρ : J → X → Y)
  (h_loc : ∀ x ∈ K, ∃ U, IsOpen U ∧ x ∈ U ∧ {j | ∃ y ∈ U, ρ j y ≠ 0}.Finite) :
  ∃ F : Set J, F.Finite ∧ ∀ j ∉ F, K ∩ tsupport (ρ j) = ∅ := by
  sorry







theorem theorem_539316_problem (p : Polynomial ℤ)
  (a b : ℚ) (c : ℕ)
  (hc_sf : Squarefree c) (hc_pos : 0 < c)
  (h_irr : Irrational ((a : ℝ) + (b : ℝ) * Real.sqrt c))
  (h_root : Polynomial.aeval ((a : ℝ) + (b : ℝ) * Real.sqrt c) p = 0) :
  Polynomial.aeval ((a : ℝ) - (b : ℝ) * Real.sqrt c) p = 0 := by
  sorry



theorem theorem_539898_problem {α : Type*} (X : Set (Set α)) :
  ⋂₀ X = {y | ∀ z ∈ X, y ∈ z} := by
  sorry















theorem theorem_540135_problem (n p : ℕ) (hn : n > 0) (hp : Nat.Prime p) :
  (Nat.factorial (n^2 + 2 * n) / Nat.factorial (n^2)).factorization p =
  ∑' k : ℕ, if k ≠ 0 then (n^2 + 2 * n) / p^k - (n^2) / p^k else 0 := by
  sorry

theorem theorem_540131_problem
  (u v : ℝ → ℝ)
  (x : ℝ)
  (hu : DifferentiableAt ℝ u x)
  (hv : DifferentiableAt ℝ v x)
  (hpos : 0 < u x) :
  deriv (fun t => u t ^ v t) x =
  (u x ^ v x) * (deriv v x * Real.log (u x) + v x * (deriv u x / u x)) := by
  sorry

theorem theorem_539526_problem
  (n_atoms : ℕ) (hn : n_atoms > 0)
  (m_liquid : ℕ)
  (S : Fin n_atoms → EuclideanSpace ℝ (Fin 3))
  (L : Fin m_liquid → EuclideanSpace ℝ (Fin 3))
  (c_S : EuclideanSpace ℝ (Fin 3))
  (h_c_S : c_S = (n_atoms : ℝ)⁻¹ • ∑ i, S i)
  (n_vec : EuclideanSpace ℝ (Fin 3))
  (p : EuclideanSpace ℝ (Fin 3))
  (r : EuclideanSpace ℝ (Fin 3))
  (h_r : r = p - c_S) -- Vector connecting c_S to p
  (h_n_nonzero : n_vec ≠ 0)
  (h_r_nonzero : r ≠ 0)
  (theta : ℝ)
  (h_theta : theta = InnerProductGeometry.angle n_vec r) :
  theta = Real.arccos (inner n_vec r / (norm n_vec * norm r)) := by
  sorry

theorem theorem_539899_problem (y : ℝ → ℝ)
  (h_diff : Differentiable ℝ y)
  (h_neq : ∀ x, y x ≠ 0)
  (h_ode : ∀ x, deriv y x = (x * (x^2 + (y x)^2)^2) / (4 * y x)) :
  ∃ c : ℝ, ∀ x, Real.arctan ((x^2 + (y x)^2) / 2) = x^2 / 2 + c := by
  sorry



theorem theorem_540149_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [FiniteDimensional 𝕜 X]
  (T : ℕ → X →L[𝕜] Y)
  (T_lim : X →L[𝕜] Y)
  (h_pointwise : ∀ x : X, Filter.Tendsto (fun n ↦ T n x) Filter.atTop (nhds (T_lim x))) :
  Filter.Tendsto (fun n ↦ ‖T n - T_lim‖) Filter.atTop (nhds 0) := by
  sorry



theorem theorem_539657_problem
  (a : ℝ → ℝ)
  (Λ K : ℝ)
  (hΛ : Λ > 0)
  (t_Λ : ℝ)
  (ht_Λ : t_Λ = 2 / (Real.sqrt 3 * Real.sqrt Λ))
  (h_diff : Differentiable ℝ a)
  (h_ode : ∀ t, a t * (deriv a t) ^ 2 = (Λ / 3) * (a t) ^ 3 + K)
  (h_init : a 0 = 0) :
  ∀ t, (a t) ^ 3 = (3 * K / Λ) * (Real.sinh (t / t_Λ)) ^ 2 := by
  sorry

theorem theorem_540808_problem (P : Prop) : P ∨ ¬P := by
  sorry

theorem theorem_540554_problem
  (S : Type*) [Fintype S] [DecidableEq S]
  (s2 : S)
  (forward : S → ℝ)
  (backward : S → ℝ)
  (prob_joint : S → ℝ)
  (prob_cond : S → ℝ)
  (h_joint : ∀ s, prob_joint s = forward s * backward s)
  (h_cond : ∀ s, prob_cond s = prob_joint s / ∑ x, prob_joint x)
  (h_denom : ∑ x, prob_joint x ≠ 0) :
  prob_cond s2 = (forward s2 * backward s2) / ∑ s, forward s * backward s := by
  sorry

theorem theorem_540776_problem
  (K : Type*) [Field K]
  (M : Type*) [AddCommGroup M] [Module K M]
  (N : Type*) [AddCommGroup N] [Module K N]
  (g : M →ₗ[K] N) :
  Nonempty ((M ⧸ LinearMap.ker g) ≃ₗ[K] LinearMap.range g) := by
  sorry

theorem theorem_540495_problem
  {G : Type*} [Group G] (a b : G)
  (h_ord : orderOf a = orderOf b) :
  ∃ (H : Type*) (hH : Group H) (φ : G →* H),
    Function.Injective φ ∧ ∃ h : H, h * φ a * h⁻¹ = φ b := by
  sorry















theorem theorem_540737_problem (M d G c a : ℝ)
  (hM : 0 < M) (hd : 0 < d) (hG : 0 < G) (hc : 0 < c) :
  a = (4 * G * M) / (d * c ^ 2) := by
  sorry

theorem theorem_540984_problem (n : ℕ) (x : ℝ) :
  (deriv^[n] (fun x => Real.exp x * Real.sin x)) x =
  Real.exp x * (2 : ℝ) ^ ((n : ℝ) / 2) * Real.sin (x + (n : ℝ) * Real.pi / 4) := by
  sorry

theorem theorem_540687_problem (n : ℕ) :
  ∑ i in Finset.range (n + 1), (i : ℚ)^3 = ((n : ℚ)^2 * (n + 1)^2) / 4 := by
  sorry







theorem theorem_541477_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  -- Conditions regarding the bilinear form a
  (a : V → V → ℝ)
  (h_cont : ∃ M > 0, ∀ u v, |a u v| ≤ M * ‖u‖ * ‖v‖)
  (h_coer : ∃ α > 0, ∀ v, a v v ≥ α * ‖v‖^2)
  -- Robin parameter condition
  (ε : ℝ) (h_eps : ε > 0)
  -- Mesh size and solutions
  (h : ℝ) (h_pos : h > 0)
  (u u_h : V)
  (V_h : Set V) (h_uh_in_Vh : u_h ∈ V_h)
  -- Condition: Variational crime + FE stability implies error bound with geometric term
  (C_geom : ℝ)
  (h_cea_crime : ∃ C_1 > 0, ∀ v_h ∈ V_h, ‖u - u_h‖ ≤ C_1 * (‖u - v_h‖ + C_geom * h))
  -- Condition: Regularity implies existence of interpolant with O(h) error
  (C_reg : ℝ)
  (h_interp : ∃ v_h ∈ V_h, ‖u - v_h‖ ≤ C_reg * h) :
  -- Conclusion: Total error is O(h)
  ∃ C, ‖u - u_h‖ ≤ C * h := by
  sorry

theorem theorem_540245_problem :
  let V := ZMod 5 × ZMod 5
  let S : Set V := {(1, 0), (0, 1), (-1, 0), (0, -1)}
  let G : SimpleGraph V := SimpleGraph.fromRel (fun u v ↦ v - u ∈ S)
  let σ_fn : V → V := fun (i, j) ↦ (j, i)
  let τ_fn : V → V := fun (i, j) ↦ (i + 1, j)
  let ρ_fn : V → V := fun (i, j) ↦ (5 - i, j)
  Subgroup.closure { f : G ≃g G | f.toFun ∈ ({σ_fn, τ_fn, ρ_fn} : Set (V → V)) } = ⊤ := by
  sorry



theorem theorem_541044_problem (n : ℕ) (a : Fin n → ℕ) (R : ℕ)
  (h_pos : ∀ i, 0 < a i) :
  (Finset.Icc 1 R).sum (fun x => if ∀ i, a i ∣ x then 1 else 0) =
  R / (Finset.univ.lcm a) := by
  sorry

theorem theorem_541124_problem (ξ : ℝ) (hξ : ξ = Real.sqrt 3 + Real.sqrt 2) :
  IntermediateField.adjoin ℚ {Real.sqrt 2, Real.sqrt 3} = IntermediateField.adjoin ℚ {ξ} := by
  sorry









theorem theorem_541654_problem (w : ℝ) (h : 1 - Complex.exp (-Complex.I * (w : ℂ)) ≠ 0) :
  (1 - Complex.exp (-Complex.I * 6 * (w : ℂ))) / (1 - Complex.exp (-Complex.I * (w : ℂ))) =
  (Complex.sin (3 * (w : ℂ)) / Complex.sin ((w : ℂ) / 2)) * Complex.exp (-Complex.I * 5 * (w : ℂ) / 2) := by
  sorry





theorem theorem_541605_problem
  (n : ℕ) [NeZero n]
  (X Y : Matrix (Fin n) (Fin n) ℝ)
  (hX : X.PosSemidef)
  (hY : Y.PosSemidef) :
  (X * Y).trace ≥ (hX.1.eigenvalues 0) * (hY.1.eigenvalues 0) := by
  sorry



theorem theorem_541935_problem (n : ℕ) [NeZero n] (G : Type*) [Group G] :
  Nat.card (Multiplicative (ZMod n) →* G) = Nat.card { g : G // orderOf g ∣ n } := by
  sorry













theorem theorem_542459_problem :
  Summable (fun n : ℕ => if n = 0 then 0 else (-1 : ℝ) ^ n * Real.sqrt (n + 1) / (n : ℝ)) := by
  sorry

theorem theorem_542242_problem :
  Filter.Tendsto (fun (p : ℝ × ℝ) ↦ p.2 * Real.exp p.1) (nhds (0, 1)) (nhds 1) := by
  sorry

theorem theorem_541575_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (alpha : ℝ → E) (theta : ℝ → ℝ) (s s₀ : ℝ)
  (h_smooth : ContDiff ℝ ⊤ alpha)
  (h_arclength : ∀ t, ‖deriv alpha t‖ = 1)
  (h_theta_def : ∀ t, Real.cos (theta t) = inner (deriv alpha t) (deriv alpha s₀))
  (h_theta_diff : DifferentiableAt ℝ theta s) :
  deriv theta s = ‖deriv (deriv alpha) s‖ := by
  sorry



theorem theorem_542290_problem (f : ℂ → ℂ) (hf : Differentiable ℂ f) 
  (K : Set ℂ) (hK : IsCompact K) :
  ∃ M > 0, ∀ z ∈ K, ‖f z‖ ≤ M := by
  sorry

theorem theorem_542446_problem
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (lam mu : E →ₗ[ℝ] F)
  (h_lim : ∀ x : E, x ≠ 0 → Filter.Tendsto (fun h => ‖lam h - mu h‖ / ‖h‖) (nhdsWithin 0 {0}ᶜ) (nhds 0)) :
  ∀ x, lam x = mu x := by
  sorry

theorem theorem_541957_problem {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (u v : V) :
  4 * inner u v = (‖u + v‖ ^ 2 : ℂ) - (‖u - v‖ ^ 2 : ℂ) +
    I * (‖u + I • v‖ ^ 2 : ℂ) - I * (‖u - I • v‖ ^ 2 : ℂ) := by
  sorry



theorem theorem_542575_problem {α : Type} (P : α → Prop) 
  (h : ¬ (∀ x, P x)) : 
  ¬ (∀ y, P y) := by
  sorry

theorem theorem_541875_problem :
  let h : ℝ → ℝ × ℝ := fun t ↦ (Real.cos t, Real.sin t)
  let α : (ℝ × ℝ) → (ℝ × ℝ) → ℝ := fun p v ↦ p.1 * v.1
  let β : (ℝ × ℝ) → (ℝ × ℝ) → ℝ := fun p v ↦ p.2 * v.2
  let x : (ℝ × ℝ) → ℝ := fun p ↦ p.1
  let y : (ℝ × ℝ) → ℝ := fun p ↦ p.2
  ∀ t : ℝ,
    -- Pullback of α applied to d/dt (represented by scalar 1)
    α (h t) (fderiv ℝ h t 1) = - Real.cos t * Real.sin t ∧
    -- Pullback of β applied to d/dt
    β (h t) (fderiv ℝ h t 1) = Real.sin t * Real.cos t ∧
    -- Pullback of coordinate functions
    x (h t) = Real.cos t ∧
    y (h t) = Real.sin t := by
  sorry





theorem theorem_541971_problem
  (n : ℕ) (a b x : ℝ)
  (I : ℕ → ℝ → ℝ)
  (hn : n > 0)
  (hb : b ≠ 0)
  (h_denom : a + b * Real.sin x ≠ 0)
  (h_deriv : ∀ k, HasDerivAt (I k) (1 / (a + b * Real.sin x) ^ k) x) :
  (1 - (n : ℝ)) * I (n - 1) x =
    (1 - 2 * (n : ℝ)) * a * I n x -
    (b * Real.cos x) / (a + b * Real.sin x) ^ n -
    (n : ℝ) * b ^ 2 * (1 - a ^ 2 / b ^ 2) * I (n + 1) x := by
  sorry





theorem theorem_541431_problem
  (L f_val ε h : ℝ)
  (h_h : 0 < h)
  (h_f : 0 ≤ f_val)
  (h_ε : 0 ≤ ε)
  (h_L : 0 ≤ L)
  (δ : Fin 5 → ℝ)
  -- The error in each evaluation f(x_0+kh) is bounded by L|f(x_0)|ε
  (h_delta : ∀ i, |δ i| ≤ L * f_val * ε)
  (E : ℝ)
  -- The error term derived from the 5-point numerical differentiation stencil
  (h_E : E = (-25 * δ 0 + 48 * δ 1 - 36 * δ 2 + 16 * δ 3 - 3 * δ 4) / (12 * h))
  -- The assumption of "no critical cancellation" implies the error is half the naive worst-case bound
  -- Naive sum of absolute coefficients: 25 + 48 + 36 + 16 + 3 = 128
  (h_no_critical_cancellation : |E| ≤ (1 / 2) * ((25 + 48 + 36 + 16 + 3) * (L * f_val * ε) / (12 * h))) :
  |E| ≤ (16 * L * f_val * ε) / (3 * h) := by
  sorry

theorem theorem_542215_problem (a b c d e f : ℝ)
  (h : a * b + c * d + e * f = 0) :
  (a + b)^2 + (c + d)^2 + (e + f)^2 = (a - b)^2 + (c - d)^2 + (e - f)^2 := by
  sorry



theorem theorem_542860_problem :
  ∃ (X : Type) (S : Set X) (hS : S.Finite) (h_card : 1 < S.ncard) (m1 m2 : MetricSpace X),
    let d1 := @dist X m1.toPseudoMetricSpace.toDist
    let diam1 := @Metric.diam X m1.toPseudoMetricSpace S
    let pairs1 := {p : X × X | p.1 ∈ S ∧ p.2 ∈ S ∧ d1 p.1 p.2 = diam1}
    let d2 := @dist X m2.toPseudoMetricSpace.toDist
    let diam2 := @Metric.diam X m2.toPseudoMetricSpace S
    let pairs2 := {p : X × X | p.1 ∈ S ∧ p.2 ∈ S ∧ d2 p.1 p.2 = diam2}
    pairs1 ≠ pairs2 := by
  sorry

theorem theorem_542876_problem (x y : ℝ → ℝ)
  (h1 : ∀ t, HasDerivAt x (x t) t)
  (h2 : ∀ t, HasDerivAt y (-y t + (x t) ^ 2) t)
  (h3 : ∀ t, x t ≠ 0) :
  ∃ C : ℝ, ∀ t, y t = C / x t + (x t) ^ 2 / 3 := by
  sorry



theorem theorem_542891_problem 
  (r : ℝ → EuclideanSpace ℝ (Fin 3))
  (L : ℝ → EuclideanSpace ℝ (Fin 3))
  (h_diff : ContDiff ℝ 2 r)
  (h_L : ∀ t, L t = crossProduct (r t) (deriv r t))
  (h_central : ∀ t, crossProduct (r t) (deriv (deriv r) t) = 0) :
  ∀ t, deriv L t = 0 := by
  sorry



theorem theorem_543271_problem (V : Submodule ℝ (Polynomial ℝ))
  (hV : V = Submodule.span ℝ ({1, X, X^2} : Set (Polynomial ℝ))) :
  ¬ (∀ p q : Polynomial ℝ, p ∈ V → q ∈ V → p * q ∈ V) := by
  sorry

theorem theorem_543358_problem
  (E : Set ℝ)
  (hE : MeasurableSet E)
  (F : Set (ℝ × ℝ))
  (hF : F = {p : ℝ × ℝ | p.1 - p.2 ∈ E}) :
  MeasurableSet F := by
  sorry





theorem theorem_542939_problem (G : Type*) [Group G] (x : G)
  (h : ∀ (M : Subgroup G),
    (IsCyclic M ∧ (∀ (K : Subgroup G), IsCyclic K → M ≤ K → M = K)) → x ∈ M) :
  x ∈ Subgroup.center G := by
  sorry

theorem theorem_543764_problem (a : ℕ → ℝ) (H : ℕ → ℝ)
  (hH : ∀ n, H n = ∑ k in Finset.Icc 1 n, (1 : ℝ) / k)
  (h0 : a 0 = 0)
  (h_rec : ∀ n : ℕ, a (n + 1) / (Nat.factorial (n + 1) : ℝ) = 
                    a n / (Nat.factorial n : ℝ) + 1 / (n + 1 : ℝ)) :
  ∀ n, 1 ≤ n → a n = (Nat.factorial n : ℝ) * H n := by
  sorry

theorem theorem_543598_problem
  {G : Type u} [Group G]
  (N : Subgroup G) [N.Normal]
  (P : Type u → Prop)
  (hP_ext : ∀ (K : Type u) [Group K] (L : Subgroup K) [L.Normal], P L → P (K ⧸ L) → P K)
  (hN_P : P N)
  (hN_max : ∀ (M : Subgroup G) [M.Normal], P M → M ≤ N) :
  ∀ (H : Subgroup (G ⧸ N)) [H.Normal], P H → H = ⊥ := by
  sorry

theorem theorem_543400_problem
  {X : Type*}
  (T1 T2 : TopologicalSpace X)
  (B1 B2 : Set (Set X))
  (hB1 : @TopologicalSpace.IsTopologicalBasis X T1 B1)
  (hB2 : @TopologicalSpace.IsTopologicalBasis X T2 B2)
  (h_cond : ∀ x : X, ∀ b1 ∈ B1, x ∈ b1 → ∃ b2 ∈ B2, x ∈ b2 ∧ b2 ⊆ b1) :
  T1 ≤ T2 := by
  sorry

theorem theorem_543523_problem (F : Type*) [Field F] [Fintype F] (h : Fintype.card F = 4) :
  ∃ ϕ : Fˣ ≃ ZMod 3, ∀ x y : Fˣ, ϕ (x * y) = ϕ x + ϕ y := by
  sorry









