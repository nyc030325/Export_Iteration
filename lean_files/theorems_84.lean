import Mathlib
import Mathlib.Tactic

















theorem theorem_453532_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  (A : V →ₗ[K] W) :
  FiniteDimensional.finrank K (LinearMap.range (LinearMap.dualMap A)) =
  FiniteDimensional.finrank K (Submodule.dualAnnihilator (LinearMap.ker A)) := by
  sorry









theorem theorem_453526_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (U : Submodule F V) :
  FiniteDimensional.finrank F U + FiniteDimensional.finrank F (Submodule.dualAnnihilator U) =
  FiniteDimensional.finrank F V := by
  sorry



theorem theorem_453521_problem
  (a b c d k : ℝ)
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0)
  (hd : d ≠ 0)
  (x₁ x₂ : ℝ)
  (hx₁ : x₁ = (-b + Real.sqrt (b^2 - 4 * a * c)) / (2 * a))
  (hx₂ : x₂ = (-b - Real.sqrt (b^2 - 4 * a * c)) / (2 * a))
  (x y : ℝ)
  (h_eqn : a * x^2 + b * x + c = 0)
  (h_y : y = d * x + k) :
  y = d * x₁ + k ∨ y = d * x₂ + k := by
  sorry

























theorem theorem_454082_problem
  (V1 V2 V3 : Type*) [Fintype V1] [Fintype V2] [Fintype V3]
  (A : Matrix V1 V2 Bool)
  (B : Matrix V2 V3 Bool)
  (C : Matrix V1 V3 Bool)
  (hC : ∀ (i : V1) (j : V3), C i j = true ↔ ∃ (k : V2), A i k = true ∧ B k j = true) :
  Finset.card (Finset.filter (fun (p : V1 × V3) => ∃ (k : V2), A p.1 k = true ∧ B k p.2 = true) Finset.univ) =
  Finset.card (Finset.filter (fun (p : V1 × V3) => C p.1 p.2 = true) Finset.univ) := by
  sorry

theorem theorem_453733_problem (n : ℕ) (x : Fin n → ℝ) :
  sSup {y : ℝ | ∃ v : Fin n → ℝ, (∑ i, |v i|) ≤ 1 ∧ y = ∑ i, v i * x i} = 
  ⨆ i, |x i| := by
  sorry

theorem theorem_453732_problem
  (n m : ℕ)
  (A : Matrix (Fin n) (Fin m) ℝ)
  (ylag : Matrix (Fin m) (Fin 1) ℝ)
  (h : Matrix (Fin n) (Fin 1) ℝ)
  (P : Matrix (Fin n) (Fin n) ℝ)
  (hP : P = A * ylag * h.transpose) :
  ∃ D : Matrix (Fin n) (Fin n) ℝ, D = Matrix.diagonal P.diag := by
  sorry













theorem theorem_454276_problem (F : Type*) [Field F]
  (h : Group.FG (Units F)) :
  Finite F := by
  sorry



theorem theorem_455208_problem (m n : ℕ) (a b : ℝ) (h : a ≠ b) :
  ∫ x in a..b, (x - a) ^ m * (x - b) ^ n =
  ((-1 : ℝ) ^ (m + 1)) *
  ((m.factorial * n.factorial : ℝ) / (m + n + 1).factorial) *
  ((a - b) ^ (m + n + 1)) := by
  sorry





theorem theorem_455090_problem (c : ℝ) (hc : c ≠ 0)
  (f : ℝ → ℝ) (hf : f = fun u ↦ |u + c|)
  (u : ℝ) (hu : u ≠ -c) :
  deriv f u = Real.sign (u + c) := by
  sorry

theorem theorem_455805_problem
  (I : ℝ → ℝ)
  (hI : ∀ x, I x = ∫ ϕ in -Real.pi..Real.pi, Real.exp (x * Real.cos ϕ)) :
  Filter.Tendsto (fun x ↦ I x / (Real.sqrt (2 * Real.pi) * Real.exp x * x ^ (-(1 / 2 : ℝ)))) Filter.atTop (nhds 1) := by
  sorry

theorem theorem_455290_problem
  (u : ℝ → ℝ → ℝ)
  (a : ℝ → ℝ → ℝ)
  (phi : ℝ → ℝ)
  (x : ℝ → ℝ)
  (x₀ : ℝ)
  -- Assumption of differentiability to ensure the derivatives are well-defined and chain rule applies
  (h_diff_u : ContDiff ℝ 1 (Function.uncurry u))
  (h_diff_x : Differentiable ℝ x)
  -- The PDE: u_t + a * u_x = 0
  (h_pde : ∀ y t, deriv (fun t' => u y t') t + a y t * deriv (fun y' => u y' t) y = 0)
  -- The Initial Condition for u
  (h_ic_u : ∀ y, u y 0 = phi y)
  -- The Characteristic ODE
  (h_ode : ∀ t, deriv x t = a (x t) t)
  -- The Initial Condition for the characteristic curve
  (h_ic_x : x 0 = x₀) :
  -- The solution along the characteristic
  ∀ t, u (x t) t = phi x₀ := by
  sorry

theorem theorem_455244_problem (s : ℕ) (p : Fin s → ℕ)
  (h_prime : ∀ i, Nat.Prime (p i))
  (h_ne_3 : ∀ i, p i ≠ 3)
  (P : ℕ)
  (hP : P = 7 * ∏ i, p i)
  (q : ℕ)
  (hq : Nat.Prime q)
  (h_div : q ∣ P + 3) :
  ¬ q ∣ P := by
  sorry

theorem theorem_455446_problem
  {X : Type*} [MetricSpace X] [CompactSpace X]
  (f : X → ℝ) (hf : Continuous f) :
  UniformContinuous f := by
  sorry

theorem theorem_455707_problem (n : ℕ) (C : ℕ → ℕ)
  (h_base : C 0 = 1)
  (h_step : ∀ k, C (k + 1) = 2 * C k) :
  C n = 2^n := by
  sorry

theorem theorem_455644_problem (E : Set ℝ) (p : ℝ)
  (hp_cl : p ∈ closure E) (hp_notin : p ∉ E) :
  ∃ f : E → ℝ, Continuous f ∧
  (∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) ∧
  ¬ ∃ l : ℝ, Filter.Tendsto f (Filter.comap Subtype.val (nhds p)) (nhds l) := by
  sorry



theorem theorem_454997_problem (n : ℕ) (F : Type*) (P : ℕ → F → Prop) :
  (∃ f : F, ∀ g : F, P n f ∧ P n g) ↔ ((∃ f : F, P n f) ∧ (∀ g : F, P n g)) := by
  sorry





theorem theorem_455682_problem
  (n g k : ℕ)
  (x : ℕ → ℝ)
  (sizes : Fin g → ℕ)
  (cum_sizes : Fin (g + 1) → ℕ)
  (h_n_pos : n > 0)
  (h_sizes_pos : ∀ i, sizes i > 0)
  (h_cum_0 : cum_sizes 0 = 0)
  (h_cum_step : ∀ i : Fin g, cum_sizes i.castSucc + sizes i = cum_sizes i.succ)
  (h_cum_n : cum_sizes (Fin.last g) = n) :
  (∑ i in Finset.Ioc 0 n, x i ^ k) / (n : ℝ) =
  (1 / (n : ℝ)) * ∑ i : Fin g, (sizes i : ℝ) *
    ((∑ m in Finset.Ioc (cum_sizes i.castSucc) (cum_sizes i.succ), x m ^ k) / (sizes i : ℝ)) := by
  sorry

theorem theorem_455855_problem
  {I : Type*} [TopologicalSpace I] [CompactSpace I]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (j : X ≃ₗ[ℝ] C(I, ℝ))
  (χ : X) (hχ : ‖χ‖ = 1)
  (h_norm : ∀ f : X, ‖f‖ ≤ ‖χ‖ * ‖j f‖) :
  Continuous j := by
  sorry







theorem theorem_455484_problem
  (a b : ℝ)
  (f g : ℝ → ℝ)
  (n : ℕ)
  (x : ℕ → ℝ)
  (ξ : ℕ → ℝ)
  (h_ab : a < b)
  (h_f_bdd : BddAbove (Set.image (fun t => |f t|) (Set.Icc a b)))
  (h_g_bdd : BddAbove (Set.image (fun t => |g t|) (Set.Icc a b)))
  (c : ℝ)
  (hc : c ∈ Set.Icc a b)
  (h_diff : ∀ z ∈ Set.Icc a b, z ≠ c → f z = g z)
  (hx0 : x 0 = a)
  (hxn : x n = b)
  (hx_mono : ∀ i, i < n → x i ≤ x (i + 1))
  (hξ : ∀ i, i < n → ξ i ∈ Set.Icc (x i) (x (i + 1))) :
  let P_norm := sSup ((Finset.range n).image (fun i => x (i + 1) - x i) : Set ℝ)
  let S_f := ∑ i in Finset.range n, f (ξ i) * (x (i + 1) - x i)
  let S_g := ∑ i in Finset.range n, g (ξ i) * (x (i + 1) - x i)
  let M := sSup (Set.image (fun t => |f t| + |g t|) (Set.Icc a b))
  |S_f - S_g| ≤ 2 * P_norm * M := by
  sorry



theorem theorem_456019_problem
  (Divisor : Type*) [AddGroup Divisor]
  (K : Divisor)
  (sq : Divisor → ℤ)
  (Ample : Divisor → Prop)
  (h_nakai : ∀ D, Ample D → sq D > 0)
  (h_rat_ell : sq K = 0)
  (h_sq_neg : ∀ D, sq (-D) = sq D) :
  ¬ Ample (-K) := by
  sorry















theorem theorem_456065_problem
  (V : ℝ × ℝ → ℝ)
  (f : ℝ × ℝ → ℝ × ℝ)
  (D : Set (ℝ × ℝ))
  (flow : ℝ → ℝ × ℝ → ℝ × ℝ)
  -- Conditions on the function V
  (hV_diff : ContDiff ℝ 1 V)
  -- Conditions on the region D
  -- D is a region (open) containing the origin in its closure (boundary), excluding boundary from interior
  (hD_open : IsOpen D) 
  (hD_origin : 0 ∈ frontier D)
  -- V > 0 in D
  (hV_pos : ∀ x ∈ D, V x > 0)
  -- V = 0 on boundary of D and at the origin
  (hV_bd : ∀ x ∈ frontier D, V x = 0)
  (hV_zero : V 0 = 0)
  -- Dynamical system conditions (f is the vector field, flow is the trajectory)
  (hf_diff : ContDiff ℝ 1 f)
  (hf_eq : f 0 = 0) -- Origin is an equilibrium
  (h_flow_deriv : ∀ t x, HasDerivAt (λ s ↦ flow s x) (f (flow t x)) t)
  (h_flow_init : ∀ x, flow 0 x = x)
  -- V_dot > 0 in D
  (hV_dot : ∀ x ∈ D, (fderiv ℝ V x) (f x) > 0) :
  -- Conclusion: The origin is an unstable equilibrium point
  -- (Negation of stability: It is not the case that for all ε, trajectories starting close stay close)
  ¬ (∀ ε > 0, ∃ δ > 0, ∀ x, ‖x‖ < δ → ∀ t ≥ 0, ‖flow t x‖ < ε) := by
  sorry

theorem theorem_456194_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  (A : X →L[𝕜] Y)
  (h : (⋃ n : ℕ, closure (A '' (Metric.closedBall 0 n))) = closure (Set.range A)) :
  Set.range A = closure (Set.range A) := by
  sorry



theorem theorem_456466_problem (K F K' : Type*)
  [Field K] [Field F] [Field K']
  [Algebra K K'] [Algebra K' F] [Algebra K F] [IsScalarTower K K' F]
  (h : ∃ a : K', IsAlgebraic K a ∧ IntermediateField.adjoin K {a} = ⊤) :
  ∀ x : F, IsAlgebraic K x → IsAlgebraic K' x := by
  sorry

theorem theorem_456530_problem (z : ℝ → ℝ → ℝ)
  (h1 : ∃ F : ℝ → ℝ, ∀ x y, z x y = F (x + x^2 / 2 - y^2 / 2))
  (h2 : ∀ x, z x 0 = x)
  (x y : ℝ) (hx : x ≥ 0) :
  z x y = -1 + Real.sqrt ((x + 1)^2 - y^2) := by
  sorry



theorem theorem_456770_problem
  (phi : ℕ → ℚ)
  (hphi : Function.Surjective phi)
  (psi : ℕ ≃ ℕ × ℕ)
  (a : ℚ → ℕ → ℝ)
  (ha : ∀ q : ℚ, Filter.Tendsto (a q) Filter.atTop (nhds (q : ℝ)))
  (b : ℕ → ℝ)
  (hb : ∀ n, b n = a (phi (psi n).1) (psi n).2) :
  ∀ q : ℚ, ∃ f : ℕ → ℕ, StrictMono f ∧ Filter.Tendsto (b ∘ f) Filter.atTop (nhds (q : ℝ)) := by
  sorry





theorem theorem_456465_problem
  (y x : Fin 4 → ℝ)
  (α : ℝ)
  (f : ℝ → ℝ)
  (β₁ β₂ : ℝ)
  (h_f : ∀ ε, f ε = α * ε)
  (h_norm : ∫ ε in (0 : ℝ)..1, f ε = 1)
  (h_pos : ∀ i, 0 < y i - β₁ - β₂ * x i)
  (h_le : ∀ i, y i - β₁ - β₂ * x i ≤ 1) :
  Real.log (∏ i, f (y i - β₁ - β₂ * x i)) =
    4 * Real.log 2 + ∑ i, Real.log (y i - β₁ - β₂ * x i) := by
  sorry





theorem theorem_456493_problem
  {X : Type*} [MetricSpace X]
  (p : ℕ → X)
  (h : ∀ n : ℕ, ∃ s : Finset X, (⋃ x ∈ s, Metric.ball x ((2 : ℝ) ^ (-(n : ℤ)))) = Set.univ) :
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (p ∘ φ) := by
  sorry

theorem theorem_457252_problem 
  (W p : ℕ → ℕ → ℝ) 
  (m : ℕ)
  (h_p : ∀ j k, p j k = (2 * k : ℝ) / (j ^ 2 : ℝ))
  (h_Wm : W m m = 1)
  (h_W_below : ∀ k, k < m → W k m = 0)
  (h_W_total : ∀ j, j > m → W j m = ∑ k in Finset.range j, p j k * W k m) :
  ∀ j, j > m → W j m = (∑ k in Finset.Ico (m + 1) j, p j k * W k m) + p j m * W m m := by
  sorry





theorem theorem_457137_problem (R : Type*) [CommRing R] :
  ∀ (M : Type*) [Monoid M] (A : Type*) [Ring A] [Algebra R A],
  Function.Bijective (fun (f : MonoidAlgebra R M →ₐ[R] A) =>
    f.toMonoidHom.comp (MonoidAlgebra.of R M)) := by
  sorry











theorem theorem_456915_problem
  {α : Type*} [DecidableEq α]
  (n : ℕ) (a : ℕ → α) (x : Equiv.Perm α) (i : ℕ)
  (hn : n > 0)
  (h_nodup : ((List.range n).map (fun k => a (n - k))).Nodup)
  (hx : x = List.formPerm ((List.range n).map (fun k => a (n - k))))
  (han1 : a (n + 1) = a 1)
  (ha0 : a 0 = a n)
  (hi_ge : 0 ≤ i)
  (hi_le : i ≤ n) :
  x (a i) = a (i + 1) := by
  sorry

theorem theorem_457832_problem
  {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (U V : H →L[𝕜] H)
  (hU : IsSelfAdjoint U)
  (hV : IsSelfAdjoint V)
  (hComm : Commute U V) :
  IsSelfAdjoint (U * V) := by
  sorry



theorem theorem_457541_problem
  (X : Type*) [LinearOrder X]
  (X_xi : X → Set X)
  (h_X_xi : ∀ ξ, X_xi ξ = {x | x < ξ})
  (omega1 : Set X)
  (h_omega1 : omega1 = {a | (X_xi a).Countable})
  (Y : Set X)
  (h_Y : Y = ⋃ ξ ∈ omega1, X_xi ξ) :
  omega1 = Y := by
  sorry







theorem theorem_457614_problem
  (u F f : ℝ → ℝ → ℝ)
  (k : ℝ)
  (hk : k > 0)
  -- Condition: Fick's law
  (h_fick : ∀ x t, F x t = -k * deriv (fun y ↦ u y t) x)
  -- Condition: Conservation Law (Continuity Equation)
  -- Note: The problem implies the evolution is determined by the flux and source,
  -- which mathematically corresponds to the continuity equation: u_t = -F_x + f.
  (h_conservation : ∀ x t, deriv (fun s ↦ u x s) t = - deriv (fun y ↦ F y t) x + f x t) :
  -- Conclusion: The Partial Differential Equation
  ∀ x t, deriv (fun s ↦ u x s) t = k * deriv (fun y ↦ deriv (fun z ↦ u z t) y) x + f x t := by
  sorry





