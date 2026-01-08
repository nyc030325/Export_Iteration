import Mathlib
import Mathlib.Tactic



theorem theorem_917717_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → E) (x₀ : E)
  (h_diff : ContDiff ℝ 1 f)
  (h_root : f x₀ = 0)
  (h_inv : IsUnit (fderiv ℝ f x₀)) :
  ∃ δ > 0, ∃ C > 0, ∀ x, ‖x - x₀‖ < δ →
    ∃ (f'inv : E →L[ℝ] E),
      f'inv ∘L (fderiv ℝ f x) = 1 ∧
      ‖x - f'inv (f x) - x₀‖ ≤ C * ‖x - x₀‖ ^ 2 := by
  sorry





theorem theorem_917837_problem
  (f : ℝ × ℝ → ℝ)
  (g : ℝ → ℝ)
  (hf : Differentiable ℝ f)
  (hg : Differentiable ℝ g) :
  ∀ t : ℝ, deriv (fun t => f (t, g t)) t = 
    deriv (fun x => f (x, g t)) t + deriv (fun y => f (t, y)) (g t) * deriv g t := by
  sorry







theorem theorem_918282_problem (n : ℤ) (h : n ≡ 1 [ZMOD 15]) : n % 15 = 1 := by
  sorry

theorem theorem_917693_problem (x y z : ℤ)
  (h : x^3 = 2 * y^3 + 4 * z^3) :
  x = 0 ∧ y = 0 ∧ z = 0 := by
  sorry











theorem theorem_918593_problem
  (f u : ℝ → ℝ)
  (x : ℝ)
  (hf : DifferentiableAt ℝ f x)
  (hu : DifferentiableAt ℝ u (f x))
  (h : deriv f x = u (f x)) :
  deriv (fun t => (u t)^2) (f x) = 2 * u (f x) * deriv u (f x) := by
  sorry

theorem theorem_918258_problem (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (p : EuclideanSpace ℝ (Fin n))
  (h_smooth : ContDiff ℝ ⊤ f)
  (h_nz : ‖f p‖ ≠ 0) :
  gradient (fun x => ‖f x‖) p = (‖f p‖)⁻¹ • fderiv ℝ f p (f p) := by
  sorry















theorem theorem_918989_problem
  {X : Type*} [MetricSpace X]
  (x : ℕ → X)
  (h : ∀ (φ : ℕ → ℕ), StrictMono φ → ¬ ∃ (l : X), Filter.Tendsto (x ∘ φ) Filter.atTop (nhds l)) :
  IsClosed (Set.range x) := by
  sorry









theorem theorem_919126_problem (n : ℕ) (v w : EuclideanSpace ℝ (Fin n))
  (hv : v ≠ 0) (hw : w ≠ 0) :
  InnerProductGeometry.angle v w = Real.arccos (inner v w / (‖v‖ * ‖w‖)) := by
  sorry



theorem theorem_919678_problem (x : ℝ) (h : |x| < 1) :
  Real.log ((1 + x) / (1 - x)) = 2 * ∑' k : ℕ, x ^ (2 * k + 1) / (2 * k + 1) := by
  sorry



theorem theorem_918872_problem
  (f g : ℝ → ℝ)
  (C₁ C₂ : ℝ)
  (hfg : f = g)
  (hC₁ : C₁ = ∫ y in (0 : ℝ)..(1 : ℝ), y * f y)
  (hC₂ : C₂ = ∫ y in (0 : ℝ)..(1 : ℝ), y^2 * f y)
  (heq : ∀ x, x^3 + (1 : ℝ) / 6 * x^2 + (1 : ℝ) / 5 * x = 
    g x + ∫ y in (0 : ℝ)..(1 : ℝ), (x^2 * y + x * y^2) * f y) :
  ∀ x, g x = x^3 - (38 : ℝ) / 1077 * x^2 + (58 : ℝ) / 1795 * x := by
  sorry

theorem theorem_919155_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (T : E →L[ℝ] E)
  (h : ∃ (N k : ℕ) (Ck : ℝ), N > 0 ∧ k ≥ 1 ∧ Ck > 0 ∧
    Ck / (N : ℝ) ^ k < 1 ∧ ‖T ^ N‖ ≤ Ck / (N : ℝ) ^ k) :
  ∃ M ω : ℝ, M > 0 ∧ ω > 0 ∧ ∀ n : ℕ, ‖T ^ n‖ ≤ M * Real.exp (-ω * n) := by
  sorry



theorem theorem_919329_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (a' b' : E) (x' : ℝ) (h_ne : a' ≠ b') :
  let d := b' - a'
  let v := a' + x' • (‖d‖⁻¹ • d)
  v = a' + x' • (‖b' - a'‖⁻¹ • (b' - a')) := by
  sorry



theorem theorem_919944_problem (z : ℂ) (θ : ℝ)
  (hz : z ≠ 0)
  (h_arg : -Real.pi < θ ∧ θ < Real.pi)
  (h_z : z = ↑(Complex.abs z) * Complex.exp (↑θ * Complex.I)) :
  Complex.log z = ↑(Real.log (Complex.abs z)) + ↑θ * Complex.I := by
  sorry



theorem theorem_918048_problem
  {K : Type*} [Field K]
  {G : Type*} [TopologicalSpace G] [Group G] [TopologicalGroup G] [LocallyCompactSpace G]
  {H : Subgroup G} (hH : IsClosed (H : Set G))
  {V : Type*} [AddCommGroup V] [Module K V] [TopologicalSpace V] [FiniteDimensional K V]
  (ρ : H →* (V →L[K] V))
  (Cc : Set (G → V))
  (hCc : Cc = { f : G → V | Continuous f ∧ HasCompactSupport f ∧ ∀ (h : H) (g : G), f (h * g) = ρ h (f g) })
  (action : G → (G → V) → (G → V))
  (h_action : ∀ g f x, action g f x = f (g⁻¹ * x)) :
  (∀ g, ∀ f ∈ Cc, action g f ∈ Cc) ∧
  (∀ g₁ g₂, ∀ f ∈ Cc, action (g₁ * g₂) f = action g₁ (action g₂ f)) := by
  sorry

theorem theorem_920173_problem (n : ℕ) (h_pos : 0 < n)
  (leave_night : ℕ → ℕ)
  (h_base : leave_night 1 = 1)
  (h_step : ∀ k, 0 < k → leave_night (k + 1) = leave_night k + 1) :
  leave_night n = n := by
  sorry



theorem theorem_919671_problem (f : (Fin 3 → ℝ) → ℝ)
  (h_poly : ∃ p : MvPolynomial (Fin 3) ℝ, ∀ x, f x = MvPolynomial.eval x p) :
  ¬ Function.Injective f := by
  sorry











theorem theorem_920330_problem (n : ℕ) :
  ∫ x in (0 : ℝ)..(Real.pi / 4), (x ^ 4 - 1) ^ n =
  ∑ k in Finset.range (n + 1), (n.choose k : ℝ) * (-1) ^ (n - k) *
    ((Real.pi / 4) ^ (4 * k + 1) / (4 * k + 1 : ℝ)) := by
  sorry



theorem theorem_920005_problem
  (n m : ℕ)
  (f : (Fin n → ℝ) → ℝ)
  (g : Fin m → (Fin n → ℝ) → ℝ)
  (D : Set (Fin n → ℝ))
  (hf : ConvexOn ℝ D f)
  (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
  (lam : Fin m → ℝ)
  (x_star : Fin n → ℝ)
  (h_x_dom : x_star ∈ D)
  (h_lam_nonneg : ∀ i, 0 ≤ lam i)
  (h_feasible : ∀ i, g i x_star ≤ 0)
  (h_min_L : ∀ x ∈ D, f x_star + ∑ i, lam i * g i x_star ≤ f x + ∑ i, lam i * g i x) :
  ∀ x ∈ D, (∀ i, g i x ≤ 0) → f x_star ≤ f x := by
  sorry











theorem theorem_920139_problem (k : ℕ) (q x : ℝ)
  (hk : 1 ≤ k) (hq : 0 ≤ q) (hx : 0 ≤ x) :
  ((Real.sqrt q + Real.sqrt x) ^ (2 ^ k) + (Real.sqrt q - Real.sqrt x) ^ (2 ^ k)) / 2 =
  ∑ n in Finset.range (2 ^ (k - 1) + 1), (Nat.choose (2 ^ k) (2 * n) : ℝ) * q ^ (2 ^ (k - 1) - n) * x ^ n := by
  sorry

theorem theorem_920376_problem (n : ℕ) (hp : Nat.Prime n) :
  ∃ m : ℕ, (m : ℚ) = ∑ k in Finset.Ico 1 ((n - 1) / 2 + 1), 
    (1 / ((n : ℚ) - (k : ℚ))) * (Nat.choose (n - k) k : ℚ) := by
  sorry

theorem theorem_921076_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (F_eta F_x : ℝ → ℝ → V)
  (t dt : ℝ → ℝ)
  (g : ℝ → V)
  (C : ℝ)
  (hC : 0 < C)
  -- The derivative of g is given by the chain rule formula implied by the problem setup
  (hg : ∀ η, HasDerivAt g (F_eta η (t η) + dt η • F_x η (t η)) η)
  -- The functions satisfy the given nonlinear ODE
  (h_ode : ∀ η, ‖F_eta η (t η)‖^2 + 2 * inner (F_eta η (t η)) (F_x η (t η)) * dt η + 
    ‖F_x η (t η)‖^2 * (dt η)^2 = C^2) :
  -- The curve has constant speed C
  ∀ η, ‖deriv g η‖ = C := by
  sorry





theorem theorem_920824_problem (f : ℝ → ℝ)
  (h_cauchy : ∀ x y, f (x + y) = f x + f y)
  (h_cont : ∃ x₀, ContinuousAt f x₀)
  (h_bound : ∃ a b : ℝ, a < b ∧ ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
  ∃ c, ∀ x, f x = c * x := by
  sorry



theorem theorem_921368_problem (n : ℕ) :
  let Z_plus : Set ℤ := {z | z > 0}
  let is_Z_plus_func (f : Set (ℕ × ℤ)) (domain_set : Set ℕ) := 
    (∀ x y₁ y₂, (x, y₁) ∈ f → (x, y₂) ∈ f → y₁ = y₂) ∧ 
    ({x | ∃ y, (x, y) ∈ f} = domain_set) ∧
    (∀ p ∈ f, p.2 ∈ Z_plus)
  let Z_n := {f : Set (ℕ × ℤ) | is_Z_plus_func f {i | 1 ≤ i ∧ i ≤ n}}
  let Z_inf := {f : Set (ℕ × ℤ) | is_Z_plus_func f {i | 1 ≤ i}}
  Z_n ∩ Z_inf = ∅ := by
  sorry



theorem theorem_921158_problem (f : ℝ × ℝ × ℝ → ℝ)
  (hf : Differentiable ℝ f)
  (h_pde : ∀ v : ℝ × ℝ × ℝ, fderiv ℝ f v (3, v.1, 2 * v.2.1) = 0) :
  ∃ F : ℝ × ℝ → ℝ, ∀ v : ℝ × ℝ × ℝ,
    f v = F (v.2.1 - v.1 ^ 2 / 6, v.2.2 + 2 * v.1 ^ 3 / 27 - 2 * v.1 * v.2.1 / 3) := by
  sorry

theorem theorem_921330_problem
  (Λ : ℂ → ℂ)
  (h_eq : ∀ s : ℂ, Λ s = star (Λ (1 - star s)))
  (Z : ℝ → ℂ)
  (hZ : ∀ t : ℝ, Z t = Λ (1 / 2 + (t : ℂ) * Complex.I)) :
  ∀ t : ℝ, (Z t).im = 0 := by
  sorry

theorem theorem_921098_problem 
  (g : ℝ → ℝ) 
  (α : ℝ) 
  (f : ℝ → ℝ → ℝ)
  (hf : ∀ x y, 0 < x → 0 < y → 
    f x y = if x = 1 ∧ y = 1 then 1 
            else if x ≠ 1 then x ^ (g (y ^ (1 / Real.logb 2 x))) 
            else y ^ α) :
  ∀ x y t, 0 < x → 0 < y → t ≠ 0 → 
  (f (x ^ (1 / t)) (y ^ (1 / t))) ^ t = f x y := by
  sorry

theorem theorem_921564_problem
  (n : ℕ)
  (X : Type*)
  (x : Fin n → X)
  (p : Fin n → ℝ)
  (A B : X → ℝ) :
  ∃! y : Fin n → ℝ, ∀ i, y i = A (x i) - ∑ j in Finset.univ.filter (fun j => p j < p i), B (x j) := by
  sorry

theorem theorem_921705_problem {V : Type} [Nonempty V] (R : V → V → Prop) :
  Symmetric R ↔ (∀ u v : V, R u v → R v u) := by
  sorry



theorem theorem_921815_problem (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (hk0 : 1 ≤ k) :
  k * Nat.choose n k = n * Nat.choose (n - 1) (k - 1) := by
  sorry



theorem theorem_921512_problem (A : ℕ → ℕ → ℤ)
  (h0 : ∀ m, A 0 m = 0)
  (h1 : ∀ m, A 1 m = if m = 0 then 1 else 0)
  (h_rec : ∀ n m, n ≥ 2 →
    A n m = A (n - 1) m + (if m > 0 then A (n - 1) (m - 1) else 0) +
            A (n - 2) m - (if m > 0 then A (n - 2) (m - 1) else 0)) :
  ∀ n m, n ≥ 1 → A n m = ∑ k in Finset.Icc m (n - 1 - m), ((Nat.choose k m : ℤ) * (Nat.choose (n - 1 - k) (k - m))) := by
  sorry



theorem theorem_921249_problem {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (n : ℕ) (hn : n > 0) (hn_le : n ≤ Fintype.card V) :
  let S_n := {U : Finset V | U.card = n}
  let C_n := {H : G.Subgraph | ∃ U ∈ S_n, H.verts = ↑U ∧ H.IsInduced ∧ H.Connected}
  C_n = {H : G.Subgraph | H.verts.ncard = n ∧ H.IsInduced ∧ H.Connected} := by
  sorry







theorem theorem_921903_problem
  (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
  -- The problem implies an identification of y ∈ V as a functional to make α_x(y) valid.
  (identify : V → Module.Dual F V)
  -- The natural identification of V with V''
  (alpha : V → Module.Dual F (Module.Dual F V))
  (h_alpha : ∀ (x : V) (f : Module.Dual F V), alpha x f = f x)
  -- The bracket operation definition
  (bracket : V → V → F)
  (h_bracket : ∀ x y, bracket x y = (alpha x) (identify y)) :
  -- The conclusion
  ∀ x y, bracket x y = bracket y x := by
  sorry

theorem theorem_922131_problem (k : Type*) [Field k] :
  ¬ Module.Free (Polynomial k) (LaurentPolynomial k) := by
  sorry

theorem theorem_922340_problem (p q n e m1 c1 d' : ℕ)
  (hp : p.Prime)
  (hq : q.Prime)
  (hn : n = p * q)
  (h_coprime : Nat.Coprime e (Nat.lcm (p - 1) (q - 1)))
  (h_c1 : c1 ≡ m1 ^ e [MOD n])
  (h_check : c1 ^ d' ≡ m1 [MOD n]) :
  e * d' ≡ 1 [MOD Nat.lcm (p - 1) (q - 1)] := by
  sorry





theorem theorem_922731_problem (V W : Type*)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] :
  IsOpen { f : V →L[ℝ] W | Function.Bijective f } := by
  sorry

theorem theorem_922374_problem
  {I : Type*}
  {X : I → Type*}
  [∀ i, TopologicalSpace (X i)]
  (A : (i : I) → Set (X i))
  (hA : ∀ i, (A i).Nonempty) :
  closure (Set.pi Set.univ A) = Set.pi Set.univ (fun i => closure (A i)) := by
  sorry







theorem theorem_922502_problem
  {X : Type*}
  (d ρ : MetricSpace X)
  (h : d.toUniformSpace.toTopologicalSpace ≠ ρ.toUniformSpace.toTopologicalSpace) :
  d.toUniformSpace ≠ ρ.toUniformSpace := by
  sorry













theorem theorem_922833_problem (h k l S : ℤ)
  (hS : S = (-1 : ℤ)^(h + k).natAbs + (-1)^(h + l).natAbs + (-1)^(h + h).natAbs + 1) :
  S = 0 ↔ (Odd h ∧ Even k ∧ Even l) ∨ (Even h ∧ Odd k ∧ Odd l) := by
  sorry

theorem theorem_923699_problem :
  ¬ Summable (fun n : ℕ => if 2 ≤ n then 1 / ((n : ℝ) * Real.log n) else 0) := by
  sorry



