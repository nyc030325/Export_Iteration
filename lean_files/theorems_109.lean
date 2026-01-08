import Mathlib
import Mathlib.Tactic









theorem theorem_589788_problem (p : ℕ) (hp : p.Prime)
  (a b : (ZMod p)ˣ)
  (h : b ∈ Subgroup.zpowers a) :
  ∃ x : ℤ, a ^ x = b := by
  sorry



theorem theorem_589767_problem
  (R : Type*) [CommRing R] [IsDomain R]
  (h_finite : ∀ (I : Ideal R), I ≠ ⊥ → Finite (R ⧸ I))
  (I J : Ideal R) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
  Nat.card (R ⧸ (I * J)) = Nat.card (R ⧸ I) * Nat.card (R ⧸ J) := by
  sorry

theorem theorem_590186_problem 
  {V : Type*} 
  (T1r T1t T2r T2t T3r T3t : V ≃ V)
  (v vt : V)
  (h : T3t (T3r (T2t (T2r (T1t (T1r v))))) = vt) :
  T1r.symm (T1t.symm (T2r.symm (T2t.symm (T3r.symm (T3t.symm vt))))) = v := by
  sorry

theorem theorem_589868_problem (X Y Z : Type*)
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  (f : X → Y) (g : Y → Z)
  (hf : Measurable f) (hg : Measurable g) :
  Measurable (g ∘ f) := by
  sorry





theorem theorem_589952_problem (n : ℕ) (t : Fin n → ℝ)
  (h_range : ∀ i, t i ∈ Set.Icc 0 1)
  (h_sum : ∑ i, t i = 1) :
  let f : (Fin n → ℂ) → ℂ := fun z ↦ ∑ i, (t i : ℂ) * z i
  IsLinearMap ℂ f ∧ Continuous f := by
  sorry









theorem theorem_590677_problem
  (f F : ℝ → ℝ)
  (θ : ℝ)
  (hf_pos : ∀ t > 0, 0 < f t)
  (hF_def : ∀ t > 0, F t = ∫ x in (0)..t, f x)
  (hθ_pos : 0 < θ)
  (h_ineq : ∀ t > 0, 0 ≤ θ * F t ∧ θ * F t < t * f t) :
  ∀ t > 0, f t > (θ / t) * F t := by
  sorry

theorem theorem_590888_problem :
  ∃ (G : Type*) (_ : Group G) (H : Subgroup G) (K : Subgroup H),
    K.Normal ∧ H.Normal ∧ ¬ (K.map H.subtype).Normal := by
  sorry











theorem theorem_591140_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (u v w x : V)
  (c d e f : ℝ) :
  inner (c • u + d • v) (e • w + f • x) =
  c * e * inner u w + c * f * inner u x + d * e * inner v w + d * f * inner v x := by
  sorry

theorem theorem_590493_problem
  {F : Type*} [Field F]
  {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [FiniteDimensional F V] [FiniteDimensional F W]
  (T : V →ₗ[F] W)
  (h_dim : FiniteDimensional.finrank F V ≠ FiniteDimensional.finrank F W) :
  ∃ (B_V : Basis (Fin (FiniteDimensional.finrank F V)) F V)
    (B_W : Basis (Fin (FiniteDimensional.finrank F W)) F W),
    let r := FiniteDimensional.finrank F (LinearMap.range T)
    let M := LinearMap.toMatrix B_V B_W T
    ∀ i j, M i j = if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then 1 else 0 := by
  sorry

theorem theorem_591139_problem : ¬ ∃ e : ℕ → (ℕ → ℕ), Function.Bijective e := by
  sorry



theorem theorem_590392_problem (a : ℕ → ℕ → ℝ)
  (h_nonneg : ∀ j k, 0 ≤ a j k)
  (h_inner_conv : ∀ j, Summable (fun k ↦ a j k))
  (h_outer_conv : Summable (fun j ↦ ∑' k, a j k)) :
  ∑' (p : ℕ × ℕ), a p.1 p.2 = ∑' j, ∑' k, a j k := by
  sorry

theorem theorem_590365_problem (n : ℕ) (P : Type*) [Fintype P] [DecidableEq P] (hP : Fintype.card P = n) :
  let E : Set (P × P) := {p | p.1 ≠ p.2}
  let valid_schedule (k : ℕ) : Prop := ∃ S : Fin k → Set (P × P),
    (∀ r, S r ⊆ E) ∧
    (∀ p ∈ E, ∃! r, p ∈ S r) ∧
    (∀ r, ∀ p1 ∈ S r, ∀ p2 ∈ S r, p1 ≠ p2 → ({p1.1, p1.2} : Set P) ∩ {p2.1, p2.2} = ∅)
  let valid_ilp (k : ℕ) : Prop := ∃ x : P → P → Fin k → ℕ,
    (∀ i j, i ≠ j → ∑ r, x i j r = 1) ∧
    (∀ i r, ∑ j in Finset.univ.filter (· ≠ i), x i j r ≤ 1) ∧
    (∀ i j r, x i j r ∈ ({0, 1} : Set ℕ))
  sInf {k | valid_schedule k} = sInf {k | valid_ilp k} := by
  sorry











theorem theorem_591091_problem
  (n : ℕ)
  (det : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
  (O P Q R S_fixed : Fin n → ℝ)
  (S : ℝ → Fin n → ℝ)
  (line : Set (Fin n → ℝ))
  (h_distinct : P ≠ Q ∧ Q ≠ R ∧ P ≠ R)
  (h_on_line : P ∈ line ∧ Q ∈ line ∧ R ∈ line ∧ S_fixed ∈ line)
  (h_O_not_on_line : O ∉ line)
  (h_S_maps_to_line : ∀ t, S t ∈ line)
  (h_S_continuous : Continuous S)
  (h_S_injective : Function.Injective S)
  (h_denom_ne_zero : det O S_fixed R * det P S_fixed Q ≠ 0) :
  let ν := fun t ↦ (det O (S t) Q * det P (S t) R) / (det O S_fixed R * det P S_fixed Q)
  Function.Injective ν := by
  sorry

theorem theorem_591273_problem (P : ℕ → Prop)
  (h_base : P 0)
  (h_ind : ∀ n : ℕ, P n → P (Nat.succ n)) :
  ∀ n : ℕ, P n := by
  sorry







theorem theorem_591291_problem {X : Type*} [MetricSpace X] (h : ¬ CompactSpace X) :
  ∃ S : Set X, S.Infinite ∧ IsClosed S ∧ DiscreteTopology ↥S := by
  sorry

theorem theorem_591666_problem (b : ℤ)
  (h_pos : 0 < b)
  (h_ns : ¬ IsSquare b)
  (r : ℝ)
  (hr : r ^ 4 = (b : ℝ))
  (A : IntermediateField ℚ ℝ)
  (hA : A = IntermediateField.adjoin ℚ {r}) :
  ¬ Normal ℚ A := by
  sorry





theorem theorem_592041_problem :
  ∫⁻ (p : ℝ × ℝ), ENNReal.ofReal (1 / (1 + p.1^2 + p.2^2)) = ⊤ := by
  sorry

theorem theorem_591868_problem :
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
  (Nat.totient n : ℝ) ≥ (n : ℝ) / (Real.exp eulerMascheroniConstant * Real.log (Real.log n) + 3 / Real.log (Real.log n)) := by
  sorry





theorem theorem_592630_problem (w₀ w : ℂ)
  (h₁ : w₀ + Complex.I * w ≠ 0)
  (h₂ : w ≠ 0)
  (h₃ : w₀ ≠ 0) :
  Complex.arg (w₀ ^ 2 / (w * Complex.I * (w₀ + Complex.I * w))) =
  2 * Complex.arg w₀ - Complex.arg w - Real.pi / 2 - Complex.arg (w₀ + Complex.I * w) := by
  sorry



theorem theorem_592475_problem
  {n : ℕ}
  -- Definitions of geometric concepts implicit in the problem statement
  (Hypersurface : Type*)
  (integral : Hypersurface → ((Fin n → ℂ) → ℂ) → ℂ)
  (is_null_homologous : Hypersurface → Set (Fin n → ℂ) → Prop)
  -- Conditions defined in the problem
  (Ω : Set (Fin n → ℂ))
  (hΩ : IsOpen Ω)
  (f : (Fin n → ℂ) → ℂ)
  (hf : DifferentiableOn ℂ f Ω)
  (S : Hypersurface)
  (hS_hom : is_null_homologous S Ω) :
  integral S f = 0 := by
  sorry





theorem theorem_592867_problem :
  ¬ ∃ (H : Nat.Partrec.Code → ℕ → Bool),
    Computable (fun p : Nat.Partrec.Code × ℕ ↦ H p.1 p.2) ∧
    ∀ (P : Nat.Partrec.Code) (x : ℕ), H P x = true ↔ (P.eval x).Dom := by
  sorry

theorem theorem_593259_problem {X : Type*} [MetricSpace X] [CompleteSpace X]
  (Ω : ℕ → Set X)
  (h_open : ∀ n, IsOpen (Ω n))
  (h_dense : ∀ n, Dense (Ω n)) :
  Dense (⋂ n, Ω n) := by
  sorry



theorem theorem_593526_problem (θ : ℝ)
  (h1 : 0 < θ) (h2 : θ < Real.pi / 2) :
  (1 + (Real.cos θ + Complex.I * Real.sin θ)) /
  (1 - (Real.cos θ + Complex.I * Real.sin θ)) =
  - (1 / (Complex.I * Real.tan (θ / 2))) := by
  sorry







theorem theorem_593468_problem
  (V : Type*)
  (d : V → V → ℝ)
  (P : Set V)
  (q : V)
  (s : V → ℝ)
  (h_d_nonneg : ∀ u v, 0 ≤ d u v)
  (h_s_pos : ∀ p ∈ P, 0 < s p)
  (T : V → ℝ)
  (h_T_def : ∀ p, T p = d p q / s p) :
  {p ∈ P | ∀ p' ∈ P, T p ≤ T p'} = {p ∈ P | ∀ p' ∈ P, d p q / s p ≤ d p' q / s p'} := by
  sorry



theorem theorem_593919_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (h1 : A ^ 2 = A)
  (h2 : IsUnit A)
  (h3 : A⁻¹ = A) :
  A = 1 := by
  sorry

theorem theorem_593564_problem (n : ℕ) (a b : Fin n → ℤ) (h : a ≠ b) :
  ∃! k : Fin n, (a k ≠ b k) ∧ (∀ j : Fin n, j < k → a j = b j) := by
  sorry







theorem theorem_594165_problem (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (t : ℂ) (ht : t ≠ 0) :
  (t ^ b) ^ (Nat.lcm a b / b) - (t ^ a) ^ (Nat.lcm a b / a) = 0 := by
  sorry



theorem theorem_593189_problem
  {α : Type*} [TopologicalSpace α]
  (A B : Set α) :
  closure A ×ˢ closure B ⊆ closure (A ×ˢ B) := by
  sorry

theorem theorem_593854_problem (P : ℕ → ℝ)
  (hP : ∀ n, P n = (3 * (n : ℝ)^2 - n) / 2)
  (x : ℝ) (hx : |x| < 1) :
  ∑' n : ℕ, P n * x^n = (2 * x^2 + x) / (1 - x)^3 := by
  sorry

theorem theorem_593933_problem {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (J : Matrix m n ℝ) :
  LinearMap.ker (Matrix.toLin' (J.transpose * J)) = LinearMap.ker (Matrix.toLin' J) := by
  sorry

theorem theorem_594073_problem
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (M : Matrix (Fin n) (Fin n) ℝ)
  (hM : M = A.transpose * A)
  (lam_q : ℝ)
  (e_q : Fin n → ℝ)
  (h_eig : M.mulVec e_q = lam_q • e_q)
  (h_min : ∀ (μ : ℝ) (x : Fin n → ℝ), x ≠ 0 → M.mulVec x = μ • x → lam_q ≤ μ)
  (h_norm : Matrix.dotProduct e_q e_q = 1) :
  ∀ p : Fin n → ℝ, Matrix.dotProduct p p = 1 →
  Matrix.dotProduct p (M.mulVec p) ≥ Matrix.dotProduct e_q (M.mulVec e_q) := by
  sorry

theorem theorem_594178_problem
  (D : Set ℝ)
  (hD : D.Nonempty)
  (fn : ℕ → ℝ → ℝ)
  (f : ℝ → ℝ)
  (h_unif : TendstoUniformlyOn fn f Filter.atTop D)
  (C : Set ℝ)
  (hC_sub : C ⊆ D)
  (hC_compact : IsCompact C) :
  TendstoUniformlyOn fn f Filter.atTop C := by
  sorry













theorem theorem_594043_problem (z : ℂ) (h_nz : z ≠ 0)
  (h_eq : Complex.cos (Complex.I * z) = Complex.cos z) :
  ∃ m : ℤ, z = (2 * (m : ℂ) * ↑Real.pi) / (1 + Complex.I) ∨
           z = (2 * (m : ℂ) * ↑Real.pi) / (1 - Complex.I) := by
  sorry



theorem theorem_594360_problem (f : ℝ → ℝ) (h : ∀ x, f x = x^5) :
  ¬ UniformContinuous f := by
  sorry



theorem theorem_594511_problem
  (E B : Type*) [TopologicalSpace E] [TopologicalSpace B]
  (p : C(E, B)) (hp : IsCoveringMap p)
  (f : C(unitInterval, B))
  (f_hat : C(unitInterval, E))
  (h_lift : p.comp f_hat = f)
  (h_neq : f_hat 0 ≠ f_hat 1) :
  ¬ ∃ (x₀ : B) (H : C(unitInterval × unitInterval, B)),
    (∀ t, H (t, 0) = f t) ∧ (∀ t, H (t, 1) = x₀) := by
  sorry









theorem theorem_595077_problem
  (N D P : ℝ → ℝ)
  (hP : ∀ x, P x = N x / D x)
  (x_star : ℝ)
  (hN : N x_star = 0)
  (hD : D x_star ≠ 0) :
  P x_star = 0 := by
  sorry



theorem theorem_594926_problem (n r : ℝ) (h_nr : n > r) (h_r0 : r > 0)
  (n' r' : ℕ) (h_n : n = n') (h_r : r = r') :
  Real.Gamma (n + 1) / (Real.Gamma (r + 1) * Real.Gamma (n - r + 1)) = (n'.choose r' : ℝ) := by
  sorry

theorem theorem_594903_problem
  (a b c A w : ℂ)
  (f : ℂ → ℂ)
  (hf : ∀ x, f x = c * x^2 + b * x + a)
  (hA : A^3 = 2)
  (hw_def : w = Complex.exp (2 * ↑Real.pi * Complex.I / 3))
  (hw_root : w^3 = 1)
  (hw_sum : w + 1 / w = -1) :
  a^3 + 2 * b^3 + 4 * c^3 - 6 * a * b * c = f A * f (A * w) * f (A / w) := by
  sorry



theorem theorem_594417_problem (n k : ℕ) (h : k ≤ n) :
  Nat.choose n k = ∑ j in Finset.range (k + 1), (Nat.choose k j) * (Nat.choose (n - k) j) := by
  sorry

theorem theorem_594992_problem
  (K : Type*) [Field K]
  (U U' V V' : Type*)
  [AddCommGroup U] [Module K U]
  [AddCommGroup U'] [Module K U']
  [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V']
  (f : U' ≃ₗ[K] U)
  (g : V ≃ₗ[K] V') :
  ∃ F : (U →ₗ[K] V) ≃ₗ[K] (U' →ₗ[K] V'),
    ∀ T : U →ₗ[K] V, F T = g.toLinearMap.comp (T.comp f.toLinearMap) := by
  sorry

theorem theorem_595183_problem
  (f g : ℝ → ℝ)
  (a b q r : ℕ → ℝ)
  (a₀ q₀ m n : ℝ)
  (hf_per : Function.Periodic f (2 * Real.pi))
  (hg_per : Function.Periodic g (2 * Real.pi))
  (hf : ∀ x, f x = a₀ + ∑' k : ℕ, if k = 0 then 0 else a k * Real.cos (k * x) + b k * Real.sin (k * x))
  (hg : ∀ x, g x = q₀ + ∑' k : ℕ, if k = 0 then 0 else q k * Real.cos (k * x) + r k * Real.sin (k * x))
  (h : ℝ → ℝ)
  (hh : ∀ x, h x = m * f x + n * g x) :
  ∀ x, h x = (m * a₀ + n * q₀) + ∑' k : ℕ, if k = 0 then 0 else 
    (m * a k + n * q k) * Real.cos (k * x) + (m * b k + n * r k) * Real.sin (k * x) := by
  sorry

theorem theorem_595197_problem
  (n : ℕ)
  (v : Fin n → ℝ)
  (hv_nonzero : v ≠ 0)
  (hv_components : ∀ i, v i ≠ 0)
  (v_inv : Fin n → ℝ)
  (h_v_inv : v_inv = fun i ↦ (v i)⁻¹)
  (M : Matrix (Fin n) (Fin n) ℝ)
  (hM : M = Matrix.vecMulVec v v_inv) :
  M.rank = 1 := by
  sorry

theorem theorem_595325_problem (u : ℝ → ℝ → ℝ) (f : ℝ → ℝ)
  (hu : Differentiable ℝ (Function.uncurry u))
  (hf : Differentiable ℝ f)
  (h_pde : ∀ x y, deriv (fun t => u t y) x - deriv (fun t => u x t) y = -1)
  (h_ic : ∀ x, u x 0 = f x) :
  ∀ x y, u x y = y + f (x + y) := by
  sorry





