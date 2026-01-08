import Mathlib
import Mathlib.Tactic



theorem theorem_928548_problem (x y : ℝ) :
  (|x| + |y| = 1) ↔
  ∃ w₁ w₂ w₃ w₄ : ℝ,
    (w₁ = 0 ∨ w₁ = 1) ∧
    (w₂ = 0 ∨ w₂ = 1) ∧
    (w₃ = 0 ∨ w₃ = 1) ∧
    (w₄ = 0 ∨ w₄ = 1) ∧
    (1 - 2 * w₁ ≤ x + y ∧ x + y ≤ 1) ∧
    (1 - 2 * w₂ ≤ -x + y ∧ -x + y ≤ 1) ∧
    (1 - 2 * w₃ ≤ x - y ∧ x - y ≤ 1) ∧
    (1 - 2 * w₄ ≤ -x - y ∧ -x - y ≤ 1) ∧
    (w₁ + w₂ + w₃ + w₄ ≤ 3) := by
  sorry

theorem theorem_930439_problem (n : ℕ) (h : n ≥ 1) : 3 ^ n > n ^ 2 - 1 := by
  sorry

theorem theorem_929678_problem (a b : ℝ) (f : ℝ → ℝ) 
  (h_ab : a < b) (h_mono : MonotoneOn f (Set.Icc a b)) :
  ∀ ε > 0, ∃ n : ℕ, 0 < n ∧ 
    let δ := (b - a) / (n : ℝ)
    let x := fun (i : ℕ) => a + i * δ
    let w := fun (i : ℕ) => f (x (i + 1)) - f (x i)
    ∑ i in Finset.range n, w i * δ < ε := by
  sorry

theorem theorem_930669_problem
  (n : ℕ)
  (A_i : Fin n → Type*)
  (T_i : Fin n → Type*)
  [∀ i, Fintype (T_i i)]
  [∀ i, DecidableEq (T_i i)]
  (u : (i : Fin n) → (Π j, A_i j) → (Π j, T_i j) → ℝ)
  (π : (Π j, T_i j) → ℝ)
  (h_pi_range : ∀ t, 0 ≤ π t ∧ π t ≤ 1)
  (h_pi_sum : ∑ t : Π j, T_i j, π t = 1)
  (ExpectedValue : ((Π j, T_i j) → ℝ) → ℝ)
  (h_Exp_def : ∀ (X : (Π j, T_i j) → ℝ), ExpectedValue X = ∑ t, π t * X t) :
  ∀ (i : Fin n) (a : Π j, A_i j),
    ExpectedValue (fun t ↦ u i a t) = ∑ t, π t * u i a t := by
  sorry





theorem theorem_930715_problem (a gamma : ℝ) (ha : a ≠ 0) (hgamma : 1 < gamma) :
  ∀ x y : ℝ, (∃ x₀ y₀ : ℝ, x₀^2 / a^2 + y₀^2 / a^2 = 1 ∧ x = x₀ / gamma ∧ y = y₀) ↔
  (x^2 * gamma^2) / a^2 + y^2 / a^2 = 1 := by
  sorry

theorem theorem_930860_problem
  (f : ℕ → ℝ → ℝ)
  (R : Set ℝ)
  (a : ℕ → ℝ)
  (h_nonneg : ∀ n, 0 ≤ a n)
  (h_bound : ∀ x ∈ R, ∀ n, |f n x| ≤ a n)
  (h_summable : Summable a) :
  TendstoUniformlyOn (fun N x ↦ ∑ i ∈ Finset.range N, f i x) (fun x ↦ ∑' i, f i x) atTop R := by
  sorry



theorem theorem_930403_problem (n : ℤ) (k : ℝ) (hk : 0 < k ∧ k < 1) :
  (1 - (k : ℂ)) * (1 + Complex.I) ^ n + (k : ℂ) * (1 + Complex.I) ^ (n + 1) =
  (1 + Complex.I) ^ n * (1 + (k : ℂ) * Complex.I) := by
  sorry



theorem theorem_931270_problem (P : Set ℕ) (h : P = { p | Nat.Prime p }) : 
  Set.Infinite P := by
  sorry









theorem theorem_930702_problem (f : ℝ × ℝ → ℝ)
  (h : ∀ x y : ℝ, f (x, y) = Real.sin (x * y)) :
  ContinuousAt f (0, 0) := by
  sorry





theorem theorem_931333_problem (n : ℕ) (hn : n ≥ 1) :
  let S := MvPolynomial (Fin n × Fin n) ℤ
  let a : Matrix (Fin n) (Fin n) S := fun i j ↦ MvPolynomial.X (i, j)
  let det_a := Matrix.det a
  let R := Localization.Away det_a
  ∀ (A : Type*) [CommRing A], Nonempty ((R →+* A) ≃ Matrix.GeneralLinearGroup (Fin n) A) := by
  sorry



theorem theorem_931152_problem
  (n : ℕ)
  (a : Fin n → ℝ)
  (x₀ : ℝ)
  (y₁ y₂ : ℝ → ℝ)
  (h_diff₁ : ContDiff ℝ n y₁)
  (h_diff₂ : ContDiff ℝ n y₂)
  (h_ode₁ : ∀ x, iteratedDeriv n y₁ x + ∑ i : Fin n, a i * iteratedDeriv i y₁ x = 0)
  (h_ode₂ : ∀ x, iteratedDeriv n y₂ x + ∑ i : Fin n, a i * iteratedDeriv i y₂ x = 0)
  (h_init : ∀ i : Fin n, iteratedDeriv i y₁ x₀ = iteratedDeriv i y₂ x₀) :
  y₁ = y₂ := by
  sorry



theorem theorem_931520_problem
  (U V : Set ℂ)
  (f g h : ℂ → ℂ)
  (hU : IsOpen U)
  (hV : IsOpen V)
  (hUV : Disjoint U V)
  (hf : DifferentiableOn ℂ f U)
  (hg : DifferentiableOn ℂ g V)
  (h_eq_f : Set.EqOn h f U)
  (h_eq_g : Set.EqOn h g V) :
  DifferentiableOn ℂ h (U ∪ V) := by
  sorry







theorem theorem_930907_problem (x r₁ r₂ r₃ : ℤ)
  (hr₁ : r₁ = 1 ∨ r₁ = 2)
  (hr₂ : r₂ = 1 ∨ r₂ = 4)
  (hr₃ : r₃ = 3 ∨ r₃ = 4)
  (h₁ : x ≡ r₁ [ZMOD 3])
  (h₂ : x ≡ r₂ [ZMOD 5])
  (h₃ : x ≡ r₃ [ZMOD 7]) :
  x^2 ≡ 16 [ZMOD 105] := by
  sorry





theorem theorem_931762_problem (P Q : Polynomial ℝ) (n m : ℕ)
  (hP : P.degree = n)
  (hQ : Q.degree = m)
  (hneq : n ≠ m) :
  ¬ ∃ (a b : ℝ), a < b ∧ ∀ x ∈ Set.Ioo a b, P.eval x = Q.eval x := by
  sorry



theorem theorem_931834_problem 
  {α : Type} 
  (R : α → α → Prop) 
  (A : Set α) 
  (B : Set α) 
  (hB : B = {x ∈ A | ¬ R x x}) : 
  ∀ x ∈ B, ¬ R x x := by
  sorry



theorem theorem_931725_problem (F : Type*) [Field F] (p : ℕ) [CharP F p] (hp : p > 0)
  (k n : ℕ) (a : Fin n → F) :
  (∑ i, a i) ^ (p ^ k) = ∑ i, (a i) ^ (p ^ k) := by
  sorry

theorem theorem_931704_problem (a : ℝ) (ha : a > 0) :
  ∫ θ in (0 : ℝ)..(Real.pi / 2), ((a * Real.sin θ)^2 - (a * (1 - Real.cos θ))^2) / 2 = 
  (1 - Real.pi / 4) * a^2 := by
  sorry



theorem theorem_931899_problem (x : ℝ) :
  let t : ℝ → ℝ := fun x ↦ Real.sqrt (x + Real.sqrt (x^2 + 1))
  HasDerivAt (fun x ↦ (t x)^3 / 3 - 1 / (t x)) (t x) x := by
  sorry











theorem theorem_932134_problem
  {G : Type*} [Group G]
  (N : Subgroup G)
  (X Y : Set G)
  (hX : X ⊆ N)
  (hN_gen : Subgroup.closure X = N)
  (hG_gen : Subgroup.closure Y = ⊤) :
  N.Normal ↔ ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ N ∧ y⁻¹ * x * y ∈ N := by
  sorry

theorem theorem_931942_problem
  (C : ℝ)
  (f g : ℝ → ℝ)
  (hf : ∀ x, f x = Real.log (abs ((x - 2) / 2 + Real.sqrt (x ^ 2 - 4 * x) / 2)) + C)
  (hg : ∀ x, g x = 2 * Real.log (abs (Real.sqrt x / 2 + Real.sqrt (x - 4) / 2)) + C)
  (x : ℝ)
  (hx : x > 4) :
  f x = g x := by
  sorry

theorem theorem_932216_problem (a b : Fin 3 → ℝ) :
  (∑ i, a i * b i)^2 ≤ (∑ j, (a j)^2) * (∑ k, (b k)^2) := by
  sorry

theorem theorem_932511_problem (k : Type*) [Field k] (n : ℕ)
  (f : MvPolynomial (Fin n) k)
  (hf : MvPolynomial.IsSymmetric f) :
  ∃ p : MvPolynomial (Fin n) k,
    f = MvPolynomial.aeval (fun (i : Fin n) => MvPolynomial.esymm (Fin n) k ((i : ℕ) + 1)) p := by
  sorry







theorem theorem_931978_problem (p : Polynomial ℂ) (hp : p ≠ 0)
  (found remaining : Multiset ℂ)
  (h_found : found = p.roots.filter (fun r => 1 ≤ Complex.abs r))
  (h_remaining : remaining = p.roots - found) :
  ∀ r ∈ remaining, Complex.abs r < 1 := by
  sorry













theorem theorem_932630_problem (W : Type*) (R : W → W → Prop) :
  (∀ (P : Set W) (w : W),
    (∀ x, R w x → ∃ y, R x y ∧ y ∈ P) →
    (∃ x, R w x ∧ ∀ y, R x y → y ∈ P)) ↔
  (∀ w, ∃ y, R w y ∧ ∀ z, R y z → y = z) := by
  sorry

theorem theorem_933534_problem
  (S : Type)
  [Membership S S]
  (zero : S)
  (succ : S → S)
  (a b : S)
  (ha : a = succ (succ (succ (succ zero))))
  (hb : b = succ (succ (succ (succ zero)))) :
  ∀ x : S, x ∈ a ↔ x ∈ b := by
  sorry

theorem theorem_933153_problem
  (F : Type*) [Field F] [CharZero F]
  (L : Type*) [LieRing L] [LieAlgebra F L] [Module.Finite F L] :
  ∃ (V : Type*) (_ : AddCommGroup V) (_ : Module F V),
    Module.Finite F V ∧
    ∃ (φ : L →ₗ⁅F⁆ Module.End F V), Function.Injective φ := by
  sorry

theorem theorem_933680_problem (A B C D E : Prop)
  (h1 : A → (¬ B ∨ C))
  (h2 : (¬ D ∧ A) → B)
  (h3 : ¬ E → A) :
  D ∨ (C ∨ E) := by
  sorry

theorem theorem_933550_problem
  (V : Type*)
  (parent : V → V)
  (root : V)
  (level : V → ℕ)
  (h_root_parent : parent root = root)
  (h_root_level : level root = 0)
  (h_parent_level : ∀ x, x ≠ root → level x = level (parent x) + 1)
  (h_parent_neq : ∀ x, x ≠ root → parent x ≠ x)
  (Succ : V → Set V)
  (h_Succ : ∀ u, Succ u = {v | parent v = u ∧ v ≠ u})
  (SuccOrder : Π u, LinearOrder (Succ u)) :
  ∀ n : ℕ, ∃ (lo : LinearOrder {x // level x = n}),
    ∀ (u v : {x // level x = n}),
      lo.le u v ↔
        (u = v ∨
         ∃ (k : ℕ), k ≤ n ∧ 0 < k ∧
           (∀ j, j < k → parent^[n - j] u.1 = parent^[n - j] v.1) ∧
           (parent^[n - k] u.1 ≠ parent^[n - k] v.1) ∧
           (let p := parent^[n - (k - 1)] u.1
            let uk := parent^[n - k] u.1
            let vk := parent^[n - k] v.1
            ∃ (huk : uk ∈ Succ p) (hvk : vk ∈ Succ p),
              (SuccOrder p).le ⟨uk, huk⟩ ⟨vk, hvk⟩)) := by
  sorry

theorem theorem_933599_problem (c : ℕ → ℂ)
  (h : Summable (fun n => ‖c n‖)) :
  ∀ x : ℝ, Summable (fun n => c n * Complex.exp (Complex.I * x * n)) := by
  sorry



theorem theorem_933038_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Set E) (x : E) (D : Set E)
  (hP : Convex ℝ P)
  (hx : x ∈ P.extremePoints ℝ)
  (hD_sub : D ⊆ P)
  (hx_in_D : x ∈ D)
  (hD_open : IsOpen (Subtype.val ⁻¹' D : Set (affineSpan ℝ P))) :
  D = {x} := by
  sorry







theorem theorem_933504_problem (a x : ℝ) (ha : 0 < a) :
  ∀ h : ℝ, HasDerivAt (fun h => (1 / 2 : ℝ) * (a ^ 2 * Real.log ((x + h + Real.sqrt (a ^ 2 + (x + h) ^ 2)) / a) +
    (x + h) * Real.sqrt (a ^ 2 + (x + h) ^ 2))) (Real.sqrt (a ^ 2 + (x + h) ^ 2)) h := by
  sorry





theorem theorem_933690_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ) (x : ℕ → E) (x_star : E)
  (h_diff : ContDiff ℝ 1 f)
  (h_method : ∀ k, ∃ α, 0 < α ∧ x (k + 1) = x k - α • gradient f (x k))
  (h_lim : MapClusterPt x_star atTop x) :
  gradient f x_star = 0 := by
  sorry





theorem theorem_933983_problem
  (f₁ f₂ f₃ : (Fin 3 → ℝ) → ℝ)
  (x y z : ℝ → ℝ)
  (γ : ℝ → (Fin 3 → ℝ))
  (a b : ℝ)
  -- Condition: γ is parameterized by x, y, z
  (hγ : ∀ t, γ t = ![x t, y t, z t])
  -- Condition: The components are smooth (differentiable)
  (hx : Differentiable ℝ x)
  (hy : Differentiable ℝ y)
  (hz : Differentiable ℝ z)
  -- Condition: α is the 1-form f₁ dx + f₂ dy + f₃ dz
  -- We model a 1-form as a map from a point to a linear map on the tangent space (Fin 3 → ℝ)
  (α : (Fin 3 → ℝ) → ((Fin 3 → ℝ) →L[ℝ] ℝ))
  (hα : ∀ p v, α p v = f₁ p * (v 0) + f₂ p * (v 1) + f₃ p * (v 2)) :
  -- Conclusion: The integral matches the expanded formula
  (∫ t in a..b, α (γ t) (deriv γ t)) =
  ∫ t in a..b, (f₁ (γ t) * deriv x t + f₂ (γ t) * deriv y t + f₃ (γ t) * deriv z t) := by
  sorry



theorem theorem_934331_problem (n : ℕ)
  (A v : Matrix (Fin n) (Fin 1) ℝ)
  (h : A * v.transpose = 1) :
  n = 1 := by
  sorry

theorem theorem_934732_problem
  (R : Type*) [CommRing R]
  (M : Type*) [AddCommGroup M] [Module R M]
  (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N]
  (f : M →ₗ[R] N)
  (h : ∀ (m : Ideal R), m.IsMaximal → LinearMap.range f ⊔ m • (⊤ : Submodule R N) = ⊤) :
  Function.Surjective f := by
  sorry



theorem theorem_934491_problem (a : ℂ) (h : IsAlgebraic ℚ a) :
  IsAlgebraic ℚ (Complex.I * a) := by
  sorry











theorem theorem_934554_problem 
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  -- A basis in LP is identified by a set of column indices.
  (B : ℕ → Finset (Fin n))
  -- The condition that the sequence of bases contains no repeats (no cycling).
  (h_distinct : ∀ i j, i ≠ j → B i ≠ B j) :
  -- The conclusion that the method must converge (terminate).
  -- Mathematically, this means an infinite distinct sequence implies a contradiction
  -- because the set of possible bases (Finset (Fin n)) is finite.
  False := by
  sorry







theorem theorem_934743_problem (X : Type*) [MetricSpace X]
  (Y E : Set X) (hE : E ⊆ Y) :
  (∃ O : Set X, IsOpen O ∧ E = O ∩ Y) ↔
  (∀ p ∈ E, ∃ r > 0, Metric.ball p r ∩ Y ⊆ E) := by
  sorry

theorem theorem_934819_problem (r phi : ℝ → ℝ)
  (h_pos : ∀ s, 0 < r s)
  (h_const : ∀ s, deriv r s = 0)
  (h_eq1 : ∀ s, deriv (deriv phi) s = 0)
  (h_eq2 : ∀ s, ((r s)^7 / ((r s)^6 + 4)) * (deriv phi s)^2 = 0) :
  ∀ s, deriv phi s = 0 := by
  sorry













theorem theorem_935400_problem {α : Type*} (S : Set α) (P : α → Prop) 
  (h : ∃ x, x ∉ S ∧ ¬ P x) : 
  ¬ (∀ x, x ∉ S → P x) := by
  sorry

theorem theorem_935661_problem (p q n : ℕ)
  (h1 : Nat.gcd p q = 1)
  (h2 : n > 0)
  (h3 : q ∣ p^n) :
  q = 1 := by
  sorry

