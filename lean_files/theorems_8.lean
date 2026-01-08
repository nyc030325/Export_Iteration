import Mathlib
import Mathlib.Tactic

theorem theorem_37555_problem 
  (log_p : ℝ → ℝ) 
  (θ_hat : ℝ) 
  (I : ℝ)
  (h_smooth : ContDiffAt ℝ 2 log_p θ_hat)
  (h_map : deriv log_p θ_hat = 0)
  (h_I : I = - deriv (deriv log_p) θ_hat)
  (h_pos : I > 0) :
  ∀ θ : ℝ, 
    Real.exp (log_p θ_hat + deriv log_p θ_hat * (θ - θ_hat) + (1 / 2 : ℝ) * deriv (deriv log_p) θ_hat * (θ - θ_hat)^2) = 
    Real.exp (log_p θ_hat) * Real.exp (- (1 / 2 : ℝ) * (θ - θ_hat)^2 * I) := by
  sorry





theorem theorem_37717_problem :
  let T : ℝ × ℝ → ℝ × ℝ := fun p ↦ ((p.1 + p.2) / Real.sqrt 2, (-p.1 + p.2) / Real.sqrt 2)
  let B : Set (ℝ × ℝ) := {p | |p.1| + |p.2| < 2}
  let S : Set (ℝ × ℝ) := {p | |p.1| < Real.sqrt 2 ∧ |p.2| < Real.sqrt 2}
  T '' B = S := by
  sorry



theorem theorem_37746_problem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (B C : Submodule K V) :
  (∃ W : Submodule K V, (W : Set V) = (B : Set V) ∪ (C : Set V)) ↔ (B ≤ C ∨ C ≤ B) := by
  sorry







theorem theorem_38030_problem (f : ℕ → ℝ → ℝ)
  (h : ∀ n : ℕ, {x : ℝ | f n x ≠ 0} ⊆ Set.Icc 0 (1 / (n : ℝ))) :
  ∀ x : ℝ, Filter.Tendsto (fun n ↦ f n x) Filter.atTop (nhds 0) := by
  sorry







theorem theorem_38965_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  (n : ℕ)
  (v : Basis (Fin n) K V)
  (A : V →ₗ[K] W)
  (hA : Function.Bijective A) :
  LinearIndependent K (fun i => A (v i)) ∧
  Submodule.span K (Set.range (fun i => A (v i))) = ⊤ := by
  sorry



theorem theorem_38692_problem
  (d : ℕ) (hd : d > 0)
  (x y : Fin d → ℝ)
  (mean_x : ℝ) (h_mean_x : mean_x = (∑ i, x i) / (d : ℝ))
  (sigma_x : ℝ) (h_sigma_x : sigma_x = Real.sqrt ((∑ i, (x i - mean_x)^2) / (d : ℝ)))
  (mean_y : ℝ) (h_mean_y : mean_y = (∑ i, y i) / (d : ℝ))
  (sigma_y : ℝ) (h_sigma_y : sigma_y = Real.sqrt ((∑ i, (y i - mean_y)^2) / (d : ℝ))) :
  Real.sqrt (∑ i, (x i - y i)^2) ≤ Real.sqrt (d : ℝ) * (Real.sqrt (sigma_x^2 + mean_x^2) + Real.sqrt (sigma_y^2 + mean_y^2)) := by
  sorry

theorem theorem_39192_problem
  (y : ℕ → Set.Icc (0 : ℝ) 1 → ℝ)
  (f : Set.Icc (0 : ℝ) 1 → ℝ)
  (h_cont : ∀ n, Continuous (y n))
  (h_pt : ∀ x, Filter.Tendsto (fun n => y n x) Filter.atTop (nhds (f x)))
  (h_disc : ¬ Continuous f) :
  ¬ TendstoUniformly y f Filter.atTop := by
  sorry



theorem theorem_38059_problem {F V A : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddTorsor V A] (S : Set A) (hS : S.Nonempty) :
  (∃ L : AffineSubspace F A, (L : Set A) = S) ↔
  (∃ (W : Submodule F V) (x : A), S = {y | ∃ w ∈ W, y = w +ᵥ x}) := by
  sorry





theorem theorem_38589_problem (n : ℕ) (v : Fin (n + 1) → (Fin n → ℝ))
  (h_indep : AffineIndependent ℝ v) :
  (MeasureTheory.volume (convexHull ℝ (Set.range v))).toReal =
  (1 / (n.factorial : ℝ)) * |Matrix.det (fun i j : Fin n => v j.succ i - v 0 i)| := by
  sorry

theorem theorem_39436_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  (S : X →L[𝕜] Y)
  (T : Y →L[𝕜] Z) :
  ‖T.comp S‖ ≤ ‖T‖ * ‖S‖ := by
  sorry

theorem theorem_38698_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  {n : ℕ}
  (B : Basis (Fin n) F V)
  (T : V →ₗ[F] V)
  (A : Matrix (Fin n) (Fin n) F)
  (hA : LinearMap.toMatrix B B T = A)
  (q : Polynomial F) :
  LinearMap.toMatrix B B (Polynomial.aeval T q) = Polynomial.aeval A q := by
  sorry





theorem theorem_39835_problem :
  let g_inv : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun u => ![(u 0 + u 1) / 2, (u 0 - u 1) / 2]
  let J : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 1/2; 1/2, -1/2]
  ∀ u : Fin 2 → ℝ, HasFDerivAt g_inv (LinearMap.toContinuousLinearMap (Matrix.toLin' J)) u := by
  sorry

theorem theorem_39474_problem
  (R : Type*) [CommRing R]
  (M : Type*) [AddCommGroup M] [Module R M]
  (n : Cardinal)
  (hM_free : Module.Free R M)
  (hM_rank : Module.rank R M = n)
  (A : Set M)
  (hA_indep : LinearIndependent R (Subtype.val : A → M)) :
  Cardinal.mk A ≤ n := by
  sorry



















theorem theorem_38350_problem (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (h_inf_dim : ¬ FiniteDimensional ℝ E) :
  ¬ IsCompact (Metric.closedBall (0 : E) 1) := by
  sorry



theorem theorem_39895_problem (n : ℕ) (a b : Fin n → ℝ)
  (h : ∀ i j, a i + b j ≠ 0) :
  Matrix.det (Matrix.of (fun i j ↦ 1 / (a i + b j))) =
  (∏ i : Fin n, ∏ j in Finset.Ioi i, (a j - a i) * (b j - b i)) /
  (∏ i : Fin n, ∏ j : Fin n, (a i + b j)) := by
  sorry

theorem theorem_38716_problem 
  (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
  (l1 l2 l3 l4 l5 l6 : ℝ) :
  ∃ p : ℝ, 0 < p ∧ 
    let l2' := l2 - p * B
    let l3' := l3 + p * C
    let l4' := l4 - p * A
    let l5' := l5 + p * C
    let l6' := l6 - p * B
    (l3' * A + l4' * C = l3 * A + l4 * C) ∧ 
    (l5' * B + l6' * C = l5 * B + l6 * C) ∧ 
    (l2' < l5') ∧ 
    (l2' * l6' > 0) := by
  sorry

theorem theorem_40419_problem
  (n : ℕ)
  (c : Fin n → ℝ)
  (b : ℝ)
  (B NB : Set (Fin n))
  (h_union : B ∪ NB = Set.univ)
  (h_c_B : ∀ i ∈ B, c i = 0)
  (h_c_NB : ∀ i ∈ NB, 0 ≤ c i) :
  ∀ (x : Fin n → ℝ) (Z : ℝ),
    (∀ i, 0 ≤ x i) →
    (Z + ∑ i, c i * x i = b) →
    Z ≤ b := by
  sorry





theorem theorem_38053_problem
  (f : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ)
  (h_cont : Continuous f)
  (h_def : ∀ x₁ x₂ x₃ : ℝ, f (x₁, x₂, x₃) = (0, 0, x₃)) :
  {x : ℝ × ℝ × ℝ | f x = x} = {x : ℝ × ℝ × ℝ | ∃ y₃ : ℝ, x = (0, 0, y₃)} := by
  sorry



theorem theorem_40170_problem (n : ℕ) (a b c : Fin n → ℝ) (i : Fin n) :
  let δ := fun (x y : Fin n) => if x = y then (1 : ℝ) else 0
  ∑ j : Fin n, ∑ l : Fin n, ∑ m : Fin n, (δ i l * δ j m - δ i m * δ j l) * a j * b l * c m = 
  (∑ j : Fin n, a j * b i * c j) - (∑ j : Fin n, a j * b j * c i) := by
  sorry

theorem theorem_40156_problem
  (n T : ℕ)
  (hn : n > 0)
  (hT : T > 0)
  (y X e : Fin n → Fin T → ℝ)
  (u : Fin n → ℝ)
  (ν : Fin T → ℝ)
  (β : ℝ)
  (h_model : ∀ i t, y i t = u i + ν t + β * X i t + e i t)
  -- Definitions of means for y, X, and e
  (y_bar_i X_bar_i e_bar_i : Fin n → ℝ)
  (y_bar_t X_bar_t e_bar_t : Fin T → ℝ)
  (y_bar_grand X_bar_grand e_bar_grand : ℝ)
  -- Hypotheses defining the values of the means
  (h_yi : ∀ i, y_bar_i i = (∑ t : Fin T, y i t) / (T : ℝ))
  (h_Xi : ∀ i, X_bar_i i = (∑ t : Fin T, X i t) / (T : ℝ))
  (h_ei : ∀ i, e_bar_i i = (∑ t : Fin T, e i t) / (T : ℝ))
  (h_yt : ∀ t, y_bar_t t = (∑ i : Fin n, y i t) / (n : ℝ))
  (h_Xt : ∀ t, X_bar_t t = (∑ i : Fin n, X i t) / (n : ℝ))
  (h_et : ∀ t, e_bar_t t = (∑ i : Fin n, e i t) / (n : ℝ))
  (h_y_grand : y_bar_grand = (∑ i : Fin n, ∑ t : Fin T, y i t) / ((n : ℝ) * (T : ℝ)))
  (h_X_grand : X_bar_grand = (∑ i : Fin n, ∑ t : Fin T, X i t) / ((n : ℝ) * (T : ℝ)))
  (h_e_grand : e_bar_grand = (∑ i : Fin n, ∑ t : Fin T, e i t) / ((n : ℝ) * (T : ℝ))) :
  ∀ i t, y i t - y_bar_i i - y_bar_t t + y_bar_grand =
         β * (X i t - X_bar_i i - X_bar_t t + X_bar_grand) +
         (e i t - e_bar_i i - e_bar_t t + e_bar_grand) := by
  sorry







theorem theorem_38513_problem
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (C : Set (Fin n → ℝ))
  (hC_ne : C.Nonempty)
  (hC_conv : Convex ℝ C)
  (hC_closed : IsClosed C)
  (hA_rank : Matrix.rank A = n) :
  ∃! p : (Fin n → ℝ) × (Fin m → ℝ),
    (p.1 ∈ C ∧ Matrix.mulVec A p.1 - b = p.2) ∧
    ∀ q : (Fin n → ℝ) × (Fin m → ℝ),
      (q.1 ∈ C ∧ Matrix.mulVec A q.1 - b = q.2) →
      (1 / 2 : ℝ) * ∑ i, (p.2 i)^2 ≤ (1 / 2 : ℝ) * ∑ i, (q.2 i)^2 := by
  sorry

theorem theorem_40416_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (D : Set X)
  (hD_subset : D ⊆ Metric.sphere 0 1)
  (hD_countable : Set.Countable D)
  (hD_dense : Metric.sphere 0 1 ⊆ closure D) :
  Set.Countable {x | ∃ q : ℚ, ∃ d ∈ D, x = (q : ℝ) • d} ∧
  Dense {x | ∃ q : ℚ, ∃ d ∈ D, x = (q : ℝ) • d} := by
  sorry





theorem theorem_40394_problem :
  ∃ S : Finset (Submodule (ZMod 2) (Fin 2 → ZMod 2)),
    S.card = 3 ∧
    (∀ V ∈ S, FiniteDimensional.finrank (ZMod 2) V = 1) ∧
    (∀ V₁ V₂, V₁ ∈ S → V₂ ∈ S → V₁ ≠ V₂ → Disjoint V₁ V₂) ∧
    (⋃ V ∈ S, (V : Set (Fin 2 → ZMod 2))) = Set.univ := by
  sorry













theorem theorem_40672_problem (n : ℕ) (x y : ℕ → ℝ)
  (h : ∀ i, 1 ≤ i ∧ i ≤ n → y i = 1 - x (n + 1 - i)) :
  ∀ i, 1 ≤ i ∧ i ≤ n → y (n + 1 - i) = 1 - x i := by
  sorry

theorem theorem_38434_problem
  (N M : ℕ)
  (z : Fin N → Fin M → ℝ)
  (π : Fin M → ℝ)
  (p : Fin N → Fin M → ℝ)
  (i_n : Fin N → Fin M)
  (h_z_binary : ∀ n i, z n i = 0 ∨ z n i = 1)
  (h_z_sum : ∀ n, ∑ i, z n i = 1)
  (h_in : ∀ n, z n (i_n n) = 1)
  (h_pi_pos : ∀ i, 0 < π i)
  (h_p_pos : ∀ n i, 0 < p n i)
  (L : ℝ)
  (h_L_def : L = ∏ n, ∏ i, (π i * p n i) ^ (z n i)) :
  Real.log L = ∑ n, Real.log (π (i_n n) * p n (i_n n)) := by
  sorry



theorem theorem_40959_problem
  -- We abstract the Mapping Class Group of the torus with a boundary
  (MCG : Type*) [Group MCG]
  -- We abstract the type of simple closed curves
  (Curve : Type*)
  -- The Dehn twist operation mapping a curve to a group element
  (twist : Curve → MCG)
  -- The geometric intersection number function
  (intersect : Curve → Curve → ℕ)
  -- Predicate identifying the boundary component
  (is_boundary : Curve → Prop)
  -- The specific curves mentioned in the problem
  (a b d : Curve)
  -- Condition: d is the boundary component
  (h_boundary : is_boundary d)
  -- Condition: a and b intersect once
  (h_intersect : intersect a b = 1) :
  -- Conclusion: The chain relation holds
  (twist a * twist b)^6 = twist d := by
  sorry





theorem theorem_40760_problem (n : ℕ) (z : Fin n → ℂ) :
  ∑ i, Complex.abs (z i) ≥ Complex.abs (∑ i, z i) := by
  sorry

theorem theorem_41314_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (A : E →L[ℝ] E)
  (t : ℝ) (ht : t ∈ Set.Icc 0 ‖A‖) :
  (t - 1) * Set.indicator (Set.Ioc 1 ‖A‖) (fun _ ↦ (1 : ℝ)) t -
  (1 - t) * Set.indicator (Set.Ioo 0 1) (fun _ ↦ (1 : ℝ)) t +
  Set.indicator (Set.Ioc 0 ‖A‖) (fun _ ↦ (1 : ℝ)) t = t := by
  sorry



theorem theorem_40119_problem
  (V : Type*)
  [NormedAddCommGroup V]
  [NormedSpace ℚ V]
  [CompleteSpace V] :
  ∃! (smul_R : ℝ → V → V),
    (∀ (r : ℝ) (x y : V), smul_R r (x + y) = smul_R r x + smul_R r y) ∧
    (∀ (r s : ℝ) (x : V), smul_R (r + s) x = smul_R r x + smul_R s x) ∧
    (∀ (r s : ℝ) (x : V), smul_R (r * s) x = smul_R r (smul_R s x)) ∧
    (∀ (x : V), smul_R 1 x = x) ∧
    (∀ (r : ℝ) (x : V), ‖smul_R r x‖ = |r| * ‖x‖) ∧
    (∀ (q : ℚ) (x : V), smul_R (q : ℝ) x = q • x) := by
  sorry



theorem theorem_41366_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (u v : E) :
  Real.cos (InnerProductGeometry.angle u v) = (inner u v) / (‖u‖ * ‖v‖) := by
  sorry







theorem theorem_41847_problem
  {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
  {n d : ℕ} (hd : d ≤ n)
  (e : Basis (Fin n) K V)
  (C : Submodule K V)
  (hC : C = Submodule.span K (e '' {i | i.val < d})) :
  C = ⨅ i : {i : Fin n // d ≤ i.val}, LinearMap.ker (e.dualBasis i) := by
  sorry





theorem theorem_41926_problem
  (n : ℕ)
  (f : Fin n → ℝ → ℝ)
  (g : ℝ → ℝ)
  (x : ℝ)
  (hf : ∀ i, ContDiff ℝ ⊤ (f i))
  (hg : Differentiable ℝ g) :
  let y := g x
  let M_gx : Matrix (Fin n) (Fin n) ℝ := fun i j ↦
    (deriv^[i] (f j)) y * (deriv g x) ^ (i : ℕ)
  let M_y : Matrix (Fin n) (Fin n) ℝ := fun i j ↦
    (deriv^[i] (f j)) y
  M_gx.det = (deriv g x) ^ (n * (n - 1) / 2) * M_y.det := by
  sorry

theorem theorem_41395_problem
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  (x x_n : X) :
  |‖x_n‖ - ‖x‖| ≤ ‖x_n - x‖ := by
  sorry







theorem theorem_41959_problem (z : ℂ) :
  Complex.abs (Complex.sin z) ^ 2 + Complex.abs (Complex.cos z) ^ 2 = 1 ↔ z.im = 0 := by
  sorry





theorem theorem_41863_problem 
  (K : Type*) [Field K] [Algebra ℚ K]
  (m : ℤ) 
  (eta : K) 
  (h_eta : eta ^ 3 = (m : K))
  (h_basis : Basis (Fin 3) ℚ K)
  (h_basis_eq : ∀ i : Fin 3, h_basis i = eta ^ (i : ℕ))
  (a b c : ℤ) : 
  Algebra.norm ℚ ((a : K) + (b : K) * eta + (c : K) * eta ^ 2) = 
  ((a ^ 3 + m * b ^ 3 + m ^ 2 * c ^ 3 - 3 * m * a * b * c : ℤ) : ℚ) := by
  sorry



theorem theorem_42291_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [CommRing R]
  (Q M : Matrix n n R)
  (t k : R)
  (hQ : Q.IsSymm)
  (A : Matrix n n R)
  (hA : A = -Q + t • (Q * M + M.transpose * Q - k • Q)) :
  A.IsSymm := by
  sorry

theorem theorem_42239_problem
  (n : ℕ)
  (T S A : Fin n → Fin n → ℝ)
  (Γ A_comma : Fin n → Fin n → Fin n → ℝ)
  (h_inv : ∀ i h, ∑ k, T i k * S k h = if i = h then 1 else 0) :
  ∀ i j p,
    ∑ k, ∑ m, T i k * (
      (∑ a, ∑ b, ∑ c, S k a * Γ a b p * A b c * T c m) +
      (∑ a, ∑ b, S k a * A_comma a b p * T b m) +
      (∑ a, ∑ b, ∑ c, S k a * A a b * Γ b c p * T c m)
    ) * S m j =
    (∑ b, Γ i b p * A b j) + A_comma i j p + (∑ b, A i b * Γ b j p) := by
  sorry





theorem theorem_42088_problem (s : ℕ) (V : Submodule ℝ (Fin s → ℝ)) :
  IsClosed (V : Set (Fin s → ℝ)) := by
  sorry

theorem theorem_42726_problem
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (A : X →L[ℝ] X)
  (S : ℝ → X →L[ℝ] X)
  (u : X)
  (s : ℝ)
  (hs : 0 ≤ s)
  -- Condition: S is a strongly continuous semigroup generated by A
  -- 1. S(0) = I
  (hS_zero : S 0 = 1)
  -- 2. Semigroup property S(t+r) = S(t)S(r)
  (hS_add : ∀ t r, 0 ≤ t → 0 ≤ r → S (t + r) = S t * S r)
  -- 3. Generator property (A is the generator, so S(t)u solves u' = Au)
  (hS_gen : ∀ x, ∀ t, 0 ≤ t → HasDerivAt (fun τ => S τ x) (A (S t x)) t) :
  -- Conclusion: v(t) = w(t) for all t ≥ 0
  ∀ t, 0 ≤ t →
    let v := S (t + s) u
    let w := S t (S s u)
    v = w := by
  sorry



theorem theorem_42678_problem
  (n m : ℕ)
  (f : (Fin n → ℝ) → (Fin m → ℝ))
  (hf : Differentiable ℝ f)
  (a b : Fin n → ℝ) :
  ∃ c : Fin m → (Fin n → ℝ),
    (∀ i, c i ∈ segment ℝ a b) ∧
    f b - f a = fun i ↦ fderiv ℝ (fun x ↦ f x i) (c i) (b - a) := by
  sorry





