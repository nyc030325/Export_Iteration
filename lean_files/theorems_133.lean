import Mathlib
import Mathlib.Tactic





theorem theorem_721036_problem (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1 / 2) :
  Filter.Tendsto (fun n : ℕ ↦ 1 - (1 - (1 - δ)) ^ n) Filter.atTop (nhds 1) := by
  sorry

theorem theorem_721404_problem (P : ℕ → Prop)
  (h1 : P 0)
  (h2 : ∀ n : ℕ, n ≠ 0 → (∀ k : ℕ, k < n → P k) → P n) :
  ∀ n : ℕ, P n := by
  sorry

theorem theorem_721339_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : Type*} [Fintype n] [DecidableEq n]
  (L : V →ₗ[K] V)
  (u v : Basis n K V)
  (C A A' : Matrix n n K)
  (hC : C = LinearMap.toMatrix u v LinearMap.id)
  (hA : A = LinearMap.toMatrix u u L)
  (hA' : A' = LinearMap.toMatrix v v L) :
  C * A = A' * C := by
  sorry

theorem theorem_721454_problem
  {J : Type*} {X : J → Type*}
  [∀ i, TopologicalSpace (X i)]
  [∀ i, T2Space (X i)] :
  T2Space ((i : J) → X i) := by
  sorry



theorem theorem_721000_problem (lam mu : ℝ) (m : ℤ × ℕ → ℝ)
  (hlam : lam > 0) (hmu : mu > 0)
  (h_absorb : ∀ j : ℤ, m (j, 0) = 0)
  (h_recurrence : ∀ i : ℤ, m (i, 1) = 1 / (lam + mu) + (lam / (lam + mu)) * m (i + 1, 1) + (mu / (lam + mu)) * m (i, 0))
  (h_inv : ∀ i : ℤ, m (i, 1) = m (i + 1, 1)) :
  ∀ i : ℤ, m (i, 1) = 1 / mu := by
  sorry









theorem theorem_721935_problem (T v_max : ℝ) (v : ℝ → ℝ)
  (hT : T ≠ 0)
  (h_quad : ∃ a b c : ℝ, ∀ t, v t = a * t^2 + b * t + c)
  (h_root0 : v 0 = 0)
  (h_rootT : v T = 0)
  (h_vmax : v (T / 2) = v_max) :
  ∀ t, v t = (4 * v_max / T ^ 2) * t * (T - t) := by
  sorry



theorem theorem_721571_problem (m : ℕ) (b : ℕ → ℂ) (hbm : b m ≠ 0) :
  let Q : ℂ → ℂ := fun z ↦ ∑ i in Finset.range (m + 1), b i * z ^ (m - i)
  ∃ R > 0, ∃ C > 0, ∀ z : ℂ, Complex.abs z < R → 1 / Complex.abs (Q z) < C := by
  sorry

theorem theorem_721699_problem (x : ℝ) (h : Real.cos x ≠ 0) :
  HasDerivAt (fun y => Real.tan y - y) (Real.tan x ^ 2) x := by
  sorry



theorem theorem_722079_problem {X : Type*} [TopologicalSpace X] :
  CompactSpace X ↔
  (∀ (ι : Type*) (U : ι → Set X), (∀ i, IsOpen (U i)) → (⋃ i, U i) = Set.univ →
    ∃ (F : Finset ι), (⋃ j ∈ F, U j) = Set.univ) := by
  sorry



theorem theorem_722286_problem
  (E : ℝ → ℝ → ℝ)
  (v₁ v₂ : ℝ)
  (hv₁ : 0 < v₁)
  (hv₂ : 0 < v₂)
  -- The assumption "dynamics ... analogous to independent random walks or Brownian motions"
  -- implies the meeting time scales inversely with velocity.
  (h_analogy : ∃ C : ℝ, 0 < C ∧ ∀ v, 0 < v → E v₁ v = C / v) :
  deriv (fun v ↦ E v₁ v) v₂ < 0 := by
  sorry

theorem theorem_722551_problem
  (n : ℕ) (k : Type*) [Field k]
  [TopologicalSpace (Fin n → k)]
  (Z : Set (Fin n → k)) (hZ : IsIrreducible Z)
  (U₁ U₂ : Set Z)
  (hU₁_open : IsOpen U₁) (hU₂_open : IsOpen U₂)
  (hU₁_ne : U₁.Nonempty) (hU₂_ne : U₂.Nonempty) :
  (U₁ ∩ U₂).Nonempty := by
  sorry

theorem theorem_721926_problem (m : ℂ) (σ : ℝ)
  (hm : ∀ k : ℤ, m ≠ k)
  (hσ_pos : 0 < σ) (hσ_lt_1 : σ < 1)
  (hσ_sep_1 : 0.5 + m.re < σ) (hσ_sep_2 : σ < 1.5 + m.re) :
  let F : ℂ → ℂ := fun s ↦ Complex.Gamma s * Complex.Gamma (1 - s) * Complex.Gamma (s - 0.5 - m) * Complex.Gamma (1.5 + m - s)
  (1 / (2 * (π : ℂ))) * ∫ t : ℝ, F (σ + t * I) = π * (m + 0.5) / Complex.cos (π * m) := by
  sorry

theorem theorem_722374_problem
  (W : Set ℝ) (x₀ : ℝ)
  (hW : IsClosed W)
  (A : Set ℝ) (hA : A = { p : ℝ | Set.Ico x₀ (x₀ + p) ⊆ W })
  (hA_nonempty : A.Nonempty)
  (hA_bdd : BddAbove A)
  (r : ℝ) (hr : r = sSup A) :
  x₀ + r ∈ W := by
  sorry

theorem theorem_722452_problem (y x : ℝ) (hy : y ≠ 0)
  (h : y = Real.tan (x * y)) :
  ∃ k : ℤ, x = (Real.arctan y + (k : ℝ) * Real.pi) / y := by
  sorry





theorem theorem_722279_problem (n : ℕ) (hn : n > 0) :
  let X : ℝ → ℝ := id
  let X_n : ℝ → ℝ := fun t ↦ (⌊(n : ℝ) * t⌋ : ℝ) / (n : ℝ)
  ∫ t in Set.Icc (0 : ℝ) 1, (X t - X_n t) = 1 / (2 * (n : ℝ)) := by
  sorry

theorem theorem_722764_problem
  (R : Type*) [EuclideanDomain R]
  (h1 : ∀ x : Rˣ, x = 1)
  (h2 : ¬ Algebra.FiniteType ℤ R) :
  (¬ Nonempty (R ≃+* ℤ)) ∧
  (∀ (k : Type*) [Field k], ¬ Nonempty (R ≃+* Polynomial k)) := by
  sorry



theorem theorem_723016_problem (k : ℕ) (a b : ℤ)
  (p : ℕ → ℕ) (hp : ∀ i, p i = Nat.nth Nat.Prime i)
  (P_k : ℕ) (hP_k : P_k = ∏ i in Finset.range k, p i)
  (h_cong : ∀ i < k, a ≡ b [ZMOD (p i : ℤ)]) :
  a ≡ b [ZMOD (P_k : ℤ)] := by
  sorry

theorem theorem_722809_problem {H : Type*} [Group H] (T : Set H)
  (h : Subgroup.closure T ≠ ⊤) :
  Subgroup.closure T < ⊤ := by
  sorry



theorem theorem_723043_problem (n : ℕ) (f : (Fin n → ℝ) → (Fin n → ℝ)) (x_star : Fin n → ℝ)
  (h_diff : ContDiff ℝ 1 f)
  (h_root : f x_star = 0)
  (h_det : LinearMap.det (fderiv ℝ f x_star).toLinearMap ≠ 0) :
  ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x_star ∈ U ∧
    ∀ x ∈ U, f x = 0 → x = x_star := by
  sorry

theorem theorem_723145_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (v : E) (N_prev N_curr : E) (ε : ℝ)
  (h_eps : ε > 0)
  (h_unit_prev : ‖N_prev‖ = 1)
  (h_unit_curr : ‖N_curr‖ = 1)
  (h_denom : 1 + inner N_prev N_curr ≠ (0 : ℝ))
  (v' : E)
  (h_infl_prev : inner (v' - v) N_prev = ε)
  (h_infl_curr : inner (v' - v) N_curr = ε) :
  v' = v + (ε / (1 + inner N_prev N_curr)) • (N_prev + N_curr) := by
  sorry





theorem theorem_723775_problem {X : Type*} [TopologicalSpace X] (K : Set X) :
  IsCompact K ↔
  (∀ (ι : Type*) (U : ι → Set X), (∀ i, IsOpen (U i)) → K ⊆ ⋃ i, U i →
    ∃ s : Finset ι, K ⊆ ⋃ i ∈ s, U i) := by
  sorry







theorem theorem_723588_problem (x : ℝ) (hx : |x| < 1)
  (f : ℝ → ℝ) (hf : ∀ y, f y = ∑' n : ℕ, if 2 ≤ n then (n : ℝ)^2 * y ^ n else 0)
  (g : ℝ → ℝ) (hg : ∀ y, g y = ∑' n : ℕ, if 1 ≤ n then (n : ℝ) * y ^ n else 0) :
  g x = x + ∫ t in (0)..x, f t / t := by
  sorry





theorem theorem_724048_problem
  (I X : Type*)
  [Nonempty I]
  [TopologicalSpace X] [T2Space X] :
  IsClosed { f : I → X | ∃ c : X, f = Function.const I c } := by
  sorry







theorem theorem_724133_problem 
  (x y : ℝ)
  (f : ℝ → ℝ → ℝ)
  (p_w_x : ℝ → ℝ)
  (roots : Finset ℝ)
  -- Condition: f is differentiable with respect to w
  (h_diff : Differentiable ℝ (f x ·))
  -- Condition: w_i are the discrete solutions to f(x, w) = y
  (h_roots : ∀ w, f x w = y ↔ w ∈ roots)
  -- Condition: Derivatives at roots are non-zero (non-degenerate)
  (h_regular : ∀ w ∈ roots, deriv (f x ·) w ≠ 0)
  -- Definition: Abstract functional representing the integral ∫ δ(g(w)) h(w) dw
  (dirac_integral : (ℝ → ℝ) → (ℝ → ℝ) → ℝ)
  -- Condition: The fundamental property of the Dirac delta function regarding roots
  (h_dirac_prop : ∀ (g : ℝ → ℝ) (h : ℝ → ℝ) (rs : Finset ℝ), 
    (∀ w, g w = 0 ↔ w ∈ rs) → 
    (∀ w ∈ rs, deriv g w ≠ 0) → 
    dirac_integral g h = ∑ w in rs, h w / |deriv g w|)
  -- Condition: p(y|x) is given by the Dirac delta function expression
  (p_y_x : ℝ)
  (h_def_p : p_y_x = dirac_integral (fun w ↦ f x w - y) p_w_x) :
  -- Conclusion: The summation formula
  p_y_x = ∑ w in roots, p_w_x w / |deriv (f x ·) w| := by
  sorry









theorem theorem_725033_problem (a b : ℝ) (S : Set ℝ) 
  (h1 : S ⊆ Set.Icc a b) 
  (h2 : S.Nonempty) : 
  sSup S ∈ Set.Icc a b := by
  sorry





theorem theorem_724948_problem (k : ℕ) (hk : k > 0) :
  (X ^ (2 ^ (k - 1)) - 1 : Polynomial ℤ) ∣ (X ^ (2 ^ k) - 1) := by
  sorry



theorem theorem_724900_problem (p n k : ℕ) (hp : p.Prime) (hk : k ≤ n) :
  padicValNat p (Nat.choose n k) =
  ((n - (Nat.digits p n).sum) - (k - (Nat.digits p k).sum) -
   ((n - k) - (Nat.digits p (n - k)).sum)) / (p - 1) := by
  sorry



theorem theorem_724176_problem : Function.Bijective h := by
  sorry







theorem theorem_725197_problem
  (n m : ℕ)
  (c₁ c₂ : EuclideanSpace ℝ (Fin n))
  (r₁ r₂ : ℝ)
  (B₁ B₂ U : Set (EuclideanSpace ℝ (Fin n)))
  (hB₁ : B₁ = Metric.ball c₁ r₁)
  (hB₂ : B₂ = Metric.ball c₂ r₂)
  (h_disj : Disjoint B₁ B₂)
  (hU : U = B₁ ∪ B₂)
  (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
  (h_analytic : AnalyticOn ℝ f U)
  (p₁ p₂ : EuclideanSpace ℝ (Fin m))
  (h_map1 : f '' B₁ = {p₁})
  (h_map2 : f '' B₂ = {p₂})
  (h_notin1 : p₁ ∉ f '' B₂)
  (h_notin2 : p₂ ∉ f '' B₁) :
  ¬ IsConnected (f '' U) := by
  sorry

theorem theorem_725177_problem
  (X : Type*)
  (hX : Nonempty X)
  (F : X → ℝ)
  (S : Set ℝ)
  (hS : S = Set.range F) :
  sSup S = sSup (Set.range F) := by
  sorry



theorem theorem_725128_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  {k : ℕ} (v : Fin k → V) :
  ((List.ofFn v).map (ExteriorAlgebra.ι K)).prod = 0 ↔ ¬ LinearIndependent K v := by
  sorry





theorem theorem_725866_problem (A : Type*) [Countable A] [Infinite A] :
  ¬ ∃ f : A → Set A, Function.Bijective f := by
  sorry



theorem theorem_725628_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  (A : V →ₗ[K] W)
  (n : ℕ)
  (x : Fin n → V)
  (h_indep : LinearIndependent K (A ∘ x))
  (h_ker : ∀ v : V, A v = 0 → v = 0) :
  Function.Injective A := by
  sorry



theorem theorem_725360_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (norm_E norm_g : V → ℝ)
  (h_norm_E : ∀ v : V, norm_E v = 0 ↔ v = 0)
  (h_norm_g : ∀ v : V, norm_g v = 0 ↔ v = 0)
  (v : V)
  (h : norm_E v = 0) :
  norm_g v = 0 := by
  sorry

theorem theorem_724702_problem (R : Type*) [CommRing R] :
  ∀ (f : LaurentPolynomial R), IsUnit f ↔
  ∃ (r : R) (n : ℤ), IsUnit r ∧ f = LaurentPolynomial.C r * LaurentPolynomial.T n := by
  sorry







theorem theorem_726058_problem (y lam : ℝ) (hlam : lam ≥ 0) :
  let f := fun (θ : ℝ) ↦ (1 / 2 : ℝ) * (y - θ)^2 + lam * |θ|
  let theta_hat := Real.sign y * (|y| - lam) * (if |y| > lam then (1 : ℝ) else 0)
  ∀ θ, f theta_hat ≤ f θ := by
  sorry



theorem theorem_726008_problem (A B : Set ℝ)
  (hA : interior (closure A) = ∅)
  (hB : interior (closure B) = ∅) :
  interior (closure (A ∪ B)) = ∅ := by
  sorry

theorem theorem_726385_problem (z : ℝ → ℝ → ℝ) (r θ : ℝ)
  (h : ContDiff ℝ 2 (Function.uncurry z)) :
  let x := r * Real.cos θ
  let y := r * Real.sin θ
  let z_polar := fun r' => z (r' * Real.cos θ) (r' * Real.sin θ)
  deriv (deriv z_polar) r =
    (deriv (fun x' => deriv (fun x'' => z x'' y) x') x) * (Real.cos θ)^2 +
    2 * (deriv (fun x' => deriv (fun y' => z x' y') y) x) * (Real.sin θ * Real.cos θ) +
    (deriv (fun y' => deriv (fun y'' => z x y'') y') y) * (Real.sin θ)^2 := by
  sorry

theorem theorem_726483_problem (n a b c : ℕ) 
  (hn : n ≥ 3) 
  (ha : a > 0) 
  (hb : b > 0) 
  (hc : c > 0) : 
  a^n + b^n ≠ c^n := by
  sorry





theorem theorem_726494_problem
  (Y : Type*) [TopologicalSpace Y]
  (X : Set Y)
  (ι : X → Y)
  (hι : ι = Subtype.val) :
  let Z := Sum Y X
  let R : Z → Z → Prop := fun z w ↦ ∃ x : X, z = Sum.inr x ∧ w = Sum.inl (ι x)
  let Q := Quotient (EqvGen.Setoid R)
  Nonempty (Q ≃ₜ Y) := by
  sorry

theorem theorem_726814_problem (a b : ℝ) : Real.exp a * Real.exp b = Real.exp (a + b) := by
  sorry

theorem theorem_726581_problem {X : Type*} [TopologicalSpace X] (A : Set X) :
  IsNowhereDense A ↔ ∀ U, IsOpen U → U ⊆ closure A → U = ∅ := by
  sorry



















theorem theorem_727091_problem 
  {X Y Ξ : Type*} 
  (F : X → Y)
  (p : X → Ξ → ℝ)
  (q : Y → Ξ → ℝ)
  (p_joint : X → Y → Ξ → ℝ)
  (p_cond : X → Y → Ξ → ℝ)
  (δ : Y → Y → ℝ)
  (r : X → Ξ → ℝ)
  (h_r_def : ∀ x ξ, r x ξ = p x ξ / q (F x) ξ)
  (h_joint_def : ∀ x y ξ, p_joint x y ξ = p x ξ * δ (F x) y)
  (h_cond_def : ∀ x y ξ, q y ξ ≠ 0 → p_cond x y ξ = p_joint x y ξ / q y ξ)
  (h_delta_prop : ∀ y₁ y₂, δ y₁ y₂ ≠ 0 → y₁ = y₂)
  (x : X) (y : Y) (ξ : Ξ)
  (hq_nz : q y ξ ≠ 0)
  (hqF_nz : q (F x) ξ ≠ 0) :
  p_cond x y ξ = r x ξ * δ (F x) y := by
  sorry

theorem theorem_727309_problem
  {S O : Type*}
  (n : ℕ) (hn : n > 0)
  (y : ℕ → S) (x : ℕ → O)
  (p_joint : ℝ)
  (p_state : ℝ)
  (p_obs_given_state : ℝ)
  (p_init : S → ℝ)
  (p_trans : S → S → ℝ)
  (p_emit : O → S → ℝ)
  (h1 : p_joint = p_state * p_obs_given_state)
  (h2 : p_state = p_init (y 0) * ∏ i in Finset.Ico 1 n, p_trans (y i) (y (i - 1)))
  (h3 : p_obs_given_state = ∏ i in Finset.range n, p_emit (x i) (y i)) :
  p_joint = (p_init (y 0) * ∏ i in Finset.Ico 1 n, p_trans (y i) (y (i - 1))) *
            (∏ i in Finset.range n, p_emit (x i) (y i)) := by
  sorry



