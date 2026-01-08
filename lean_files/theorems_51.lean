import Mathlib
import Mathlib.Tactic



























theorem theorem_273903_problem 
  (D₁ D₂ α : Set ℂ)
  (F : ℂ → ℂ)
  -- Conditions for D₁
  (hD₁_open : IsOpen D₁)
  (hD₁_conn : IsConnected D₁)
  (hD₁_sc : SimplyConnectedSpace D₁)
  -- Conditions for D₂
  (hD₂_open : IsOpen D₂)
  (hD₂_conn : IsConnected D₂)
  (hD₂_sc : SimplyConnectedSpace D₂)
  -- Disjointness
  (h_disj : Disjoint D₁ D₂)
  -- α is the common boundary segment
  (hα_bound : α ⊆ frontier D₁ ∩ frontier D₂)
  (hα_conn : IsConnected α)
  (hα_int : interior α = ∅)
  -- The combined set is a domain (open)
  (h_union_open : IsOpen (D₁ ∪ D₂ ∪ α))
  -- F is continuous on the union (implies agreements on boundary)
  (hF_cont : ContinuousOn F (D₁ ∪ D₂ ∪ α))
  -- F is analytic on the components
  (hF_an1 : DifferentiableOn ℂ F D₁)
  (hF_an2 : DifferentiableOn ℂ F D₂) :
  -- Conclusion: F is analytic on the whole domain
  DifferentiableOn ℂ F (D₁ ∪ D₂ ∪ α) := by
  sorry









theorem theorem_275066_problem (p : ℕ) [Fact (Nat.Prime p)]
  (V : Type*) [AddCommGroup V] [Module (ZMod p) V] [Fintype V]
  (h : FiniteDimensional.finrank (ZMod p) V = 2) :
  Fintype.card V = p ^ 2 := by
  sorry











theorem theorem_274711_problem
  (n : ℕ)
  (c₁ : ℝ)
  (v xₖ : EuclideanSpace ℝ (Fin n))
  (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  (hA : IsSelfAdjoint A)
  (x : EuclideanSpace ℝ (Fin n)) :
  gradient (fun y => c₁ + inner v y + (1 / 2 : ℝ) * inner (y - xₖ) (A (y - xₖ))) x =
  v + A (x - xₖ) := by
  sorry



theorem theorem_274467_problem (a b : ℂ)
  (h1 : a + b = 6)
  (h2 : a^2 + b^2 = 14) :
  (a = 3 - I * Real.sqrt 2 ∧ b = 3 + I * Real.sqrt 2) ∨
  (a = 3 + I * Real.sqrt 2 ∧ b = 3 - I * Real.sqrt 2) := by
  sorry

theorem theorem_275352_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (K : Set X)
  (M : Submodule ℝ X) [FiniteDimensional ℝ M]
  (A : X →L[ℝ] NormedSpace.Dual ℝ X)
  (x : X) :
  ContinuousOn (fun z ↦ (A z) x) (K ∩ (M : Set X)) := by
  sorry















theorem theorem_275227_problem
  {X Θ I : Type} [Fintype I] [Nonempty I]
  (f_tilde : X → Θ → ℝ)
  (x : X)
  (θ : I → Θ)
  (p : I → ℝ)
  (h_model : ∀ i, p i = Real.exp (f_tilde x (θ i)) / ∑ j, Real.exp (f_tilde x (θ j))) :
  ∃ C : ℝ, ∀ i, p i = C * Real.exp (f_tilde x (θ i)) := by
  sorry

theorem theorem_275647_problem (y₁ y₂ : ℝ → ℝ)
  (hy₁ : Differentiable ℝ y₁) (hy₂ : Differentiable ℝ y₂)
  (h₁ : ∀ x, deriv y₁ x = 3 * y₁ x - y₂ x)
  (h₂ : ∀ x, deriv y₂ x = y₁ x + y₂ x) :
  ∃ a b : ℝ, ∀ x,
    y₁ x = (a * x + b) * Real.exp (2 * x) ∧
    y₂ x = (a * x - a + b) * Real.exp (2 * x) := by
  sorry







theorem theorem_275745_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (E : Set X)
  (A : Set (X →L[ℝ] X))
  (M : ℝ)
  (x₀ : X)
  (r : ℝ)
  (h_M_pos : M > 0)
  (h_r_pos : r > 0)
  (h_geom : Metric.ball x₀ r ⊆ E)
  (h_bound : ∀ T ∈ A, ∀ x ∈ E, ‖T x‖ ≤ M) :
  ∀ T ∈ A, ∀ y : X, ‖y‖ < r → ‖T y‖ ≤ 2 * M := by
  sorry









theorem theorem_276210_problem
  (n : ℕ)
  (H : Matrix (Fin n) (Fin n) ℝ)
  (v : Fin n → ℝ)
  (hH_symm : H.IsSymm)
  (hH_posDef : H.PosDef)
  (f : (Fin n → ℝ) → ℝ)
  (hf : f = fun t => Matrix.dotProduct t (H.mulVec t) - Matrix.dotProduct v t) :
  let t_sol := (1 / 2 : ℝ) • (H⁻¹.mulVec v)
  (∀ t, f t_sol ≤ f t) ∧ (∀ t, f t = f t_sol → t = t_sol) := by
  sorry



theorem theorem_275899_problem
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix m m ℝ)
  (B : Matrix m n ℝ)
  (h_semi_orth : B.transpose * B = 1) :
  ∀ (μ : ℝ), μ ≠ 0 →
    (Module.End.HasEigenvalue (Matrix.toLin' (A * B * B.transpose)) μ ↔
     Module.End.HasEigenvalue (Matrix.toLin' (B.transpose * A * B)) μ) := by
  sorry















theorem theorem_276849_problem
  (n : ℕ)
  (U : Set (Fin n → ℝ))
  (hU : IsOpen U)
  (f : (Fin n → ℝ) → (Fin n → ℝ))
  (g : (Fin n → ℝ) → (Fin n → ℝ))
  (hf : ContDiffOn ℝ ⊤ f U)
  (hg : ContDiffOn ℝ ⊤ g (f '' U))
  (hinv_l : ∀ x ∈ U, g (f x) = x)
  (hinv_r : ∀ y ∈ f '' U, f (g y) = y)
  (x : Fin n → ℝ)
  (hx : x ∈ U)
  (grad_x_f : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
  (h_grad_x_f : grad_x_f = fderiv ℝ f x)
  (grad_f_x : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
  (h_grad_f_x : grad_f_x = fderiv ℝ g (f x)) :
  grad_f_x.comp grad_x_f = ContinuousLinearMap.id ℝ (Fin n → ℝ) ∧
  grad_x_f.comp grad_f_x = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
  sorry









theorem theorem_276944_problem (x y u v t : ℝ) 
  (h1 : x = u + v) 
  (h2 : y = u - v) : 
  x + y ≤ 2 * t ↔ u ≤ t := by
  sorry

theorem theorem_276920_problem {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [Module.Finite F V] (T S : V →ₗ[F] V) :
  LinearMap.det (T * S) = LinearMap.det T * LinearMap.det S := by
  sorry





theorem theorem_276997_problem
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  (f : Matrix m n ℝ)
  (d : n → ℝ)
  (h1 : (f.transpose * f).PosDef)
  (h2 : ∀ i, 0 < d i ^ 2) :
  let A := f.transpose * f + Matrix.diagonal (fun i => d i ^ 2)
  IsUnit A := by
  sorry









theorem theorem_277573_problem
  (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (hf : Differentiable ℝ f)
  (x p : EuclideanSpace ℝ (Fin n))
  (t : ℝ) :
  deriv (fun t => f (x + t • p)) t = inner (gradient f (x + t • p)) p := by
  sorry



theorem theorem_277013_problem 
  (D A : Set ℂ) 
  (hD_open : IsOpen D) 
  (hD_conn : IsConnected D) 
  (hA_open : IsOpen A) 
  (hA_ne : A ≠ Set.univ) 
  (hDA : closure D ⊆ A) 
  (hD_comp : IsCompact (closure D)) : 
  ∃ ε > 0, Metric.thickening ε D ⊆ A := by
  sorry







theorem theorem_277604_problem
  (n : ℕ)
  (U V : Set (Fin n → ℝ))
  (T : (Fin n → ℝ) → (Fin n → ℝ))
  (hU_open : IsOpen U)
  (hV_open : IsOpen V)
  (hU_conn : IsConnected U)
  (hT_smooth : ContDiffOn ℝ ⊤ T U)
  (hT_bij : Set.BijOn T U V)
  (hT_inv : ∃ g, ContDiffOn ℝ ⊤ g V ∧ Set.LeftInvOn g T U ∧ Set.RightInvOn g T V)
  (h_det_ne_zero : ∀ p ∈ U, LinearMap.det (fderiv ℝ T p).toLinearMap ≠ 0) :
  (∀ p ∈ U, 0 < LinearMap.det (fderiv ℝ T p).toLinearMap) ∨
  (∀ p ∈ U, LinearMap.det (fderiv ℝ T p).toLinearMap < 0) := by
  sorry



theorem theorem_278123_problem
  (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
  (f : X → ℂ) (hf : Continuous f) (h_nez : ∀ x, f x ≠ 0)
  (g : X → ℝ) (hg : ∀ x, g x = Complex.abs (f x)) :
  ∃ a b : ℝ, Set.range g = Set.Icc a b := by
  sorry



theorem theorem_277826_problem
  (n m : ℕ)
  (X : Matrix (Fin n) (Fin m) ℝ)
  (y : Fin n → ℝ)
  (β : Fin m → ℝ)
  (p : Fin n → ℝ)
  (i : Fin m)
  (h_normal : X.transpose.mulVec (X.mulVec β) = X.transpose.mulVec y)
  (h_p : p = X.mulVec β)
  (h_cat : ∀ j : Fin n, X.transpose i j = 0 ∨ X.transpose i j = 1) :
  ∑ j in Finset.univ.filter (fun j => X.transpose i j = 1), p j =
  ∑ j in Finset.univ.filter (fun j => X.transpose i j = 1), y j := by
  sorry

theorem theorem_277734_problem
  {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
  (X : Matrix n p ℝ)
  (Y : Matrix n Unit ℝ)
  (h_inv : Invertible (X.transpose * X)) :
  let w_hat := (⅟(X.transpose * X)) * X.transpose * Y
  let L := fun (w : Matrix p Unit ℝ) ↦ (Y - X * w).transpose * (Y - X * w)
  ∀ w : Matrix p Unit ℝ, (L w_hat) () () ≤ (L w) () () := by
  sorry

theorem theorem_278106_problem
  (V : Type*) [AddCommGroup V] [Module ℝ V]
  [FiniteDimensional ℝ V]
  (n : ℕ)
  (h_dim : FiniteDimensional.finrank ℝ V = n)
  (h_odd : Odd n)
  (phi : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (h_skew : ∀ v w, phi v w = - phi w v) :
  ∃ v : V, v ≠ 0 ∧ ∀ w : V, phi v w = 0 := by
  sorry





theorem theorem_278173_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (ω : V →ₗ[F] V →ₗ[F] F)
  (ω_l : V →ₗ[F] Module.Dual F V)
  (h_l : ∀ x, ω_l x = ω x)
  (ω_r : V →ₗ[F] Module.Dual F V)
  (h_r : ∀ y x, ω_r y x = ω x y) :
  Function.Bijective ω_l ↔ Function.Bijective ω_r := by
  sorry











theorem theorem_278610_problem
  {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  (A : X →L[ℝ] Y)
  (h : ∀ n : ℕ, ∃ K : Set Y, IsCompact K ∧ A '' (Metric.closedBall 0 n) ⊆ K) :
  IsCompactOperator A := by
  sorry













theorem theorem_278985_problem {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] (n m : ℕ) (S : Set V)
  (h_dim : FiniteDimensional.finrank F V = n)
  (h_card : S.ncard = m)
  (h_cond : m > n) :
  ¬ LinearIndependent F ((↑) : S → V) := by
  sorry





