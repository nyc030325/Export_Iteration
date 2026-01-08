import Mathlib
import Mathlib.Tactic







theorem theorem_415945_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (s : ℕ → V) (t : V) (r : ℝ) (L : ℝ)
  (hr : r > 0)
  (h_bound : ∀ n, ‖s n - t‖ < r)
  (h_lim : Filter.Tendsto (fun n ↦ ‖s n - t‖) Filter.atTop (nhds L)) :
  L ≤ r := by
  sorry





theorem theorem_416213_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (M : Submodule 𝕜 X)
  (hM : IsClosed (M : Set X)) :
  IsOpenMap (Submodule.mkQ M) := by
  sorry

theorem theorem_416044_problem (n : ℕ) (A V : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
  (V.transpose * A * V) k k = ∑ s : Fin n, ∑ t : Fin n, A s t * V s k * V t k := by
  sorry



theorem theorem_416300_problem
  (Ms : List (Matrix (Fin 2) (Fin 2) ℝ))
  (norm : Matrix (Fin 2) (Fin 2) ℝ → ℝ)
  (h_norm_pos : ∀ M ∈ Ms, norm M > 0)
  (k : ℝ := (Ms.map norm).prod)
  (A : Matrix (Fin 2) (Fin 2) ℝ := (Ms.map (fun M => (norm M)⁻¹ • M)).prod)
  (M : Matrix (Fin 2) (Fin 2) ℝ := Ms.prod)
  (I2 : Matrix (Fin 2) (Fin 2) ℝ := 1)
  (h_det_M_pos : 0 < Matrix.det (I2 + M))
  (h_det_A_pos : 0 < Matrix.det ((k⁻¹ • I2) + A)) :
  Real.log (Matrix.det (I2 + M)) = 2 * Real.log k + Real.log (Matrix.det ((k⁻¹ • I2) + A)) := by
  sorry



theorem theorem_416603_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  (T : V →ₗ[K] W)
  (q : V →ₗ[K] K)
  (hT_surj : Function.Surjective T)
  (h_ker : LinearMap.ker T ≤ LinearMap.ker q) :
  ∃ q' : W → K, ∀ x : V, q' (T x) = q x := by
  sorry

theorem theorem_416510_problem
  {K V V' : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V']
  (T : V →ₗ[K] V') :
  Nonempty ((V ⧸ LinearMap.ker T) ≃ₗ[K] LinearMap.range T) := by
  sorry



theorem theorem_415875_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (A : X →L[ℝ] X)
  (T : ℝ → X →L[ℝ] X)
  (hT_deriv : ∀ (y : X) (s : ℝ), HasDerivAt (fun u ↦ T u y) (A (T s y)) s)
  (hT_zero : T 0 = 1)
  (x : X)
  (t : ℝ) :
  ∫ s in (0)..t, A (T s x) = t • (A x) + ∫ s in (0)..t, ∫ v in (0)..s, (A ^ 2) (T v x) := by
  sorry







theorem theorem_416876_problem (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (q : ℝ)
  (hn : n > 0)
  (hq : q = ∑ i, ∑ j, Q i j)
  (h_sym : Q.IsSymm)
  (h_pd : Q.PosDef) :
  0 < q := by
  sorry











theorem theorem_416677_problem 
  (m₁ m₂ r : EuclideanSpace ℝ (Fin 3)) 
  (hr : r ≠ 0) :
  fderiv ℝ (fun x => fderiv ℝ (fun y => 1 / ‖y‖) x m₂) r m₁ = 
  3 * inner m₁ r * inner m₂ r / ‖r‖ ^ 5 - inner m₁ m₂ / ‖r‖ ^ 3 := by
  sorry

theorem theorem_416746_problem
  {n : ℕ}
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  (T : V →ₗ[F] V)
  (v : Basis (Fin n) F V)
  (L : AlternatingMap F V F (Fin n))
  (hL : L v = 1) :
  L (T ∘ v) = (LinearMap.det T) * L v := by
  sorry

theorem theorem_417192_problem {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix m n ℝ) :
  {v : n → ℝ | Matrix.mulVec A v = 0} =
  {v : n → ℝ | ∀ w, w ∈ Set.range (Matrix.mulVec A.transpose) → Matrix.dotProduct v w = 0} := by
  sorry

theorem theorem_417346_problem
  (n : ℕ)
  (l : ℝ)
  (hl : 0 < l)
  (x y xk yk : EuclideanSpace ℝ (Fin n))
  (f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
  (h_f : f = fun p ↦ ‖p.1 - p.2‖^2 - l^2)
  (L : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)
  (h_L : HasFDerivAt f L (xk, yk)) :
  f (xk, yk) + L (x - xk, y - yk) =
    ‖xk - yk‖^2 + 2 * inner (xk - yk) ((x - xk) - (y - yk)) - l^2 := by
  sorry



theorem theorem_417260_problem (n : ℕ) (x y : EuclideanSpace ℝ (Fin n))
  (c : ℝ) (hc : 1 < c) :
  ‖x - y‖^2 ≥ ‖x‖^2 / c - ‖y‖^2 / (c - 1) := by
  sorry



theorem theorem_417244_problem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
  ¬ ∃ A : H →L[ℝ] H, ∀ x : H, inner (A x) x = (1 : ℝ) := by
  sorry





theorem theorem_417082_problem (n : ℕ) (θ : ℝ)
  (T : Matrix (Fin n) (Fin n) ℝ)
  (R_x : ℝ → Matrix (Fin n) (Fin n) ℝ)
  (P : Fin n → ℝ)
  (hT : Invertible T) :
  Matrix.mulVec (⅟T) (Matrix.mulVec (R_x θ) (Matrix.mulVec T P)) = 
  Matrix.mulVec (⅟T * R_x θ * T) P := by
  sorry











theorem theorem_417752_problem
  (L a : ℝ)
  (hL : L > 0)
  (u0 : ℝ → ℝ)
  (u v : ℝ → ℝ → ℝ)
  (h_u_pde : ∀ x ∈ Set.Icc 0 L, ∀ t > 0, deriv (fun t' => u x t') t = a^2 * deriv (fun x' => deriv (fun x'' => u x'' t) x') x)
  (h_v_pde : ∀ x ∈ Set.Icc 0 L, ∀ t > 0, deriv (fun t' => v x t') t = a^2 * deriv (fun x' => deriv (fun x'' => v x'' t) x') x)
  (h_u_bc_0 : ∀ t > 0, u 0 t = 0)
  (h_u_bc_L : ∀ t > 0, u L t = 0)
  (h_v_bc_0 : ∀ t > 0, v 0 t = 0)
  (h_v_bc_L : ∀ t > 0, v L t = 0)
  (h_u_ic : ∀ x ∈ Set.Icc 0 L, u x 0 = u0 x)
  (h_v_ic : ∀ x ∈ Set.Icc 0 L, v x 0 = u0 x) :
  ∀ x ∈ Set.Icc 0 L, ∀ t > 0, u x t = v x t := by
  sorry



theorem theorem_417939_problem
  (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (S : Submodule ℝ E) :
  IsCompl S S.orthogonal ∧ Nonempty (S.orthogonal ≃ₗ[ℝ] E ⧸ S) := by
  sorry



theorem theorem_418243_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  {n : ℕ}
  (e : Fin n → V)
  (h_indep : LinearIndependent F e)
  (h_span : Submodule.span F (Set.range e) = ⊤)
  (v : V) :
  ∃! (c : Fin n → F), ∑ i, c i • e i = v := by
  sorry

theorem theorem_418496_problem {n : ℕ} {R : Type*} [CommRing R]
  (A : Matrix (Fin n) (Fin n) R)
  (i j : Fin n)
  (h_idx : i < j)
  (h_eq : ∀ k, A k i = A k j) :
  Matrix.det A = 0 := by
  sorry



theorem theorem_418165_problem
  (F : Type*) [Field F]
  (V : Type*) [AddCommGroup V] [Module F V]
  (u : V →ₗ[F] V)
  (h_dim : FiniteDimensional.finrank F V = 2)
  (h_not_scalar : ∀ c : F, u ≠ c • LinearMap.id) :
  ∃ (v : V) (b : Basis (Fin 2) F V),
    b 0 = v ∧
    b 1 = u v ∧
    LinearMap.toMatrix b b u = !![0, -LinearMap.det u; 1, LinearMap.trace F V u] := by
  sorry





theorem theorem_418391_problem
  (n l : ℕ)
  (hl : l ≤ n)
  (E : Type*) [AddCommGroup E] [Module ℝ E]
  (b : Basis (Fin n) ℝ E)
  (L : Submodule ℝ E)
  (hL : L = Submodule.span ℝ (b '' {i : Fin n | i.val < l})) :
  L = ⨅ (i : Fin n) (_ : l ≤ i.val), LinearMap.ker (b.coord i) := by
  sorry

theorem theorem_418663_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (M : Submodule 𝕜 H)
  (h_dense : Dense (M : Set H))
  (h_proper : M ≠ ⊤) :
  M.orthogonal = ⊥ := by
  sorry



theorem theorem_418353_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {n : Type*} [Fintype n] [DecidableEq n]
  (G : Basis n F V)
  (H : Basis n F V)
  (T : V →ₗ[F] V)
  (A B C : Matrix n n F)
  (hC : C = G.toMatrix H)
  (hA : A = LinearMap.toMatrix G G T)
  (hB : B = LinearMap.toMatrix H H T) :
  B = C * A * C⁻¹ := by
  sorry



theorem theorem_418699_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (B : LinearMap.BilinForm ℝ V)
  (h_symm : B.IsSymm)
  (h_nondeg : B.Nondegenerate)
  (K : Submodule ℝ V)
  (h_iso : ∀ u ∈ K, ∀ v ∈ K, B u v = 0) :
  FiniteDimensional.finrank ℝ K ≤ FiniteDimensional.finrank ℝ V / 2 := by
  sorry



theorem theorem_419335_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [Field K]
  (B : Matrix n n K)
  (v u : n → K)
  (h : (B * (1 + Matrix.vecMulVec v u)).det = 0) :
  B.det = 0 ∨ (1 + Matrix.vecMulVec v u).det = 0 := by
  sorry

theorem theorem_418956_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  (A : V ≃L[𝕜] V) (B : V ≃L[𝕜] V) (X : V →L[𝕜] V) :
  fderiv 𝕜 (fun (T : V →L[𝕜] V) ↦ (A : V →L[𝕜] V).comp T) (B : V →L[𝕜] V) X =
  (A : V →L[𝕜] V).comp X := by
  sorry

theorem theorem_418843_problem
  {K : Type*} [NontriviallyNormedField K]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
  (g : X →ₗ[K] X)
  (hg_cont : Continuous g)
  (x_seq : ℕ → X)
  (x : X)
  (h_weak : ∀ φ : X →L[K] K, Filter.Tendsto (fun n ↦ φ (x_seq n)) Filter.atTop (nhds (φ x))) :
  ∀ φ : X →L[K] K, Filter.Tendsto (fun n ↦ φ (g (x_seq n))) Filter.atTop (nhds (φ (g x))) := by
  sorry



theorem theorem_418549_problem
  (K : Type*) [Field K]
  (n : ℕ) (hn : n > 3)
  (S D A : Set (Matrix (Fin n) (Fin n) K))
  (hS : S = {m | ∃ i j, m = Matrix.stdBasisMatrix i j 1 - Matrix.stdBasisMatrix j i 1})
  (hD : D = {m | ∃ i j, m = Matrix.stdBasisMatrix i i 1 + Matrix.stdBasisMatrix j j 1})
  (hA : A = {m | ∃ i j, m = Matrix.stdBasisMatrix i j 1 + Matrix.stdBasisMatrix j i 1}) :
  Submodule.span K (S ∪ D ∪ A) = ⊤ := by
  sorry

theorem theorem_419272_problem
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : ℝ → E) (D : ℝ → (E →L[ℝ] F)) (t : ℝ)
  (hf : DifferentiableAt ℝ f t)
  (hD : DifferentiableAt ℝ D t) :
  deriv (fun s ↦ (D s) (f s)) t = (deriv D t) (f t) + (D t) (deriv f t) := by
  sorry

theorem theorem_418830_problem :
  let v : ℂ × ℂ := (1, 1 + Complex.I)
  let V : Submodule ℂ (ℂ × ℂ) := Submodule.span ℂ {v}
  let Re_V : Set (ℝ × ℝ) := {w | ∃ z ∈ V, w = (z.1.re, z.2.re)}
  Re_V = Set.univ := by
  sorry







theorem theorem_418775_problem (n : ℕ) (E : Type*) [AddCommGroup E] [Module ℝ E]
  [FiniteDimensional ℝ E] (h_dim : FiniteDimensional.finrank ℝ E = n)
  (S : Set E) (hS : S.Finite) (x y : E)
  (hx : x ∈ convexHull ℝ S) (hy : y ∈ convexHull ℝ S) :
  ∃ S' : Set E, S' ⊆ S ∧ S'.ncard ≤ 2 * n + 1 ∧ x ∈ convexHull ℝ S' ∧ y ∈ convexHull ℝ S' := by
  sorry

theorem theorem_418935_problem
  {F : Type*} [Field F]
  {n m : ℕ}
  (T : (Fin n → F) →ₗ[F] (Fin m → F)) :
  ∃ s : Set (Fin m → F),
    s ⊆ LinearMap.range T ∧
    LinearIndependent F (Subtype.val : s → (Fin m → F)) ∧
    Submodule.span F s = LinearMap.range T ∧
    ∃ S : Set (Fin m → F),
      s ⊆ S ∧
      LinearIndependent F (Subtype.val : S → (Fin m → F)) ∧
      Submodule.span F S = ⊤ := by
  sorry





theorem theorem_419290_problem (m n : ℕ) (W : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
  Real.sqrt (∑ i, (∑ j, W i j * x j)^2) ≤
  Real.sqrt (∑ i, ∑ j, (W i j)^2) * Real.sqrt (∑ j, (x j)^2) := by
  sorry

theorem theorem_419045_problem (a : Fin 3 → Fin 3 → ℤ)
  (h_range : ∀ i j, a i j = 1 ∨ a i j = -1)
  (h1 : a 0 0 * a 1 1 * a 2 2 = 1)
  (h2 : a 0 1 * a 1 2 * a 2 0 = 1)
  (h3 : a 0 2 * a 1 0 * a 2 1 = 1)
  (h4 : a 0 1 * a 1 0 * a 2 2 = -1)
  (h5 : a 1 2 * a 2 1 * a 0 0 = -1)
  (h6 : a 0 2 * a 2 0 * a 1 1 = -1) :
  False := by
  sorry



theorem theorem_418792_problem
  {n p m k : Type*} [Fintype n] [Fintype p] [Fintype m] [Fintype k]
  [DecidableEq k]
  (X : Matrix n p ℝ) -- Original explanatory variables
  (T : Matrix n m ℝ) -- PLS components
  (h_PLS : ∃ W : Matrix p m ℝ, T = X * W) -- PLS construction assumption: T is a linear projection of X
  (Beta : Matrix m k ℝ) -- GLR coefficients on T
  (Beta_0 : k → ℝ) -- Intercepts
  :
  -- Conclusion: The model is interpretable in terms of X.
  -- i.e., There exist coefficients Gamma for X such that the Softmax probabilities match.
  ∃ (Gamma : Matrix p k ℝ) (Gamma_0 : k → ℝ),
    let logits_T (i : n) (c : k) := Beta_0 c + (T * Beta) i c
    let prob_T (i : n) (c : k) := Real.exp (logits_T i c) / ∑ d, Real.exp (logits_T i d)
    let logits_X (i : n) (c : k) := Gamma_0 c + (X * Gamma) i c
    let prob_X (i : n) (c : k) := Real.exp (logits_X i c) / ∑ d, Real.exp (logits_X i d)
    ∀ i c, prob_X i c = prob_T i c := by
  sorry













theorem theorem_419683_problem
  {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]
  (W : Submodule K V)
  (D : Representation K G V) :
  (∀ g : G, Submodule.map (D g) W ≤ W) ↔ (∀ (g : G) (w : W), D g w ∈ W) := by
  sorry













theorem theorem_420058_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  {n : ℕ}
  (m : Basis (Fin n) F V)
  (T : V →ₗ[F] V) :
  LinearMap.toMatrix m m T = Matrix.of (fun i j => m.repr (T (m j)) i) := by
  sorry

theorem theorem_420330_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) :
  ∀ i : Fin m,
    let d := Finset.lcm Finset.univ (fun j => (A i j).den)
    ∀ j : Fin n, ∃ z : ℤ, (d : ℚ) * A i j = z := by
  sorry





theorem theorem_420517_problem
  (K V W : Type*)
  [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  [FiniteDimensional K V] [FiniteDimensional K W]
  (T : V →ₗ[K] W)
  (h_inj : Function.Injective T)
  (h_dim : FiniteDimensional.finrank K V = FiniteDimensional.finrank K W) :
  Function.Surjective T := by
  sorry









theorem theorem_421012_problem (V : Type*) [AddCommGroup V] [Module ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]
  (A : V →ₗ[ℝ] V) :
  ∃ z : ℂ, (Polynomial.map (algebraMap ℝ ℂ) A.charpoly).IsRoot z := by
  sorry

theorem theorem_420670_problem
  (K K' : Type*) [Field K] [Field K'] [Algebra K K']
  (V : Type*) [AddCommGroup V] [Module K V]
  (U : Set V)
  (hU : LinearIndependent K (fun (u : U) => (u : V))) :
  LinearIndependent K' (fun (u : U) => (1 : K') ⊗ₜ[K] (u : V)) := by
  sorry



