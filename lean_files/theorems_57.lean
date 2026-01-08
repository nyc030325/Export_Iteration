import Mathlib
import Mathlib.Tactic

theorem theorem_305345_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (L : Module.End K V)
  (h1 : IsNilpotent L)
  (h2 : ∃ P : V ≃ₗ[K] V, P.symm.comp (L.comp (P : V →ₗ[K] V)) = 0) :
  L = 0 := by
  sorry











theorem theorem_305574_problem
  (n : ℕ)
  (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W]
  (X : Matrix (Fin n) (Fin n) W) :
  (⨆ (x_star : NormedSpace.Dual ℝ W),
    ⨆ (α : Fin n → ℝ) (hα : ∑ i, (α i)^2 = 1) (β : Fin n → ℝ) (hβ : ∑ j, (β j)^2 = 1),
      ∑ i, ∑ j, α i * β j * x_star (X i j)) =
  (⨆ (x_star : NormedSpace.Dual ℝ W),
    ‖(LinearMap.toContinuousLinearMap
      (Matrix.toLin' (Matrix.of (fun i j ↦ x_star (X i j)))) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖) := by
  sorry





theorem theorem_305622_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (E : Set V)
  (h_closed : IsClosed E)
  (h_convex : Convex ℝ E)
  (h_nonempty : E.Nonempty) :
  ∃! y₀ ∈ E, ‖y₀‖ = sInf (norm '' E) := by
  sorry

theorem theorem_305149_problem
  (a b c d : ℝ)
  (M_q : Matrix (Fin 4) (Fin 4) ℝ)
  (hMq : M_q = !![a,  b,  c,  d;
                  -b, a, -d,  c;
                  -c, d,  a, -b;
                  -d, -c, b,  a])
  (V : Matrix (Fin 4) (Fin 3) ℝ) :
  (M_q * V) 0 = fun j => Matrix.dotProduct ![a, b, c, d] (fun i => V i j) := by
  sorry

theorem theorem_305751_problem (n : ℕ)
  (T : EuclideanSpace ℝ (Fin n) → ℝ)
  (hT : ∀ x, T x = ‖x‖) :
  (∀ x, 1 < ‖x‖ → 1 < T x) ∧ (∀ x, ‖x‖ < 1 → T x < 1) := by
  sorry









theorem theorem_306574_problem
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (h : ∀ (i j : Fin m), Matrix.dotProduct (A i) (A j) = if i = j then 1 else 0) :
  (A.transpose * A) ^ 2 = A.transpose * A := by
  sorry



theorem theorem_306559_problem
  (h : ℝ × ℝ → ℝ)
  (x y : ℝ → ℝ)
  (h_diff : Differentiable ℝ h)
  (x_diff : Differentiable ℝ x)
  (y_diff : Differentiable ℝ y)
  (t : ℝ) :
  deriv (fun t => h (x t, y t)) t =
    (fderiv ℝ h (x t, y t)) (1, 0) * deriv x t +
    (fderiv ℝ h (x t, y t)) (0, 1) * deriv y t := by
  sorry







theorem theorem_307257_problem (s : Set ℂ) (t : Set ℂ)
  (h_subset : t ⊆ s)
  (h_indep : LinearIndependent ℝ (Subtype.val : t → ℂ)) :
  t.Finite ∧ t.ncard ≤ 2 := by
  sorry

theorem theorem_306742_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA : A.PosSemidef) (hB : B.PosSemidef) :
  Matrix.PosSemidef (fun i j => A i j * B i j) := by
  sorry





theorem theorem_306996_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
  (h_symm : A.IsSymm)
  (h_psd : A.PosSemidef)
  (hc : c > 0) :
  (c • A).PosSemidef := by
  sorry







theorem theorem_307327_problem (n : ℕ) (hn : n ≥ 1) :
  let B₀ : Set (Fin n → ℝ) := {x | {i | x i ≠ 0}.ncard ≤ 1}
  let B_infty : Set (Fin n → ℝ) := {x | ∀ i, |x i| ≤ 1}
  let B₁ : Set (Fin n → ℝ) := {x | ∑ i, |x i| ≤ 1}
  convexHull ℝ (B₀ ∩ B_infty) = B₁ := by
  sorry



theorem theorem_307839_problem
  {K U V W : Type*} [Field K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  (A : U →ₗ[K] V)
  (B : V →ₗ[K] W)
  (h_sub : LinearMap.range A ≤ LinearMap.ker B)
  (h_dim : FiniteDimensional.finrank K (LinearMap.range A) = FiniteDimensional.finrank K (LinearMap.ker B)) :
  LinearMap.range A = LinearMap.ker B := by
  sorry



theorem theorem_307668_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (x y z : H) :
  (1 / 2 : ℝ) * ‖x - z‖ ^ 2 = (1 / 2 : ℝ) * ‖x - y‖ ^ 2 + (1 / 2 : ℝ) * ‖y - z‖ ^ 2 + inner (x - y) (y - z) := by
  sorry



theorem theorem_307533_problem
  (n : ℕ)
  (A Q : Matrix (Fin n) (Fin n) ℝ)
  (hA_symm : A.IsSymm)
  (hA_pos : A.PosDef)
  (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
  (Q.transpose * A * Q).PosDef := by
  sorry

theorem theorem_307164_problem (m n : ℕ) (X : Matrix (Fin n) (Fin m) ℝ) (l u : Fin n → ℝ) :
  Set.Nonempty ({x : Fin n → ℝ | ∀ i, l i ≤ x i ∧ x i ≤ u i} ∩
                {x : Fin n → ℝ | ∃ y : Fin m → ℝ, Matrix.mulVec X y = x}) ↔
  ∃ (y : Fin m → ℝ) (x : Fin n → ℝ), (∀ i, l i ≤ x i ∧ x i ≤ u i) ∧
    Matrix.mulVec X y - x = 0 := by
  sorry



theorem theorem_307927_problem
  (F : Type*) [Field F]
  (ν : ℕ)
  (V : Submodule F (Fin (2 * ν + 1) → F))
  (h_dim : FiniteDimensional.finrank F V ≤ ν) :
  ∃ c : Fin (ν + 1) → F, c ≠ 0 ∧
  ∀ v ∈ V, ∑ i : Fin (ν + 1), c i * v (Fin.castLE (by linarith) i) = 0 := by
  sorry







theorem theorem_307936_problem
  (u : ℝ → ℝ)
  (c₀ : ℝ)
  (a b : ℕ → ℝ)
  (h_rep : ∀ x, u x = c₀ + ∑' k : ℕ, if k = 0 then 0 else a k * Real.cos (k * x) + b k * Real.sin (k * x))
  (h_coeffs : ∀ k, k ≥ 1 → a k = 0 ∧ b k = 0) :
  ∀ x, u x = c₀ := by
  sorry

theorem theorem_307920_problem
  {K : Type*} [Field K]
  {n : Type*} [Fintype n] [DecidableEq n]
  (M : Matrix n n K)
  (hM : IsUnit M)
  (E : Matrix n n K)
  (h_trans : E * M = 1) :
  E * 1 = M⁻¹ := by
  sorry



theorem theorem_308074_problem (n : ℕ) (b : Fin n → ℝ)
  (h_pos : ∀ i, 0 < b i)
  (h_distinct : Function.Injective b) :
  LinearIndependent ℝ (fun i ↦ (fun x ↦ Real.log (1 + b i * x))) := by
  sorry





theorem theorem_307843_problem (M : Matrix (Fin 6) (Fin 6) ℤ) 
  (h1 : M = M_def) 
  (h2 : M = L_def * U_def) : 
  M.det = 1 := by
  sorry

theorem theorem_308291_problem
  {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]
  (T : X →L[K] Y)
  (hT : Function.Surjective T) :
  IsOpenMap T := by
  sorry



theorem theorem_308136_problem (n : ℕ) (M : Matrix (Fin n) (Fin n) ℕ)
  (hM : ∀ i j, M i j = 0 ∨ M i j = 1)
  (P : Matrix (Fin n) (Fin n) ℕ)
  (hP : P = ∑ k in Finset.Icc 1 n, M ^ k)
  (i j : Fin n) :
  P i j > 0 ↔ Relation.TransGen (fun a b ↦ M a b = 1) i j := by
  sorry



theorem theorem_308673_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  (B_tilde : Set V)
  (h_indep : LinearIndependent F ((↑) : B_tilde → V))
  (h_maximal : ∀ B : Set V, LinearIndependent F ((↑) : B → V) → B_tilde ⊆ B → B_tilde = B) :
  Submodule.span F B_tilde = ⊤ := by
  sorry





theorem theorem_308939_problem (n : ℕ) (X Z : ℕ → ℝ)
  (hn : n ≠ 0)
  (hZ : ∀ i < n + 1, Z i ≠ 0)
  (hX : ∀ i < n + 1, X i ≠ 0)
  (h_eq : ∀ i < n + 1, (Z i) ^ (-2 : ℝ) + 1 / (n : ℝ) =
    (∑ j in Finset.range (n + 1), (X j) ^ 2) / ((n : ℝ) * (X i) ^ 2)) :
  ∑ i in Finset.range (n + 1), ((Z i) ^ (-2 : ℝ) + 1 / (n : ℝ))⁻¹ = (n : ℝ) := by
  sorry

theorem theorem_308798_problem (n : ℕ) (a x : ℕ → ℝ) :
  (∑ j in Finset.Icc 1 n, a j * x j)^2 ≤
  (∑ j in Finset.Icc 1 n, a j ^ 2) * (∑ j in Finset.Icc 1 n, x j ^ 2) := by
  sorry

















theorem theorem_309150_problem (n : ℕ) (g : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
  (hg : IsUnit g.det) :
  HasDerivAt (fun x => Matrix.det (Function.update g i (Function.update (g i) j x)))
    (g.det * g⁻¹ j i) (g i j) := by
  sorry

theorem theorem_309792_problem
  {K V W : Type*}
  [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  (T : V →ₗ[K] W)
  (U : W →ₗ[K] V)
  (h : LinearMap.comp U T = LinearMap.id) :
  Function.Injective T := by
  sorry



theorem theorem_309787_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (L : V →L[ℝ] V)
  (x : V) :
  fderiv ℝ L x = L := by
  sorry







theorem theorem_310022_problem
  (m n : ℕ)
  (a : ℕ → ℕ → ℝ)
  (w : ℕ → ℝ)
  (a_interp : ℕ → ℝ)
  (h_a_interp : ∀ j, a_interp j = ∑ i in Finset.Icc 1 m, w i * a i j)
  (a_bar : ℝ)
  (h_a_bar : a_bar = (1 / n : ℝ) * ∑ j in Finset.Icc 1 n, a_interp j)
  (a_bar_i : ℕ → ℝ)
  (h_a_bar_i : ∀ i, a_bar_i i = (1 / n : ℝ) * ∑ j in Finset.Icc 1 n, a i j) :
  a_bar = ∑ i in Finset.Icc 1 m, w i * a_bar_i i := by
  sorry

theorem theorem_309775_problem
  {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M]
  (n : ℕ)
  (m : Fin n → M)
  (h_gen : Submodule.span R (Set.range m) = ⊤)
  (φ : Module.End R M)
  (A : Matrix (Fin n) (Fin n) R)
  (hA : ∀ i, φ (m i) = ∑ j, A i j • m j) :
  Polynomial.aeval φ (Matrix.charpoly A) = 0 := by
  sorry







theorem theorem_310085_problem (a b c d : ℂ)
  (M : Matrix (Fin 2) (Fin 2) ℂ)
  (hM : M = !![a, b; c, d])
  (h_det : M.det = 1)
  (h_inv : M⁻¹ = !![star a, star c; star b, star d]) :
  M ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  sorry

theorem theorem_309752_problem
  (k : Type*) [Field k]
  (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (U W : Submodule k V)
  (h : IsCompl U W)
  (T : V →ₗ[k] V) :
  let T_UU := (U.linearProjOfIsCompl W h) ∘ₗ T ∘ₗ U.subtype
  let T_WW := (W.linearProjOfIsCompl U h.symm) ∘ₗ T ∘ₗ W.subtype
  LinearMap.trace k V T = LinearMap.trace k U T_UU + LinearMap.trace k W T_WW := by
  sorry

theorem theorem_309892_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (K : Set H) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
  (F G : H)
  (u : H) (hu_in : u ∈ K) (hu_sol : ∀ v ∈ K, inner F (v - u) ≥ (0 : ℝ))
  (utilde : H) (hut_in : utilde ∈ K) (hut_sol : ∀ v ∈ K, inner G (v - utilde) ≥ (0 : ℝ)) :
  ∀ ε > 0, ∃ δ > 0, ‖F - G‖ < δ → ‖utilde - u‖ < ε := by
  sorry



theorem theorem_310348_problem (n : ℕ) {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R) :
  A.det = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • ∏ i : Fin n, A i (σ i) := by
  sorry

theorem theorem_310249_problem 
  (A B C X : ℝ × ℝ) 
  (k : ℝ)
  (h_distinct : A ≠ C ∧ A ≠ X ∧ C ≠ X)
  (h_angle : (B.1 - A.1) * (C.1 - A.1) + (B.2 - A.2) * (C.2 - A.2) = 0)
  (B' C' : ℝ × ℝ)
  (h_B' : B'.1 = A.1 + ((B.1 - A.1) * Real.cos k + (B.2 - A.2) * Real.sin k) ∧ 
          B'.2 = A.2 + (-(B.1 - A.1) * Real.sin k + (B.2 - A.2) * Real.cos k))
  (h_C' : C'.1 = A.1 + ((C.1 - A.1) * Real.cos k + (C.2 - A.2) * Real.sin k) ∧ 
          C'.2 = A.2 + (-(C.1 - A.1) * Real.sin k + (C.2 - A.2) * Real.cos k))
  (h_col : Collinear ℝ {B', C', X})
  (h_denom1 : B'.1 - X.1 ≠ 0)
  (h_denom2 : C'.1 - X.1 ≠ 0) :
  (B'.2 - X.2) / (B'.1 - X.1) = (C'.2 - X.2) / (C'.1 - X.1) := by
  sorry



theorem theorem_309908_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : E → ℝ)
  (h_c2 : ContDiff ℝ 2 f)
  (h_f0 : f 0 = 0)
  (h_df0 : fderiv ℝ f 0 = 0)
  (h_hom : ∀ (t : ℝ) (x : E), f (t • x) = t ^ 2 * f x) :
  ∀ x : E, f x = (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 f 0 ![x, x] := by
  sorry

theorem theorem_310196_problem
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (W V : Matrix m n ℝ)
  [Invertible (W.transpose * V)] :
  let Q := W * W.transpose + (1 : Matrix m m ℝ) - V * (V.transpose * V)⁻¹ * V.transpose
  Matrix.PosDef Q := by
  sorry

theorem theorem_310557_problem
  {A : Type*} [AddCommGroup A] [Module ℝ A]
  (x : Module.Dual ℝ A)
  (hx : x ≠ 0) :
  FiniteDimensional.finrank ℝ (Submodule.span ℝ {x}) = 1 := by
  sorry

theorem theorem_310480_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (f : X → ℝ)
  (h : ∀ x, f x = ‖x‖) :
  Continuous f := by
  sorry

theorem theorem_310197_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (p : ℕ)
  (X : Fin (p + 1) → V)
  (β : Fin (p + 1) → K)
  (Y : V)
  (hY : Y = ∑ i, β i • X i) :
  Submodule.span K (insert Y (Set.range X)) = Submodule.span K (Set.range X) := by
  sorry













theorem theorem_310321_problem
  {V : Type*} [NormedRing V] [NormedAlgebra ℝ V] [CompleteSpace V]
  (T : Units V)
  (g : ℝ → V)
  (a : ℝ)
  (h_diff : DifferentiableAt ℝ g a)
  (h_cond : deriv g a = T) :
  ↑(T⁻¹) * deriv g a = 1 := by
  sorry





