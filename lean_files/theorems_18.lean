import Mathlib
import Mathlib.Tactic





theorem theorem_91442_problem (K : Type*) [Field K]
  (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (A : Submodule K (Module.Dual K V))
  (hA : A < ⊤) :
  ∃ v : V, v ≠ 0 ∧ ∀ f ∈ A, f v = 0 := by
  sorry

theorem theorem_91800_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (c : E)
  (r : ℝ)
  (a : E)
  (d : ℝ)
  (hr : 0 ≤ r) :
  (∀ x ∈ Metric.closedBall c r, inner a x ≤ d) ↔ inner a c ≤ d - r * ‖a‖ := by
  sorry





theorem theorem_92044_problem
  (n : ℕ)
  (x y : ℝ → (Fin n → ℝ))
  (h_smooth_x : ContDiff ℝ ⊤ x)
  (h_smooth_y : ContDiff ℝ ⊤ y)
  -- The "new frame" is modeled as a time-dependent transformation T
  (T : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
  -- The transformation is a translation (preserving the axes)
  (h_trans : ∀ t, ∃ d, ∀ v, T t v = v + d)
  -- The object is at the origin in the new frame
  (h_origin : ∀ t, T t (x t) = 0) :
  -- The coordinates of the camera in the new frame
  ∀ t, T t (y t) = y t - x t := by
  sorry





theorem theorem_92260_problem
  (π : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ)
  (i : ℝ × ℝ → ℝ × ℝ × ℝ × ℝ)
  (x₁ x₂ y₁ y₂ : ℝ × ℝ × ℝ × ℝ → ℝ)
  (hπ : π = fun x ↦ (x.2.2.1, x.2.2.2))
  (hi : i = fun y ↦ (0, 0, y.1, y.2))
  (hx₁ : x₁ = fun x ↦ x.1)
  (hx₂ : x₂ = fun x ↦ x.2.1)
  (hy₁ : y₁ = fun x ↦ x.2.2.1)
  (hy₂ : y₂ = fun x ↦ x.2.2.2) :
  (∀ x, fderiv ℝ (x₁ ∘ i ∘ π) x = 0) ∧
  (∀ x, fderiv ℝ (x₂ ∘ i ∘ π) x = 0) ∧
  (∀ x, fderiv ℝ (y₁ ∘ i ∘ π) x = fderiv ℝ y₁ x) ∧
  (∀ x, fderiv ℝ (y₂ ∘ i ∘ π) x = fderiv ℝ y₂ x) := by
  sorry

theorem theorem_92613_problem
  (B : Type*)
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  (T : B →L[ℝ] B)
  (hT : IsCompactOperator T)
  (h_ball : IsSeqCompact (Metric.closedBall (0 : B) 1)) :
  FiniteDimensional ℝ B := by
  sorry

theorem theorem_92529_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (hV : FiniteDimensional.finrank K V = 3)
  (B : V →ₗ[K] V →ₗ[K] K)
  (hB_sym : ∀ u v, B u v = B v u)
  (hB_nondeg : LinearMap.Nondegenerate B)
  (P : Submodule K V) (hP_rank : FiniteDimensional.finrank K P = 1)
  (hP_not_on_C : ∀ v ∈ P, v ≠ 0 → B v v ≠ 0)
  (l₁ l₂ : Submodule K V)
  (hl₁_rank : FiniteDimensional.finrank K l₁ = 2)
  (hl₂_rank : FiniteDimensional.finrank K l₂ = 2)
  (hl_diff : l₁ ≠ l₂)
  (hP_l₁ : P ≤ l₁)
  (hP_l₂ : P ≤ l₂)
  (Q₁ Q₂ : Submodule K V)
  (hQ₁ : ∀ x, x ∈ Q₁ ↔ ∀ y ∈ l₁, B x y = 0)
  (hQ₂ : ∀ x, x ∈ Q₂ ↔ ∀ y ∈ l₂, B x y = 0) :
  (∀ x, x ∈ Q₁ ⊔ Q₂ ↔ ∀ y ∈ P, B x y = 0) := by
  sorry

theorem theorem_92778_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (hchar : ringChar F > 2)
  (q : QuadraticForm F V)
  (f : V → V → F)
  (hf : ∀ u v, f u v = (2 : F)⁻¹ * (q (u + v) - q u - q v))
  (u v : V) :
  q (u + v) = q u + q v + f u v + f v u := by
  sorry

theorem theorem_92658_problem (n : ℕ) (hn : n ≥ 2) :
  ∃ (A B : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ),
    A.charpoly = B.charpoly ∧ (F A).charpoly ≠ (F B).charpoly := by
  sorry











theorem theorem_92442_problem (n : ℕ) (f : (Fin n → ℝ) → ℝ)
  (h_lin : IsLinearMap ℝ f)
  (h_bound : ∃ B : ℝ, ∀ a : Fin n → ℝ, f a > B) :
  f = 0 := by
  sorry

theorem theorem_92780_problem
  (m p : ℕ)
  (f : (Fin m → ℝ) → (Fin p → ℝ))
  (g : ℝ → (Fin m → ℝ))
  (x : ℝ)
  (hf : Differentiable ℝ f)
  (hg : Differentiable ℝ g) :
  fderiv ℝ (f ∘ g) x = (fderiv ℝ f (g x)).comp (fderiv ℝ g x) := by
  sorry

theorem theorem_92743_problem (N : ℕ) (hN : N ≥ 2) :
  (∑ k in Finset.Icc 1 (N - 1),
    (Finset.filter (fun p : ℕ × ℕ => p.1 > 0 ∧ p.2 > 0 ∧ p.1 * p.2 < k * (N - k))
      (Finset.product (Finset.range (k * (N - k))) (Finset.range (k * (N - k))))).card : ℤ) =
  ∑ k in Finset.Icc 1 (N - 1),
    ∑ i in Finset.Icc 1 (k * (N - k) - 1), (Int.ceil ((k * (N - k) : ℚ) / i) - 1) := by
  sorry



theorem theorem_93000_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (A B : H →L[𝕜] H) :
  ContinuousLinearMap.adjoint (A * B) = (ContinuousLinearMap.adjoint B) * (ContinuousLinearMap.adjoint A) := by
  sorry

theorem theorem_92988_problem
  (K : Type*) [Field K]
  (A B : Matrix (Fin 2) (Fin 2) K) :
  Matrix.trace (A^2 * B^2) - (Matrix.trace A) * (Matrix.trace (A * B^2)) +
  (Matrix.det A) * ((Matrix.trace B)^2 - 2 * Matrix.det B) = 0 := by
  sorry

theorem theorem_93009_problem (n : ℕ) (a : Fin n → Fin n → ℂ) (x y : Fin n → ℂ) :
  ∑ i, (∑ j, a i j * x j) * y i = ∑ j, (∑ i, a i j * y i) * x j := by
  sorry

theorem theorem_93083_problem
  (A B C a b c w : ℝ)
  (h : A^2 + B^2 ≠ 0) :
  let n_hat : Fin 3 → ℝ := (1 / Real.sqrt (A^2 + B^2 + C^2)) • ![A, B, C]
  let u_hat : Fin 3 → ℝ := (1 / Real.sqrt (A^2 + B^2)) • ![B, -A, 0]
  let v_hat : Fin 3 → ℝ := (1 / (Real.sqrt (A^2 + B^2) * Real.sqrt (A^2 + B^2 + C^2))) • ![-A * C, -B * C, A^2 + B^2]
  let cross_prod (x y : Fin 3 → ℝ) : Fin 3 → ℝ :=
    ![x 1 * y 2 - x 2 * y 1, x 2 * y 0 - x 0 * y 2, x 0 * y 1 - x 1 * y 0]
  Matrix.dotProduct u_hat n_hat = 0 ∧ cross_prod u_hat n_hat = v_hat := by
  sorry



theorem theorem_93098_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
  (hA : A.IsSymm) :
  Matrix.dotProduct x (A.mulVec x) = Matrix.trace (A * Matrix.vecMulVec x x) := by
  sorry



theorem theorem_93372_problem
  (n p : Type*) [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
  (X₁ X₂ : Matrix n p ℝ)
  (β : p → ℝ)
  (H₀ : Prop)
  (hH₀ : H₀ ↔ Matrix.mulVec X₁ β = Matrix.mulVec X₂ β)
  (h_reject : ¬ H₀) :
  Matrix.mulVec X₁ β ≠ Matrix.mulVec X₂ β := by
  sorry



theorem theorem_93704_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (P Q : V ≃ₗ[K] V)
  (T : V →ₗ[K] V)
  (S : V →ₗ[K] V)
  (hS : S = (P : V →ₗ[K] V) ∘ₗ T ∘ₗ (Q : V →ₗ[K] V)) :
  FiniteDimensional.finrank K (LinearMap.range T) = FiniteDimensional.finrank K (LinearMap.range S) := by
  sorry



theorem theorem_93549_problem (x c d : Fin 3 → ℝ) :
  Matrix.dotProduct x (crossProduct c d) = Matrix.dotProduct c (crossProduct d x) := by
  sorry

theorem theorem_93323_problem
  {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (A : E →ₗ[ℝ] F)
  (V : Set E)
  (hV : IsOpen V) :
  IsOpen (LinearMap.rangeRestrict A '' V) := by
  sorry

















theorem theorem_93171_problem (m n r : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (h : Matrix.rank A = r) :
  ∃ (Q : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin m) (Fin n) ℝ),
    A = Q * R ∧
    Q.transpose * Q = 1 ∧
    (∀ (i : Fin m) (j : Fin n), (j : ℕ) < (i : ℕ) → R i j = 0) ∧
    (∀ (i : Fin m) (j : Fin n), r ≤ (i : ℕ) → R i j = 0) := by
  sorry

theorem theorem_93751_problem
  (F : Type*) [Field F]
  (C : Type*) [AddCommGroup C] [Module F C]
  (C₀ : Submodule F C)
  (h_nontriv : Nontrivial (C ⧸ C₀))
  (h_gen : ∃ v : C ⧸ C₀, ∀ x : C ⧸ C₀, ∃ a : F, x = a • v) :
  Module.rank F (C ⧸ C₀) = 1 := by
  sorry

theorem theorem_93903_problem (f : ℝ → ℝ → ℝ) (r φ : ℝ)
  (hr : r > 0)
  (hf : ContDiff ℝ 2 (Function.uncurry f)) :
  let x := r * Real.cosh φ
  let y := r * Real.sinh φ
  let g := fun (r' φ' : ℝ) => f (r' * Real.cosh φ') (r' * Real.sinh φ')
  let d2f_dx2 := deriv (fun x' => deriv (fun x'' => f x'' y) x') x
  let d2f_dy2 := deriv (fun y' => deriv (fun y'' => f x y'') y') y
  let dg_dr := deriv (fun r' => g r' φ) r
  let d2g_dr2 := deriv (fun r' => deriv (fun r'' => g r'' φ) r') r
  let d2g_dphi2 := deriv (fun φ' => deriv (fun φ'' => g r φ'') φ') φ
  d2f_dx2 - d2f_dy2 = d2g_dr2 + (1 / r) * dg_dr - (1 / (r ^ 2)) * d2g_dphi2 := by
  sorry

theorem theorem_93913_problem (m n p : ℕ)
  (f : (Fin m → ℝ) → (Fin p → ℝ))
  (g : (Fin n → ℝ) → (Fin m → ℝ))
  (x : ℝ → (Fin n → ℝ))
  (t : ℝ)
  (hf : Differentiable ℝ f)
  (hg : Differentiable ℝ g)
  (hx : Differentiable ℝ x) :
  deriv (f ∘ g ∘ x) t = (fderiv ℝ f (g (x t))) ((fderiv ℝ g (x t)) (deriv x t)) := by
  sorry

theorem theorem_94189_problem
  (n M : ℕ)
  (c : Fin M → EuclideanSpace ℝ (Fin n))
  (P P_tilde : ℝ)
  (hM : 0 < M)
  (hP : 0 < P)
  (hP_tilde : 0 < P_tilde)
  (h_exp : (∑ i, ‖c i‖^2) / (M : ℝ) ≤ n * P) :
  ((Finset.filter (fun i => (n : ℝ) * P_tilde < ‖c i‖^2) Finset.univ).card : ℝ) ≤ (M : ℝ) * (P / P_tilde) := by
  sorry

theorem theorem_94343_problem (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (d : Matrix (Fin n) (Fin 1) ℝ)
  (z : ℝ)
  (hA : Invertible A)
  (μ : ℝ)
  (hμ : μ = z - (d.transpose * A⁻¹ * d) 0 0)
  (hμ_nz : μ ≠ 0) :
  (Matrix.fromBlocks A d d.transpose !![z])⁻¹ =
    Matrix.fromBlocks
      (A⁻¹ + (1 / μ) • (A⁻¹ * d * d.transpose * A⁻¹))
      (-(1 / μ) • (A⁻¹ * d))
      (-(1 / μ) • (d.transpose * A⁻¹))
      !![1 / μ] := by
  sorry





theorem theorem_94456_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) (c : ℂ)
  (hk : k ≥ 1)
  (h_eig : Module.End.HasEigenvalue (Matrix.toLin' (A ^ k)) c) :
  ∃ b : ℂ, b ^ k = c ∧ Module.End.HasEigenvalue (Matrix.toLin' A) b := by
  sorry

theorem theorem_94044_problem
  (n : ℕ)
  (Q : Matrix (Fin n) (Fin n) ℝ)
  (h_nonpos : ∀ i j, Q i j ≤ 0)
  (h_orth : Q.transpose * Q = 1) :
  ∃ σ : Equiv.Perm (Fin n), Q = - (Matrix.of (fun i j ↦ if i = σ j then (1 : ℝ) else 0)) := by
  sorry

theorem theorem_92952_problem
  (n : ℕ)
  (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
  (Y_star : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
  (hB_symm : B.IsSymm)
  (h_relaxed_feas : Y_star.PosSemidef ∧ ∀ (i : Fin n), Y_star i.castSucc i.castSucc = 1)
  (h_relaxed_opt : ∀ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
    (Y.PosSemidef ∧ ∀ (i : Fin n), Y i.castSucc i.castSucc = 1) →
    (B * Y_star).trace ≤ (B * Y).trace)
  (h_structure : ∃ x : Fin n → ℝ, (∀ i, x i = 1 ∨ x i = -1) ∧
    Y_star = Matrix.vecMulVec (Fin.snoc x 1) (Fin.snoc x 1)) :
  ∀ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
    (∃ x : Fin n → ℝ, (∀ i, x i = 1 ∨ x i = -1) ∧
      Y = Matrix.vecMulVec (Fin.snoc x 1) (Fin.snoc x 1)) →
    (B * Y_star).trace ≤ (B * Y).trace := by
  sorry

theorem theorem_94669_problem
  (n : ℕ)
  (l : Fin n → ℕ)
  (hl : ∀ i, 1 ≤ l i)
  (x : Fin n → ℂ)
  (N : ℕ)
  (hN : N = ∑ i, l i)
  (δ : ℝ)
  (hδ : 0 < δ)
  (h_sep : ∀ i j, i ≠ j → δ ≤ Complex.abs (x i - x j))
  (h_bound : ∀ i, Complex.abs (x i) ≤ 1)
  (u : (j : Fin n) → (k : Fin (l j)) → Polynomial ℂ)
  (hu_deg : ∀ j k, (u j k).degree < N)
  (hu_interp : ∀ j k, ∀ i : Fin n, ∀ q : Fin (l i),
    (derivative^[q] (u j k)).eval (x i) = if i = j ∧ (q : ℕ) = (k : ℕ) then 1 else 0) :
  ∀ j k, ∑ m in Finset.range N, Complex.abs ((u j k).coeff m) ≤
    (2 / δ) ^ N * (2 / Nat.factorial k) * ((1 : ℝ) / 2 + N / δ) ^ (l j - 1 - (k : ℕ)) := by
  sorry





theorem theorem_94653_problem
  {R : Type*} [CommRing R]
  (r s t r' s' t' : R)
  (A : Matrix (Fin 3) (Fin 3) R)
  (hA : IsUnit A.det)
  (h_trans : ![r', s', t'] = Matrix.vecMul ![r, s, t] A) :
  Ideal.span ({r, s, t} : Set R) = Ideal.span ({r', s', t'} : Set R) := by
  sorry



theorem theorem_94530_problem (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (u x : EuclideanSpace ℝ (Fin n)) (h : DifferentiableAt ℝ f u) :
  fderiv ℝ f u x = inner (gradient f u) x := by
  sorry







theorem theorem_95133_problem {n : ℕ} (K : Matrix (Fin n) (Fin n) ℤ)
  (h_symm : K.IsSymm) :
  AddSubgroup.index (Matrix.toLin' K).range.toAddSubgroup = Int.natAbs K.det := by
  sorry



theorem theorem_94924_problem
  (n : ℕ)
  (F : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
  (x : ℝ → (Fin n → ℝ))
  (t : ℝ)
  (hF : Differentiable ℝ (Function.uncurry F))
  (hx : Differentiable ℝ x)
  (h2x : DifferentiableAt ℝ (deriv x) t)
  (h_ode : ∀ t, deriv x t = F t (x t)) :
  deriv (deriv x) t = 
    deriv (fun τ => F τ (x t)) t + 
    (fderiv ℝ (fun y => F t y) (x t)) (F t (x t)) := by
  sorry



theorem theorem_94247_problem (x y t : ℝ)
  (Z : Matrix (Fin 2) (Fin 2) ℝ)
  (hZ : Z = (-x) • !![1, 0; 0, -1] - y • !![0, 1; 1, 0] - t • !![0, -1; 1, 0]) :
  (1 : Matrix (Fin 2) (Fin 2) ℝ) + Z = !![1 - x, -y + t; -y - t, 1 + x] := by
  sorry





theorem theorem_95478_problem (f : ℝ → ℝ)
  (h_cont : ContinuousOn f (Set.Icc 0 1)) :
  ∃ c ∈ Set.Icc 0 1, ∫ t in (0 : ℝ)..(1 : ℝ), f t = f c := by
  sorry





theorem theorem_95485_problem
  (k : ℕ)
  (V : Type*) [AddCommGroup V] [Module ℝ V]
  (v : Basis (Fin k) ℝ V) :
  ∃ Φ : (Fin k → ℝ) → V,
    (∀ a, Φ a = ∑ i, a i • v i) ∧
    IsLinearMap ℝ Φ ∧
    Function.Bijective Φ := by
  sorry





















theorem theorem_96311_problem (a b : ℝ) (h_ab : a < b)
  (l : ℕ) (α : ℕ → ℝ)
  (h_zero : ∀ x ∈ Set.Icc a b, ∑ k in Finset.range (l + 1), α k * x ^ k = 0) :
  ∀ k ∈ Finset.range (l + 1), α k = 0 := by
  sorry





theorem theorem_96113_problem (n : ℕ) :
  let x := MvPolynomial.X (σ := Fin n) (R := ℤ)
  let Δ := ∏ i : Fin n, ∏ j in Finset.filter (fun j => i < j) Finset.univ, (x i - x j)
  let A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℤ) := fun i j =>
    if i.val < n - 1 then (x j) ^ (n - i.val) else 1
  ∃ P : MvPolynomial (Fin n) ℤ, A.det = Δ * P := by
  sorry

theorem theorem_95987_problem
  (m : ℕ)
  (n : ℕ)
  (Q P : Matrix (Fin m) (Fin m) ℂ)
  (vals : Fin m → ℂ)
  (hn : n > 0)
  (hP : IsUnit P)
  (hQ : Q = P * Matrix.diagonal vals * P⁻¹) :
  (1 + (n : ℂ)⁻¹ • Q) ^ n = P * Matrix.diagonal (fun i => (1 + vals i / (n : ℂ)) ^ n) * P⁻¹ := by
  sorry



theorem theorem_95791_problem {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [FiniteDimensional F V] [FiniteDimensional F W]
  (T : V →ₗ[F] W) :
  ∃ (K : Basis (Fin (FiniteDimensional.finrank F V)) F V)
    (L : Basis (Fin (FiniteDimensional.finrank F W)) F W),
    LinearMap.toMatrix K L T = Matrix.of (fun i j =>
      if i.val = j.val ∧ j.val < FiniteDimensional.finrank F (LinearMap.range T) then 1 else 0) := by
  sorry





theorem theorem_96323_problem
  {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (e : Basis (Fin n) K V)
  (f : Basis (Fin n) K (Module.Dual K V))
  (hf : f = e.dualBasis)
  (z : Basis (Fin n) K V)
  (t : Basis (Fin n) K (Module.Dual K V))
  (ht : t = z.dualBasis)
  (C : Matrix (Fin n) (Fin n) K)
  (hC : C = e.toMatrix z)
  (D : Matrix (Fin n) (Fin n) K)
  (hD : D = f.toMatrix t) :
  D = C⁻¹.transpose := by
  sorry





theorem theorem_96825_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (h : ∀ (x : ℝ) (v : Fin n → ℝ), Matrix.mulVec A v = x • v → v = 0) :
  Matrix.det A > 0 := by
  sorry

theorem theorem_96568_problem
  (n : ℕ)
  (V : Type*) [AddCommGroup V] [Module ℝ V]
  (E F : Basis (Fin n) ℝ V)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (h_basis_trans : ∀ i, F i = ∑ j, A j i • E j)
  (v : V)
  (a b : Fin n → ℝ)
  (h_v_E : v = ∑ j, a j • E j)
  (h_v_F : v = ∑ i, b i • F i) :
  ∀ j, a j = ∑ i, b i * A j i := by
  sorry



