import Mathlib
import Mathlib.Tactic

theorem theorem_11784_problem
  {F : Type*} [Field F]
  (f : F → F)
  (h_add : ∀ x y : F, f (x + y) = f x + f y)
  (h_smul : ∀ c x : F, f (c * x) = c * f x) :
  IsLinearMap F f := by
  sorry





theorem theorem_10741_problem :
  ∃ (n : ℕ) (A B C : Matrix (Fin n) (Fin n) ℝ),
    A.PosSemidef ∧ B.PosSemidef ∧ C.PosSemidef ∧
    (A + B - C).PosSemidef ∧
    ¬ ∃ (A₁ B₁ : Matrix (Fin n) (Fin n) ℝ),
      A₁.PosSemidef ∧ B₁.PosSemidef ∧
      (A - A₁).PosSemidef ∧ (B - B₁).PosSemidef ∧
      A₁ + B₁ = C := by
  sorry



theorem theorem_12315_problem
  {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y]
  (H : Set X) (hH : Dense H)
  (f : ℕ → X → Y)
  (h_equi : Equicontinuous f)
  (h_lim_H : ∀ x ∈ H, ∃ y, Filter.Tendsto (fun n ↦ f n x) Filter.atTop (nhds y)) :
  ∀ x : X, ∃ y, Filter.Tendsto (fun n ↦ f n x) Filter.atTop (nhds y) := by
  sorry



theorem theorem_11804_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (A_plus_I : V →L[ℝ] (V →L[ℝ] ℝ))
  (h_def : ∀ f g : V, A_plus_I f g = inner f g) :
  ∀ L : V →L[ℝ] ℝ, ∃! h : V, ∀ g : V, A_plus_I h g = L g := by
  sorry







theorem theorem_12290_problem
  {k : Type*} [Field k]
  {X Y Z : Type*}
  [AddCommGroup X] [Module k X]
  [AddCommGroup Y] [Module k Y]
  [AddCommGroup Z] [Module k Z]
  (T : X →ₗ[k] Z) :
  LinearMap.ker (TensorProduct.map T (LinearMap.id : Y →ₗ[k] Y)) =
  LinearMap.range (TensorProduct.map (LinearMap.ker T).subtype (LinearMap.id : Y →ₗ[k] Y)) := by
  sorry











theorem theorem_11883_problem (V X : Type*)
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : V →L[ℂ] X) (he : Function.Injective e)
  (T : X →L[ℂ] X)
  (hT : ∀ x : X, ∃ v : V, e v = T x)
  (S : V →L[ℂ] V)
  (hS : ∀ v : V, e (S v) = T (e v)) :
  spectralRadius ℂ T = spectralRadius ℂ S := by
  sorry



















theorem theorem_12753_problem
  {L H : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  (V : Submodule ℝ L)
  (hV_closed : IsClosed (V : Set L))
  (i : H →L[ℝ] L)
  (h_dom : ∀ x, ‖i x‖ ≤ ‖x‖)
  (h_subset : ∀ v : V, ∃ h : H, i h = v)
  : ∃ C > 0, ∀ (f : V), ∃ (h : H), i h = f.1 ∧ ‖f.1‖ ≤ C * ‖h‖ := by
  sorry



theorem theorem_11736_problem
  {n : ℕ} (hn : n > 0)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (h_dim : FiniteDimensional.finrank ℝ E = n)
  (A : E →L[ℝ] E)
  (h_symm : IsSelfAdjoint A)
  (vals : Fin n → ℝ)
  (b : Fin n → E)
  (h_sorted : Antitone vals)
  (h_ortho : Orthonormal ℝ b)
  (h_eigen : ∀ i, A (b i) = vals i • b i)
  (x : E) :
  inner x (A x) ≤ vals ⟨0, hn⟩ * ‖x‖^2 := by
  sorry

theorem theorem_11983_problem
  (n d : ℕ)
  (p : Fin (n + 1) → EuclideanSpace ℝ (Fin 2))
  (t : Fin (n + 1) → ℝ)
  (ht : ∀ i, t i = (i : ℝ) / n)
  (β : ℝ → EuclideanSpace ℝ (Fin 2))
  (h_beta_bezier : ∃ c : Fin (d + 1) → EuclideanSpace ℝ (Fin 2),
    ∀ x, β x = ∑ j : Fin (d + 1), (bernsteinPolynomial ℝ d j).eval x • c j)
  (h_beta_optimal : ∀ γ : ℝ → EuclideanSpace ℝ (Fin 2),
    (∃ c : Fin (d + 1) → EuclideanSpace ℝ (Fin 2), ∀ x, γ x = ∑ j : Fin (d + 1), (bernsteinPolynomial ℝ d j).eval x • c j) →
    (1 / ((n : ℝ) + 1)) * ∑ i : Fin (n + 1), ‖β (t i) - p i‖^2 ≤ (1 / ((n : ℝ) + 1)) * ∑ i : Fin (n + 1), ‖γ (t i) - p i‖^2) :
  IsMinOn (fun f ↦ (1 / ((n : ℝ) + 1)) * ∑ i : Fin (n + 1), ‖f (t i) - p i‖^2)
    {γ | ∃ c : Fin (d + 1) → EuclideanSpace ℝ (Fin 2), ∀ x, γ x = ∑ j : Fin (d + 1), (bernsteinPolynomial ℝ d j).eval x • c j}
    β := by
  sorry



theorem theorem_10971_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
  A * Matrix.adjugate A = Matrix.det A • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  sorry

theorem theorem_11628_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X Y Z W : Type*}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace W]
  (f : X → Y) (g : X → Z)
  (B : Y →L[𝕜] Z →L[𝕜] W)
  (x h : X)
  (hf : DifferentiableAt 𝕜 f x)
  (hg : DifferentiableAt 𝕜 g x)
  (ψ : X → W)
  (hψ : ψ = fun x => B (f x) (g x)) :
  fderiv 𝕜 ψ x h = B (fderiv 𝕜 f x h) (g x) + B (f x) (fderiv 𝕜 g x h) := by
  sorry



theorem theorem_11212_problem
  (K : Type*) [Field K]
  (V W : Type*) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (m n : ℕ)
  (b1 : Basis (Fin m) K V)
  (b2 : Basis (Fin n) K W)
  (phi : V →ₗ[K] W)
  (A : Matrix (Fin n) (Fin m) K)
  (hA : A = LinearMap.toMatrix b1 b2 phi)
  (c1 : Basis (Fin m) K V)
  (c2 : Basis (Fin n) K W)
  (P : Matrix (Fin m) (Fin m) K)
  (hP : P = b1.toMatrix c1)
  (Q : Matrix (Fin n) (Fin n) K)
  (hQ : Q = b2.toMatrix c2) :
  LinearMap.toMatrix c1 c2 phi = Q⁻¹ * A * P := by
  sorry









theorem theorem_12184_problem
  {K G V : Type*}
  [Field K] [Group G] [Fintype G]
  [AddCommGroup V] [Module K V]
  (R₁ : G →* Module.End K V)
  (R₂ : G →* Module.End K V)
  (l : Module.End K V) :
  let L := ∑ x : G, R₁ x * l * R₂ (x⁻¹)
  ∀ g : G, R₁ g * L * R₂ (g⁻¹) = L := by
  sorry









theorem theorem_12504_problem
  (f_XY : ℝ → ℝ → ℝ)
  (u v : ℝ)
  (hu : u ≠ 0) :
  let g : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1, p.2 / p.1)
  let J := fderiv ℝ g (u, v)
  let f_X_XY := f_XY (g (u, v)).1 (g (u, v)).2 * abs (LinearMap.det J.toLinearMap)
  f_X_XY = f_XY u (v / u) * (1 / abs u) := by
  sorry

theorem theorem_12825_problem
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ) (hf : Differentiable ℝ f)
  (p q : E)
  (φ : ℝ → E) (hφ : φ = fun t ↦ p + t • (q - p))
  (g : ℝ → ℝ) (hg : g = f ∘ φ)
  (t : ℝ) :
  HasDerivAt g ((fderiv ℝ f (φ t)) (q - p)) t := by
  sorry





theorem theorem_13341_problem {X : Type*} [AddCommGroup X] [Module ℝ X]
  (f g : X →ₗ[ℝ] ℝ)
  (h : LinearMap.ker f = LinearMap.ker g) :
  ∃ α : ℝ, ∀ x : X, g x = α * f x := by
  sorry







theorem theorem_13761_problem
  (K : Set ℝ) (hK : IsCompact K)
  (f_n : ℕ → K → ℝ) (f : K → ℝ)
  (h_cont_fn : ∀ n, Continuous (f_n n))
  (h_cont_f : Continuous f)
  (h_pointwise : ∀ x, Filter.Tendsto (fun n ↦ f_n n x) Filter.atTop (nhds (f x)))
  (h_mono : (∀ x n, f_n n x ≤ f_n (n + 1) x) ∨ (∀ x n, f_n (n + 1) x ≤ f_n n x)) :
  TendstoUniformly f_n f Filter.atTop := by
  sorry

theorem theorem_13623_problem
  {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [StrictConvexSpace ℝ Y]
  (h_dim : 1 < Module.rank ℝ X)
  (f : X → Y)
  (h_f0 : f 0 = 0)
  (h_rat_iso : ∀ x y : X, (∃ q : ℚ, ‖x - y‖ = q) → ‖f x - f y‖ = ‖x - y‖) :
  ∀ x y : X, ‖f x - f y‖ = ‖x - y‖ := by
  sorry

theorem theorem_13575_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (f : V →L[ℝ] W)
  (x : V) (hx : x ≠ 0) :
  ‖f x‖ ≤ ‖f‖ * ‖x‖ := by
  sorry



theorem theorem_13989_problem
  {K : Type*} [Field K]
  {E₀ E₁ V₀ V₁ : Type*}
  [AddCommGroup E₀] [Module K E₀]
  [AddCommGroup E₁] [Module K E₁]
  [AddCommGroup V₀] [Module K V₀]
  [AddCommGroup V₁] [Module K V₁]
  (f : E₀ →ₗ[K] E₁) (g : V₁ →ₗ[K] V₀) :
  ∃ L : (E₁ →ₗ[K] V₁) →ₗ[K] (E₀ →ₗ[K] V₀), ∀ h : E₁ →ₗ[K] V₁, L h = g.comp (h.comp f) := by
  sorry

theorem theorem_13354_problem (n : ℕ) (G : Type*) [Group G]
  (phi : G → Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
  Function.Injective phi ↔ ¬ ∃ g1 g2 : G, g1 ≠ g2 ∧ phi g1 = phi g2 := by
  sorry

theorem theorem_14675_problem {𝕜 : Type*} [RCLike 𝕜] {V : Type*}
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] (f g : V) :
  ‖f + g‖ ≤ ‖f‖ + ‖g‖ := by
  sorry





theorem theorem_13264_problem
  {J Θ : Type*} [Fintype J] [Fintype Θ]
  (b : J → Θ → ℝ)
  (x : J → ℝ)
  (y : J → Θ → ℝ)
  (h_pos : ∀ j θ, y j θ ≥ 0)
  (h_constr : ∀ j θ, y j θ ≥ b j θ - x j)
  (h_opt : ∀ y' : J → Θ → ℝ,
    (∀ j θ, y' j θ ≥ 0) →
    (∀ j θ, y' j θ ≥ b j θ - x j) →
    ∑ j, ∑ θ, y j θ ≤ ∑ j, ∑ θ, y' j θ) :
  ∀ j θ, y j θ = max (b j θ - x j) 0 := by
  sorry









theorem theorem_13521_problem (n : Type*) [Fintype n] [DecidableEq n]
  (A B : Matrix n n ℝ) (F : Matrix n n ℝ)
  (hF : F = A * B) :
  let vec : Matrix n n ℝ → Matrix (n × n) Unit ℝ :=
    fun M ij _ ↦ M ij.2 ij.1
  let I : Matrix n n ℝ := 1
  vec F = (B.transpose.kronecker I) * (vec A) := by
  sorry





theorem theorem_13812_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (h_inf : ¬ FiniteDimensional ℂ H)
  (S₀ S₁ : H →L[ℂ] H)
  (h_iso₀ : star S₀ * S₀ = 1)
  (h_iso₁ : star S₁ * S₁ = 1)
  (h_rel : S₀ * star S₀ + S₁ * star S₁ = 1)
  (φ : (H →L[ℂ] H) →⋆ₐ[ℂ] (H →L[ℂ] H)) :
  φ S₀ * star (φ S₀) + φ S₁ * star (φ S₁) = 1 := by
  sorry

theorem theorem_13715_problem (f : ℂ → ℂ)
  (h_entire : Differentiable ℂ f)
  (h_bound : ∀ z : ℂ, Complex.abs (f z) ≤ Real.pi * Real.exp (2 * z.re)) :
  ∃ a : ℂ, ∀ z : ℂ, f z = a * Complex.exp (2 * z) := by
  sorry





















theorem theorem_12989_problem (n d k : ℕ) (hk : k < d)
  (X : Matrix (Fin n) (Fin d) ℝ)
  (X_pca X_isomap : Matrix (Fin n) (Fin k) ℝ)
  (frobenius_norm : Matrix (Fin n) (Fin k) ℝ → ℝ)
  (h_frobenius : ∀ M, frobenius_norm M = Real.sqrt (∑ i, ∑ j, (M i j)^2))
  (NLSTAT : ℝ)
  (h_NLSTAT : NLSTAT = frobenius_norm (X_isomap - X_pca)) :
  NLSTAT = Real.sqrt (∑ i, ∑ j, (X_isomap i j - X_pca i j)^2) := by
  sorry

theorem theorem_14400_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  {W : Type*} [AddCommGroup W] [Module K W]
  {n m : ℕ}
  (D : Basis (Fin n) K V)
  (F : Basis (Fin m) K W)
  (T : V →ₗ[K] W)
  (C : Matrix (Fin m) (Fin n) K)
  (h : ∀ i : Fin n, T (D i) = ∑ j : Fin m, C j i • F j) :
  LinearMap.toMatrix D F T = C := by
  sorry







theorem theorem_14999_problem
  (n : ℕ)
  (K : Type*) [Field K]
  (A B : Matrix (Fin n) (Fin n) K)
  (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
  (hC : C = Matrix.fromBlocks 0 A B 0) :
  ∀ (μ : K), Module.End.HasEigenvalue (Matrix.toLin' C) μ ↔
    Module.End.HasEigenvalue (Matrix.toLin' (A * B)) (μ ^ 2) := by
  sorry





theorem theorem_15605_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
  spectrum ℂ A ⊆ Set.range (Complex.ofReal) := by
  sorry



theorem theorem_15029_problem
  {K : Type*} [Field K]
  {n m p : Type*} [Fintype n] [Fintype m] [Fintype p]
  [DecidableEq n] [DecidableEq m] [DecidableEq p]
  (A : Matrix n m K) (B : Matrix m p K)
  (h : FiniteDimensional.finrank K (LinearMap.range (Matrix.toLin' (A * B))) =
       FiniteDimensional.finrank K (LinearMap.range (Matrix.toLin' A))) :
  LinearMap.range (Matrix.toLin' (A * B)) = LinearMap.range (Matrix.toLin' A) := by
  sorry







theorem theorem_16098_problem
  (n : ℕ) (hn : n > 0)
  (ι : Type*) [Fintype ι]
  (b : ι → EuclideanSpace ℝ (Fin n))
  (hb : ∑ i, ‖b i‖^2 ≠ 0) :
  let s_vals : Set ℝ := {(10 : ℝ) ^ (-132 : ℤ), 1, (10 : ℝ) ^ 345};
  let a (s : ℝ) : EuclideanSpace ℝ (Fin n) :=
    (WithLp.equiv 2 (Fin n → ℝ)).symm (fun j => if j.val = 0 then s else 0);
  (∃ s ∈ s_vals, ∑ i, ‖a s‖^2 * ‖b i‖^2 < ∑ i, ‖b i‖^2) ∧
  (∃ s ∈ s_vals, ∑ i, ‖a s‖^2 * ‖b i‖^2 = ∑ i, ‖b i‖^2) ∧
  (∃ s ∈ s_vals, ∑ i, ‖a s‖^2 * ‖b i‖^2 > ∑ i, ‖b i‖^2) := by
  sorry

theorem theorem_15109_problem (n : ℕ) (a_seq b_seq : Fin (n + 1) → ℝ)
  (s2 t2 a b R : ℝ)
  (h_s2 : s2 = ∑ i : Fin n, |a_seq i.castSucc| ^ 2)
  (h_t2 : t2 = ∑ i : Fin n, |b_seq i.castSucc| ^ 2)
  (h_a : a = |a_seq (Fin.last n)|)
  (h_b : b = |b_seq (Fin.last n)|)
  (h_R : R = s2 * t2 + a^2 * b^2 + 2 * a * b * ∑ i : Fin n, |a_seq i.castSucc| * |b_seq i.castSucc|) :
  R ≤ (s2 + a^2) * (t2 + b^2) := by
  sorry

theorem theorem_16051_problem (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ)
  (h_diff : ContDiff ℝ 2 f)
  (hM : M > 0)
  (h_hess : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ M) :
  ∀ x y, ‖gradient f x - gradient f y‖ ≤ M * ‖x - y‖ := by
  sorry



