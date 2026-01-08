import Mathlib
import Mathlib.Tactic



theorem theorem_152288_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
  (hA : A.IsHermitian) (hB : B.IsHermitian) :
  spectrum ℂ (Matrix.fromBlocks A B B A) =
  spectrum ℂ (A + B) ∪ spectrum ℂ (A - B) := by
  sorry







theorem theorem_151667_problem (n : ℕ) (c : Fin n → ℂ)
  (h : ∑ j, c j = 0) :
  ∑ j, ∑ k, c j * star (c k) = 0 := by
  sorry









theorem theorem_152500_problem
  (K : Type*) [Field K] (hK : ringChar K ≠ 2)
  (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (q : QuadraticForm K V)
  (b : V →ₗ[K] V →ₗ[K] K)
  (h_b : b = q.polarBilin)
  (h_nondeg : b.Nondegenerate)
  (u : V ≃ₗ[K] V)
  (h_u : ∀ x y, b (u x) (u y) = b x y) :
  (LinearMap.det (u : V →ₗ[K] V)) ^ 2 = 1 := by
  sorry















theorem theorem_152730_problem
  (K : Type*) [Field K]
  (V U W : Type*)
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  (T1 : V →ₗ[K] U) (T2 : U →ₗ[K] W)
  (h1 : Function.Injective T1)
  (h2 : Function.Injective T2) :
  Function.Injective (T2.comp T1) := by
  sorry

theorem theorem_152870_problem (m n : ℕ)
  (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin m) (Fin n) ℝ)
  (hA : A.PosSemidef) (hB : B.PosSemidef) :
  ∃! Y : Matrix (Fin m) (Fin n) ℝ, A * Y * B + Y = C := by
  sorry



theorem theorem_152740_problem
  {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (A : LinearPMap 𝕜 H H)
  (hA : IsClosed (A.graph : Set (H × H)))
  (S : Submodule 𝕜 (H × H))
  (hS_sub : S ≤ A.graph)
  (hS_closed : IsClosed (S : Set (H × H)))
  (hS_dense : Dense ((S.map (LinearMap.fst 𝕜 H H)) : Set H)) :
  ∃ B : LinearPMap 𝕜 H H, IsClosed (B.graph : Set (H × H)) ∧ B.graph = S := by
  sorry







theorem theorem_153352_problem (n : ℕ) (h_n : n ≥ 2)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (v : Fin n → ℝ)
  (hA : A = fun i j => 
    if i.val = 0 ∧ j.val = 1 then 2
    else if i.val = 1 ∧ j.val = 0 then 1
    else if i = j ∧ 2 ≤ i.val then 1
    else 0)
  (hv : v = fun i => 
    if i.val = 0 then Real.sqrt 2
    else if i.val = 1 then 1
    else 0) :
  Matrix.mulVec A v = Real.sqrt 2 • v := by
  sorry



theorem theorem_153632_problem (e_i h_ii SSE : ℝ)
  (h_cond : SSE * (1 - h_ii) > e_i ^ 2) :
  e_i / Real.sqrt (SSE * (1 - h_ii) - e_i ^ 2) =
  Real.sign e_i * Real.sqrt (e_i ^ 2 / (SSE * (1 - h_ii) - e_i ^ 2)) := by
  sorry

theorem theorem_153344_problem (a b : ℝ)
  (X : Set (ℝ → ℝ)) (hX : X = {f | ContDiff ℝ ⊤ f ∧ HasCompactSupport f})
  (A : Set (ℝ → ℝ)) (hA : A = {g ∈ X | ∫ x in a..b, g x = 0}) :
  {f ∈ X | ∀ g ∈ A, ∫ x, f x * g x = 0} = {0} := by
  sorry

theorem theorem_153164_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousSMul ℝ V]
  (C : Set V)
  (hC_conv : Convex ℝ C)
  (hC_open : IsOpen C)
  (hC_zero : 0 ∈ C) :
  {x : V | gauge C x < 1} = C := by
  sorry











theorem theorem_154131_problem
  (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (hf : Continuous f)
  (φ : ℝ → ℝ)
  (hφ : ∀ r, φ r = sSup (f '' Metric.sphere 0 r)) :
  ContinuousOn φ (Set.Ici 0) := by
  sorry

theorem theorem_154287_problem (A : Matrix (Fin 3) (Fin 3) ℝ) :
  A ^ 2 ≠ -1 := by
  sorry



theorem theorem_154030_problem 
  (G : Type*) [Group G]
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (ρ ρ' : Representation ℂ G V)
  (h_equiv : ∃ (T : V ≃ₗᵢ[ℂ] V), ∀ (g : G), T.toLinearMap * (ρ g) = (ρ' g) * T.toLinearMap) :
  ∃ (P : V ≃ₗᵢ[ℂ] V), ∀ (g : G), ρ' g = P.toLinearMap * (ρ g) * P.symm.toLinearMap := by
  sorry

theorem theorem_153892_problem
  (n : ℕ)
  (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
  (h_symm : M.IsSymm)
  (h_diag : ∀ i, M i i = 1)
  (h_off : ∀ i j, i ≠ j → M i j ≤ 0)
  (h_det : M.det < 0)
  (h_minors : ∀ i, (M.submatrix (Fin.succAbove i) (Fin.succAbove i)).det > 0)
  (v : Fin (n + 1) → ℤ)
  (hv_nonneg : ∀ i, 0 ≤ v i)
  (hv_nonzero : v ≠ 0) :
  let v_real : Fin (n + 1) → ℝ := fun i ↦ v i
  Matrix.dotProduct (Matrix.vecMul v_real M⁻¹) v_real < 0 := by
  sorry

theorem theorem_154281_problem
  (m n k : ℕ)
  (X : Matrix (Fin m) (Fin n) ℝ)
  (y : Fin n → ℝ)
  (hn : 1 < n)
  (X' : Matrix (Fin (m + k)) (Fin n) ℝ := fun i j =>
    if h : i < m then X ⟨i, h⟩ j else y j)
  (E : Matrix (Fin n) (Fin n) ℝ := - X.transpose * X) :
  (X'.transpose * X' + E).det = 0 := by
  sorry

theorem theorem_153938_problem : Set.Infinite solution_set := by
  sorry

theorem theorem_154464_problem
  (gdet : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) ℝ → ℝ)
  (h_det : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ), gdet A = A.det)
  (h_mul : ∀ {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ),
    gdet (A * B) = gdet A * gdet B)
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (h_neq : m ≠ n) :
  gdet A = 0 := by
  sorry



theorem theorem_154462_problem (n : ℕ) (hn : n > 0)
  (N : (Fin n → ℝ) → ℝ)
  (hN_zero : ∀ x, N x = 0 ↔ x = 0)
  (hN_homog : ∀ (c : ℝ) x, N (c • x) = |c| * N x)
  (hN_triangle : ∀ x y, N (x + y) ≤ N x + N y)
  (max_norm : (Fin n → ℝ) → ℝ)
  (h_max_def : ∀ x, (∀ i, |x i| ≤ max_norm x) ∧ (∃ i, |x i| = max_norm x)) :
  ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
    ∀ x, C₁ * max_norm x ≤ N x ∧ N x ≤ C₂ * max_norm x := by
  sorry

theorem theorem_154189_problem
  (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (h_symm : A.IsSymm)
  (hn : n > 0) :
  let vector_rep_norm_sq := fun (M : Matrix (Fin n) (Fin n) ℝ) ↦
    (∑ i, (M i i) ^ 2) + ∑ i, ∑ j, if i < j then (2 * M i j) ^ 2 else 0
  let L := fun c ↦ vector_rep_norm_sq (A - c • (1 : Matrix (Fin n) (Fin n) ℝ))
  ∀ c : ℝ, L (A.trace / (n : ℝ)) ≤ L c := by
  sorry

theorem theorem_154552_problem
  {n : ℕ}
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  (B Bc : Basis (Fin n) F V)
  (Q : Matrix (Fin n) (Fin n) F)
  (hQ : Q = B.toMatrix Bc)
  (P : V) :
  B.equivFun P = (Q⁻¹).mulVec (Bc.equivFun P) := by
  sorry

theorem theorem_154233_problem
  {n : ℕ} (hn : n > 0)
  {F : Type*} [Field F]
  (c : Fin n → F)
  (C : Matrix (Fin n) (Fin n) F)
  (hC : C = Matrix.circulant c)
  (ω : F)
  (hω : ω ^ n = 1) :
  ∀ k : Fin n, Module.End.HasEigenvalue (Matrix.toLin' C) (∑ j : Fin n, c j * ω ^ ((k : ℕ) * (j : ℕ))) := by
  sorry



theorem theorem_154659_problem (n m : ℕ) (v : Fin (n + 1) → (Fin m → ℝ))
  (h : FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range (fun (i : Fin n) ↦ v i.succ - v 0))) = n) :
  FiniteDimensional.finrank ℝ (affineSpan ℝ (Set.range v)).direction = n := by
  sorry

theorem theorem_154746_problem
  {S : Type*}
  (Extension : S → S → Prop)
  (Invertible : S → Prop)
  (h_trans : Transitive Extension)
  (M M' : S)
  (Ms : List S)
  (h1 : ∀ m ∈ Ms, Extension M m)
  (h2 : Extension M' M)
  (h3 : Invertible M') :
  (∀ m ∈ Ms, Extension M' m) ∧ Invertible M' := by
  sorry



theorem theorem_154635_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  {n : ℕ}
  (A : Basis (Fin n) F V)
  (f : V →ₗ[F] V) :
  ∃! M : Matrix (Fin n) (Fin n) F,
    ∀ v : V, A.equivFun (f v) = Matrix.mulVec M (A.equivFun v) := by
  sorry











theorem theorem_155113_problem
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (phi : E × E → F)
  (h_cont : Continuous phi)
  (h_hom : ∀ (x y : E) (r : ℝ), 0 < r → phi (x, r • y) = r • phi (x, y))
  (a b c d : ℝ)
  (h_ab : a ≤ b)
  (h_cd : c ≤ d)
  (gamma : ℝ → E)
  (alpha : ℝ → ℝ)
  (h_gamma_smooth : ContDiffOn ℝ 1 gamma (Set.Icc a b))
  (h_alpha_smooth : ContDiffOn ℝ 1 alpha (Set.Icc c d))
  (h_alpha_incr : ∀ s ∈ Set.Icc c d, 0 < deriv alpha s)
  (h_alpha_c : alpha c = a)
  (h_alpha_d : alpha d = b)
  (h_alpha_maps : Set.MapsTo alpha (Set.Icc c d) (Set.Icc a b)) :
  ∫ t in a..b, phi (gamma t, deriv gamma t) =
    ∫ s in c..d, phi ((gamma ∘ alpha) s, deriv (gamma ∘ alpha) s) := by
  sorry





theorem theorem_155266_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (A : Submodule 𝕜 X)
  (hA : IsClosed (A : Set X))
  (g : X)
  (h : ∀ (F : X →L[𝕜] 𝕜), (∀ a ∈ A, F a = 0) → F g = 0) :
  g ∈ A := by
  sorry

theorem theorem_155381_problem (δ : Fin 3 → Fin 3 → ℝ)
  (hδ : ∀ i j, δ i j = if i = j then 1 else 0) (k n : Fin 3) :
  (∑ j : Fin 3, δ j j) * δ k n - (∑ j : Fin 3, δ j n * δ k j) = 2 * δ k n := by
  sorry

theorem theorem_155654_problem (n : ℕ)
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (f : SchwartzMap E ℂ →L[ℂ] ℂ) -- f is a Tempered Distribution
  (g : SchwartzMap E ℂ)         -- g is a Schwartz function
  (FourierS : SchwartzMap E ℂ → SchwartzMap E ℂ) -- Fourier transform on Schwartz space
  (FourierT : (SchwartzMap E ℂ →L[ℂ] ℂ) → (SchwartzMap E ℂ →L[ℂ] ℂ)) -- Fourier transform on Distributions
  (h_dual : ∀ (u : SchwartzMap E ℂ →L[ℂ] ℂ) (φ : SchwartzMap E ℂ), (FourierT u) φ = u (FourierS φ)) -- Definition by duality
  (h_invol : ∀ (φ : SchwartzMap E ℂ), FourierS (FourierS φ) = φ) -- Normalization property from solution
  :
  f g = (FourierT f) (FourierS g) := by
  sorry

theorem theorem_156307_problem (m n : ℕ)
  (A : Matrix (Fin m) (Fin m) ℝ)
  (B : Matrix (Fin n) (Fin n) ℝ)
  (C : Matrix (Fin m) (Fin n) ℝ) :
  (∃! X : Matrix (Fin m) (Fin n) ℝ, A * X + X * B = C) ↔
  (∀ (z₁ z₂ : ℂ),
    (Polynomial.map (algebraMap ℝ ℂ) (Matrix.charpoly A)).IsRoot z₁ →
    (Polynomial.map (algebraMap ℝ ℂ) (Matrix.charpoly B)).IsRoot z₂ →
    z₁ + z₂ ≠ 0) := by
  sorry







theorem theorem_155979_problem (F : Type*) [Field F] [Finite F]
  (V : Type*) [AddCommGroup V] [Module F V] :
  ¬ Nonempty (V ≃+ ℤ) := by
  sorry

theorem theorem_155663_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {n : Type*} [Fintype n] [DecidableEq n]
  (β β' : Basis n F V)
  (T : V →ₗ[F] V)
  (A_β : Matrix n n F := LinearMap.toMatrix β β T)
  (A_β' : Matrix n n F := LinearMap.toMatrix β' β' T)
  (P : Matrix n n F := β'.toMatrix β) :
  A_β' = P⁻¹ * A_β * P := by
  sorry



theorem theorem_155874_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  (S : Set V)
  (hS : LinearIndependent F ((↑) : S → V)) :
  ∃ B : Set V, S ⊆ B ∧ LinearIndependent F ((↑) : B → V) ∧ Submodule.span F B = ⊤ := by
  sorry

theorem theorem_156213_problem (n : ℕ) (f : (Fin n → ℝ) → ℝ)
  (hf : ContDiff ℝ 2 f) (x y : Fin n → ℝ) :
  ∑ i : Fin n, iteratedFDeriv ℝ 2 (fun u ↦ f (u - y)) x (fun _ ↦ Pi.single i 1) =
  ∑ i : Fin n, iteratedFDeriv ℝ 2 (fun v ↦ f (x - v)) y (fun _ ↦ Pi.single i 1) := by
  sorry



theorem theorem_155714_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (x₀ : E)
  (Z : Submodule ℝ E)
  (hZ : Z = Submodule.span ℝ {x₀})
  (f : Z → ℝ)
  (hf : ∀ α : ℝ, f ⟨α • x₀, by rw [hZ]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)⟩ = α * ‖x₀‖) :
  ∀ (x y : Z) (s : ℝ), f (x + s • y) = f x + s * f y := by
  sorry

theorem theorem_156284_problem (n : ℕ) (L : Matrix (Fin n) (Fin n) ℝ)
  (h_nonsing : IsUnit L)
  (h_lower : ∀ i j : Fin n, i < j → L i j = 0) :
  ∀ i j : Fin n, i < j → (L⁻¹) i j = 0 := by
  sorry

theorem theorem_156129_problem
  {R : Type*} [CommRing R]
  (A B : Matrix (Fin 2) (Fin 2) R) :
  Matrix.det A * Matrix.det B = Matrix.det (A * B) := by
  sorry











theorem theorem_156881_problem
  (f g : (Fin 2 → ℝ) → (Fin 2 → ℝ))
  (z : Fin 2 → ℝ)
  (hg : DifferentiableAt ℝ g z)
  (hf : DifferentiableAt ℝ f (g z)) :
  LinearMap.det ((fderiv ℝ f (g z)).toLinearMap) * LinearMap.det ((fderiv ℝ g z).toLinearMap) =
  LinearMap.det ((fderiv ℝ (f ∘ g) z).toLinearMap) := by
  sorry



theorem theorem_157007_problem
  (S : Set (lp (fun _ : ℕ => ℝ) 2))
  (hS : S = { x | Set.Finite { k | x k ≠ 0 } ∧ ∑' k, x k = 0 }) :
  Dense S := by
  sorry

theorem theorem_157394_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (f : V →ₗ[ℝ] ℝ)
  (h : ∃ B : ℝ, ∀ x : V, f x ≥ B) :
  ∀ x : V, f x = 0 := by
  sorry

theorem theorem_157138_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (A : Matrix n n ℂ)
  (h_distinct : (Matrix.charpoly A).Separable)
  (B C : Matrix n n ℂ)
  (hB_inv : IsUnit B)
  (hC_inv : IsUnit C)
  (hB_comm : A * B = B * A)
  (hC_comm : A * C = C * A) :
  B * C = C * B := by
  sorry





theorem theorem_156958_problem 
  (m : ℕ) -- Let m denote the number of iterations
  (hm : m > 0)
  (cost_solve : ℕ → ℝ) -- Cost of solving the linear system per iteration
  (cost_eval : ℕ → ℝ) -- Cost of additional computations per iteration
  -- The linear system solve accounts for n^3/3 (plus lower order terms)
  (h_solve : (fun n => cost_solve n - (1/3 : ℝ) * (n : ℝ)^3) =O[atTop] (fun n => (n : ℝ)^2))
  -- Additional computations account for O(n^2)
  (h_eval : cost_eval =O[atTop] (fun n => (n : ℝ)^2)) :
  -- The total complexity is mn^3/3 + O(mn^2)
  (fun n => (m : ℝ) * (cost_solve n + cost_eval n) - ((m : ℝ) * (n : ℝ)^3) / 3) =O[atTop] (fun n => (m : ℝ) * (n : ℝ)^2) := by
  sorry











theorem theorem_157822_problem
  {n : ℕ}
  {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M]
  (e : Basis (Fin n) R M)
  (dx : Fin n → Module.Dual R M)
  (h_dual : ∀ i j, dx i (e j) = if i = j then 1 else 0)
  (J_comp : Fin n → Fin n → R)
  (X_comp : Fin n → R)
  (X : M)
  (hX : X = ∑ l, X_comp l • e l)
  (J : M →ₗ[R] M)
  (hJ : J = ∑ i, ∑ k, J_comp i k • LinearMap.smulRight (dx i) (e k)) :
  ∀ k, e.repr (J X) k = ∑ l, J_comp l k * X_comp l := by
  sorry







theorem theorem_157760_problem
  (n m : ℕ)
  (F : (Fin n → ℝ) → (Fin m → ℝ))
  (hF : Differentiable ℝ F)
  (x y : Fin n → ℝ)
  (t : ℝ) :
  IsLinearMap ℝ (fderiv ℝ F (x + t • y)) := by
  sorry

