import Mathlib
import Mathlib.Tactic











theorem theorem_401767_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (P : Matrix n n ℝ)
  (hP_pos : P.PosDef)
  (hP_le_I : (1 - P).PosSemidef) :
  Real.log P.det ≤ (P - 1).trace := by
  sorry

theorem theorem_402471_problem :
  ∃ ε : ℝ, ε > 0 ∧
  let A : ℝ := ε
  let B : ℝ := -ε
  abs (Complex.arg (A : ℂ) - Complex.arg (B : ℂ)) > abs (A - B) := by
  sorry



theorem theorem_402350_problem :
  ∃ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ),
    A.IsSymm ∧ B ^ 2 = 1 ∧ A * B ≠ B * A := by
  sorry



theorem theorem_401560_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  (A : V →ₗ[K] V)
  (x y : V)
  (hx1 : (A ^ 3) x = 0)
  (hx2 : (A ^ 2) x ≠ 0)
  (hy1 : (A ^ 3) y = 0)
  (hy2 : (A ^ 2) y ≠ 0)
  (h_cond : y ∉ Submodule.span K {x, A x, (A ^ 2) x} + LinearMap.ker (A ^ 2)) :
  LinearIndependent K ![x, A x, (A ^ 2) x, y, A y, (A ^ 2) y] := by
  sorry

theorem theorem_402215_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  (W : Subspace 𝕜 V)
  (R : (V ⧸ W) →L[𝕜] V)
  (h_inv : ∀ x : V ⧸ W, W.mkQ (R x) = x)
  (h_complete : CompleteSpace (V ⧸ W)) :
  ∃ U : Subspace 𝕜 V, IsClosed (U : Set V) ∧ IsCompl U W := by
  sorry

theorem theorem_402092_problem (n : ℕ) (hn : n > 0)
  (A : Matrix (Fin n) (Fin n) ℤ)
  (hA : ∀ (i j : Fin n), A i j = if i = j then 1 else (j : ℤ) + 1) :
  A.det = (-1 : ℤ) ^ (n - 1) * (Nat.factorial (n - 1) : ℤ) := by
  sorry











theorem theorem_402533_problem (n : ℕ)
  (D : Matrix (Fin n) (Fin n) ℝ)
  (u : Fin n → ℝ)
  (v : Fin n → ℝ)
  (hv : v = Matrix.mulVec D u)
  (h_col_sum : ∀ j, ∑ i, D i j = 0) :
  ∑ i, v i = 0 := by
  sorry

theorem theorem_401777_problem (n : ℕ)
  (g : (Fin n → ℝ) → ((Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
  (e : Fin n → (Fin n → ℝ))
  (he : e = Pi.basisFun ℝ (Fin n))
  (h_cont : ∀ k : Fin n, Continuous (fun x => g x (e k))) :
  ∀ v : Fin n → ℝ, Continuous (fun x => g x v) := by
  sorry











theorem theorem_402503_problem
  (A : Type*) [AddCommGroup A] [Module ℤ A]
  [Module.Free ℤ A] [Module.Finite ℤ A]
  (β : ℤ) (hβ : β ≠ 0) :
  let m_β : A →ₗ[ℤ] A := LinearMap.lsmul ℤ A β
  Int.natAbs (LinearMap.det m_β) = Nat.card (A ⧸ LinearMap.range m_β) := by
  sorry

theorem theorem_403376_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (h : ∀ i j, |A i j| ≤ 1) :
  |A.det| ≤ (Nat.factorial n : ℝ) := by
  sorry











theorem theorem_402693_problem
  {n : ℕ} [NeZero n]
  (A M : Matrix (Fin n) (Fin n) ℝ)
  -- σA, σM, σAM represent the singular values of A, M, and AM respectively
  (σA σM σAM : Fin n → ℝ)
  -- Condition: Singular values are sorted descending
  (hA_anti : Antitone σA)
  (hM_anti : Antitone σM)
  (hAM_anti : Antitone σAM)
  -- Condition: Singular values are non-negative
  (hA_nonneg : ∀ i, 0 ≤ σA i)
  (hM_nonneg : ∀ i, 0 ≤ σM i)
  (hAM_nonneg : ∀ i, 0 ≤ σAM i)
  -- Condition: The squares of the singular values are the eigenvalues of XᵀX
  -- (represented here by the roots of the characteristic polynomial)
  (hA_vals : Multiset.map (· ^ 2) (Multiset.ofList (List.ofFn σA)) = (A.transpose * A).charpoly.roots)
  (hM_vals : Multiset.map (· ^ 2) (Multiset.ofList (List.ofFn σM)) = (M.transpose * M).charpoly.roots)
  (hAM_vals : Multiset.map (· ^ 2) (Multiset.ofList (List.ofFn σAM)) = ((A * M).transpose * (A * M)).charpoly.roots) :
  ∀ i : Fin n,
    σA i * σM (Fin.last (n - 1)) ≤ σAM i ∧ σAM i ≤ σA i * σM 0 := by
  sorry





theorem theorem_403171_problem
  (n m k : ℕ)
  (E : Matrix (Fin n) (Fin m) ℝ)
  (U : Matrix (Fin n) (Fin k) ℝ)
  (S : Matrix (Fin k) (Fin k) ℝ)
  (V : Matrix (Fin m) (Fin k) ℝ)
  (h_rank : E.rank = k)
  (h_svd : E = U * S * V.transpose)
  (h_U_ortho : U.transpose * U = 1)
  (h_S_diag : S.IsDiag)
  (h_S_pos : ∀ i, 0 < S i i)
  (h_V_ortho : V.transpose * V = 1) :
  LinearMap.range (Matrix.toLin' E) = LinearMap.range (Matrix.toLin' U) := by
  sorry















theorem theorem_403860_problem
  {R : Type*} [CommRing R]
  (n : ℕ)
  (x : Fin n → R)
  (h_distinct : Function.Injective x) :
  (Matrix.of (fun i j : Fin n => x i ^ (j : ℕ))).det = 
  ∏ i : Fin n, ∏ j in Finset.Ioi i, (x j - x i) := by
  sorry

theorem theorem_403792_problem
  (n m : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (c : Fin n → ℝ) :
  ConvexOn ℝ Set.univ (fun x =>
    2 * (∑ i, |x i|) + (∑ j, (Matrix.mulVec A x - b) j ^ 2) - Matrix.dotProduct c x) := by
  sorry



theorem theorem_403876_problem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
  sSup {r : ℝ | ∃ (x : Fin m → ℝ) (y : Fin n → ℝ), x ≠ 0 ∧ y ≠ 0 ∧
    r = (Matrix.dotProduct x (Matrix.mulVec A y)) /
      (Real.sqrt (Matrix.dotProduct x x) * Real.sqrt (Matrix.dotProduct y y))} =
  sSup {r : ℝ | ∃ (y : Fin n → ℝ), y ≠ 0 ∧
    r = Real.sqrt (Matrix.dotProduct (Matrix.mulVec A y) (Matrix.mulVec A y)) /
      Real.sqrt (Matrix.dotProduct y y)} := by
  sorry

theorem theorem_403802_problem (n : ℕ) (x y : Fin n → ℂ) :
  Complex.abs (∑ i, x i * star (y i)) ≤ 
  Real.sqrt (∑ i, x i * star (x i)).re * Real.sqrt (∑ i, y i * star (y i)).re := by
  sorry





theorem theorem_404005_problem
  {I J K L M P Q R : Type*}
  [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype M]
  [Fintype P] [Fintype Q] [Fintype R]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [DecidableEq M]
  [DecidableEq P] [DecidableEq Q] [DecidableEq R]
  (g : (P × Q × R → ℝ) → (I × J → ℝ))
  (f : (I × J → ℝ) → (K × L × M → ℝ))
  (x : P × Q × R → ℝ)
  (hg : DifferentiableAt ℝ g x)
  (hf : DifferentiableAt ℝ f (g x)) :
  ∀ (k : K) (l : L) (m : M) (p : P) (q : Q) (r : R),
    fderiv ℝ (f ∘ g) x (Pi.single (p, q, r) 1) (k, l, m) =
    ∑ i : I, ∑ j : J,
      (fderiv ℝ f (g x) (Pi.single (i, j) 1) (k, l, m)) *
      (fderiv ℝ g x (Pi.single (p, q, r) 1) (i, j)) := by
  sorry





theorem theorem_404394_problem
  (x y : ℝ → ℂ)
  (hx : ∀ t, x t = (t : ℂ) * I)
  (hy : ∀ t, y t = 2 * (t : ℂ)) :
  (∫ t in (0 : ℝ)..1, deriv x t * star (y t)) ≠
  (∫ t in (0 : ℝ)..1, star (x t) * deriv y t) := by
  sorry





theorem theorem_404093_problem :
  ∃ (n : ℕ) (X U Y : Matrix (Fin n) (Fin n) ℝ),
    X.IsSymm ∧ U.IsSymm ∧ Y.IsSymm ∧
    X.PosDef ∧ U.PosDef ∧ Y.PosDef ∧
    ¬ (Y * X * Y - U * X * U).PosDef := by
  sorry





















theorem theorem_404506_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {n : ℕ}
  (b : Basis (Fin n) F V)
  (α : F) (hα : α ≠ 0) :
  let b' := fun i => α • b i
  LinearIndependent F b' ∧ Submodule.span F (Set.range b') = ⊤ := by
  sorry

theorem theorem_405058_problem (n : ℕ) 
  (norm1 norm2 : (Fin n → ℝ) → ℝ)
  (h1_nonneg : ∀ x, 0 ≤ norm1 x)
  (h1_def : ∀ x, norm1 x = 0 ↔ x = 0)
  (h1_hom : ∀ (c : ℝ) (x : Fin n → ℝ), norm1 (c • x) = |c| * norm1 x)
  (h1_tri : ∀ x y, norm1 (x + y) ≤ norm1 x + norm1 y)
  (h2_nonneg : ∀ x, 0 ≤ norm2 x)
  (h2_def : ∀ x, norm2 x = 0 ↔ x = 0)
  (h2_hom : ∀ (c : ℝ) (x : Fin n → ℝ), norm2 (c • x) = |c| * norm2 x)
  (h2_tri : ∀ x y, norm2 (x + y) ≤ norm2 x + norm2 y) :
  ∃ C1 C2 : ℝ, C1 > 0 ∧ C2 > 0 ∧ 
    ∀ x y : Fin n → ℝ, 
      C1 * norm1 (x - y) ≤ norm2 (x - y) ∧ 
      norm2 (x - y) ≤ C2 * norm1 (x - y) := by
  sorry

theorem theorem_405361_problem
  (n : ℕ)
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA : A.PosSemidef)
  (hB : B.PosSemidef)
  (h_le : (B - A).PosSemidef) :
  A.trace ≤ B.trace := by
  sorry







theorem theorem_404661_problem (n k : ℕ)
  (X : Matrix (Fin n) (Fin k) ℝ)
  (y epsilon : Matrix (Fin n) (Fin 1) ℝ)
  (beta : Matrix (Fin k) (Fin 1) ℝ)
  (h_model : y = X * beta + epsilon)
  (h_inv : Invertible (Matrix.transpose X * X)) :
  let beta_hat := (Matrix.transpose X * X)⁻¹ * Matrix.transpose X * y
  let outer_prod := epsilon * Matrix.transpose epsilon
  let sandwich := (Matrix.transpose X * X)⁻¹ * (Matrix.transpose X * outer_prod * X) * (Matrix.transpose X * X)⁻¹
  (beta_hat - beta) * Matrix.transpose (beta_hat - beta) = sandwich := by
  sorry

theorem theorem_405454_problem
  (m n : ℕ)
  (hm : m ≥ n)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (h_lin_indep : LinearIndependent ℝ (fun j i => A i j)) :
  ∃ (Q : Matrix (Fin m) (Fin n) ℝ) (R : Matrix (Fin n) (Fin n) ℝ),
    A = Q * R ∧
    Q.transpose * Q = 1 ∧
    (∀ i j, j < i → R i j = 0) ∧
    IsUnit R := by
  sorry



theorem theorem_405531_problem
  {R : Type*} [CommRing R] {n : ℕ}
  (A L U : Matrix (Fin n) (Fin n) R)
  (h_decomp : A = L * U)
  (hL_lower : ∀ i j, i < j → L i j = 0)
  (hU_upper : ∀ i j, j < i → U i j = 0)
  (hL_diag : ∀ i j, i ≠ j → L i j = 0)
  (hU_diag : ∀ i j, i ≠ j → U i j = 0) :
  ∀ i j, i ≠ j → A i j = 0 := by
  sorry

theorem theorem_404790_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (x_n : ℕ → X) (x : X)
  (h_weak : ∀ φ : NormedSpace.Dual ℝ X, Filter.Tendsto (fun n => φ (x_n n)) Filter.atTop (nhds (φ x)))
  (h_norm : Filter.Tendsto (fun n => ‖x_n n‖) Filter.atTop (nhds ‖x‖)) :
  Filter.Tendsto x_n Filter.atTop (nhds x) := by
  sorry











theorem theorem_405374_problem
  {I V : Type*} [AddCommGroup V] [Module ℝ V]
  (S : I → V)
  (h_span : ∀ v : V, ∃ c : I →₀ ℝ, Finsupp.total I V ℝ S c = v)
  (h_indep : ∀ c : I →₀ ℝ, Finsupp.total I V ℝ S c = 0 → c = 0) :
  ∀ v : V, ∃! c : I →₀ ℝ, Finsupp.total I V ℝ S c = v := by
  sorry

theorem theorem_405405_problem
  {R : Type*} [CommRing R]
  {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
  (A B L D U : Matrix n n R)
  (h_decomp : B = L * D * U)
  (h_L_tri : ∀ i j, i < j → L i j = 0)
  (h_L_diag : ∀ i, L i i = 1)
  (h_D_diag : ∀ i j, i ≠ j → D i j = 0)
  (h_U_tri : ∀ i j, j < i → U i j = 0)
  (h_U_diag : ∀ i, U i i = 1) :
  (A * B).det = A.det * B.det := by
  sorry

theorem theorem_405574_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (θ θ' : V →ₗ[F] V)
  (h : θ.comp θ' = LinearMap.id) :
  θ'.comp θ = LinearMap.id := by
  sorry

theorem theorem_405238_problem
  (f₁ f₂ g₁ g₂ : ℝ → ℝ)
  (hf₁ : Differentiable ℝ f₁)
  (hf₂ : Differentiable ℝ f₂)
  (hg₁ : Differentiable ℝ g₁)
  (hg₂ : Differentiable ℝ g₂) :
  ∀ x : ℝ, deriv (fun t => Matrix.det !![f₁ t, g₁ t; f₂ t, g₂ t]) x =
    Matrix.det !![deriv f₁ x, deriv g₁ x; f₂ x, g₂ x] +
    Matrix.det !![f₁ x, g₁ x; deriv f₂ x, deriv g₂ x] := by
  sorry

theorem theorem_405599_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (w v : E) (r : ℝ) :
  deriv (fun t : ℝ => w + t • v) r = v := by
  sorry

theorem theorem_405142_problem
  (n : ℕ) (hn : n > 2)
  (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (b : OrthonormalBasis (Fin n) ℝ E)
  (v : E) (hv : v ≠ 0)
  (theta : ℝ) (htheta : 0 ≤ theta ∧ theta < 2 * Real.pi)
  (h_span : v ∈ Submodule.span ℝ {b ⟨0, by linarith⟩, b ⟨1, by linarith⟩}) :
  let b1 := b ⟨0, by linarith⟩
  let b2 := b ⟨1, by linarith⟩
  let x1 := inner b1 v
  let x2 := inner b2 v
  -- The vector v' defined by applying the rotation matrix R_theta to the coordinates (x1, x2)
  let v_prime_matrix := (x1 * Real.cos theta - x2 * Real.sin theta) • b1 +
                        (x1 * Real.sin theta + x2 * Real.cos theta) • b2
  -- The vector v' defined by applying the geometric rotation to the basis vectors
  let v_prime_geom := x1 • (Real.cos theta • b1 + Real.sin theta • b2) +
                      x2 • (-Real.sin theta • b1 + Real.cos theta • b2)
  v_prime_matrix = v_prime_geom := by
  sorry











theorem theorem_405857_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  (F : V →ₗ[K] K)
  (hF : F ≠ 0) :
  ∃ r : K, r ≠ 0 ∧ ∃ x : V, x ≠ 0 ∧ F (r⁻¹ • x) = 1 := by
  sorry











