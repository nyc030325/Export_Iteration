import Mathlib
import Mathlib.Tactic

theorem theorem_163105_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  {W : Type*} [AddCommGroup W] [Module F W]
  {I : Type*}
  (T : V →ₗ[F] W)
  (v : Basis I F V) :
  LinearMap.range T = Submodule.span F (Set.range (fun i => T (v i))) := by
  sorry



theorem theorem_162973_problem
  (n : ℕ)
  (C : Set ((Fin n → ℝ) × ℝ))
  (hC_closed : IsClosed C)
  (hC_sigma : SigmaCompactSpace C)
  (r : (Fin n → ℝ) → EReal)
  (hr : ∀ x, r x = sSup ((fun t : ℝ ↦ (t : EReal)) '' {t | (x, t) ∈ C})) :
  Measurable r := by
  sorry



theorem theorem_163121_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) :
  ∃ (U : Matrix (Fin m) (Fin m) ℤ) (V : Matrix (Fin n) (Fin n) ℤ) (D : Matrix (Fin m) (Fin n) ℤ),
    IsUnit U.det ∧
    IsUnit V.det ∧
    D = U * A * V ∧
    (∀ (i : Fin m) (j : Fin n), i.val ≠ j.val → D i j = 0) ∧
    (∀ (k : ℕ) (hm : k < m) (hn : k < n), 0 ≤ D ⟨k, hm⟩ ⟨k, hn⟩) ∧
    (∀ (k : ℕ) (hm : k + 1 < m) (hn : k + 1 < n),
      D ⟨k, Nat.lt_of_succ_lt hm⟩ ⟨k, Nat.lt_of_succ_lt hn⟩ ∣ D ⟨k + 1, hm⟩ ⟨k + 1, hn⟩) := by
  sorry

theorem theorem_162684_problem
  (n : ℕ) (hn : 0 < n)
  (lam : ℝ) (hlam : 1 < lam)
  (C : Fin n → ℝ)
  (hC : C = fun _ ↦ 1 / (n : ℝ))
  (Δ : Set (Fin n → ℝ))
  (hΔ : Δ = {θ | (∑ i, θ i) = 1 ∧ ∀ i, 0 ≤ θ i})
  (Δ' : Set (Fin n → ℝ))
  (hΔ' : Δ' = {θ' | ∃ θ ∈ Δ, θ' = C + lam • (θ - C)}) :
  Δ' = {θ' | (∑ i, θ' i) = 1 ∧ ∀ i, (1 - lam) / (n : ℝ) ≤ θ' i} := by
  sorry



theorem theorem_163343_problem (N : ℕ) (B : Matrix (Fin N) (Fin N) ℝ)
  (h : IsUnit (1 - B)) :
  (1 - B)⁻¹ - 1 = B * (1 - B)⁻¹ := by
  sorry

theorem theorem_163352_problem 
  (n : ℕ)
  (a a_s : ℝ)
  (B B_s : Matrix (Fin n) (Fin n) ℝ)
  (Γ_tilde : ℝ → Matrix (Fin n) (Fin n) ℝ → ℝ)
  (consistent : (ℝ → Matrix (Fin n) (Fin n) ℝ → ℝ) → ℝ → Matrix (Fin n) (Fin n) ℝ → Prop)
  (h_eq_a : a_s = a)
  (h_eq_B : B_s = B)
  (h_framework : consistent Γ_tilde a B) :
  consistent Γ_tilde a_s B_s := by
  sorry



theorem theorem_163758_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {E : Type*} [TopologicalSpace E]
  (A : E → Matrix n n ℝ)
  (B : Matrix n n ℝ)
  (hA_symm : ∀ x, (A x).IsSymm)
  (hB_symm : B.IsSymm)
  (hA_cont : Continuous A) :
  frontier {x | (A x - B).PosSemidef} =
  {x | (A x - B).PosSemidef ∧ (A x - B).det = 0} := by
  sorry





theorem theorem_163905_problem
  {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (T : LinearPMap 𝕜 H H)
  (h_dense : Dense (T.domain : Set H)) :
  T.IsClosable ↔
  (∀ (u : ℕ → T.domain) (v : H),
    Filter.Tendsto (fun n => (u n : H)) Filter.atTop (nhds 0) →
    Filter.Tendsto (fun n => T (u n)) Filter.atTop (nhds v) →
    v = 0) := by
  sorry









theorem theorem_163478_problem (n : ℕ) (C X : Matrix (Fin n) (Fin n) ℝ)
  (hX : X.IsSymm) :
  ∑ i, ∑ j, C i j * X i j =
  ∑ i, ∑ j, ((1 / 2 : ℝ) • (C + C.transpose)) i j * X i j := by
  sorry

theorem theorem_161154_problem
  (n m : ℕ) [NeZero m]
  (D : Set (Fin n → ℝ))
  (hD : Convex ℝ D)
  (A₀ : Matrix (Fin m) (Fin m) ℝ)
  (A_seq : Fin n → Matrix (Fin m) (Fin m) ℝ)
  (hA₀ : A₀.IsSymm)
  (hA_seq : ∀ i, (A_seq i).IsSymm)
  (A : (Fin n → ℝ) → Matrix (Fin m) (Fin m) ℝ)
  (hA_aff : ∀ x, A x = A₀ + ∑ i, x i • A_seq i) :
  ∃ f : (Fin n → ℝ) → ℝ,
    (∀ x, ∃ h : (A x).IsHermitian, f x = ⨆ i, h.eigenvalues i) ∧
    ConvexOn ℝ D f := by
  sorry







theorem theorem_163976_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (L : Set V) (hL : LinearIndependent F (fun x : L ↦ (x : V))) :
  ∃ B : Set V, L ⊆ B ∧ LinearIndependent F (fun x : B ↦ (x : V)) ∧ Submodule.span F B = ⊤ := by
  sorry



theorem theorem_164308_problem
  (F₁ F : Type*) [Field F₁] [Field F] [Algebra F₁ F]
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) F₁)
  (Y : Fin m → F₁)
  (h_exists_in_F : ∃ X : Fin n → F, Matrix.mulVec (A.map (algebraMap F₁ F)) X = fun i ↦ algebraMap F₁ F (Y i)) :
  ∃ X : Fin n → F₁, Matrix.mulVec A X = Y := by
  sorry



theorem theorem_164462_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  (L : X →L[𝕜] X) :
  ∃ S T : X →L[𝕜] X, IsUnit S ∧ IsUnit T ∧ L = S + T := by
  sorry





theorem theorem_164946_problem (n : ℕ) :
  (Fintype.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : ℝ) /
  (Fintype.card (Matrix (Fin n) (Fin n) (ZMod 2)) : ℝ) =
  ∏ k in Finset.range n, (1 - (1 : ℝ) / 2 ^ (k + 1)) := by
  sorry







theorem theorem_164809_problem
  {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (f g : V → ℝ) :
  ∑ v, f v * (∑ w in G.neighborFinset v, (g w - g v)) =
  ∑ v, (∑ w in G.neighborFinset v, (f w - f v)) * g v := by
  sorry









theorem theorem_165198_problem
  {F : Type*} [Field F]
  {n : Type*} [Fintype n] [DecidableEq n]
  (A S : Matrix n n F)
  (h_comm : A * S = S * A)
  (hS : IsUnit S) :
  S⁻¹ * A * S = A := by
  sorry

















theorem theorem_165347_problem
  (A : Type*) [CommRing A] [Algebra ℝ A]
  (I : Submodule ℝ A)
  (I_sq : Set A)
  (hI_sq : I_sq = { x : A | ∃ (n : ℕ) (f g : Fin n → A),
    (∀ i, f i ∈ I) ∧ (∀ i, g i ∈ I) ∧ x = ∑ i : Fin n, f i * g i }) :
  ∃ (S : Submodule ℝ A), (S : Set A) = I_sq := by
  sorry







theorem theorem_165705_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (A : Matrix n n ℝ)
  (h_spec : ∀ z ∈ (Polynomial.map (algebraMap ℝ ℂ) A.charpoly).roots, z.im = 0 ∧ 0 < z.re) :
  ((Polynomial.map (algebraMap ℝ ℂ) A.charpoly).roots.map (fun z => Real.log z.re)).sum ≤ (A - 1).trace := by
  sorry

theorem theorem_165515_problem (X : Type*) [MetricSpace X] [CompactSpace X] :
  ∀ x y : X, dist x y = sSup { r | ∃ f : ContinuousMap X ℝ, LipschitzWith 1 f ∧ r = |f x - f y| } := by
  sorry



theorem theorem_165612_problem (n : ℕ) (F : Type*) [Field F] (h_char : ringChar F ≠ 2)
  (A : Matrix (Fin n) (Fin n) F) (h_skew : A.transpose = -A) :
  ∀ x : Fin n → F, Matrix.dotProduct x (Matrix.mulVec A x) = 0 := by
  sorry

theorem theorem_165925_problem
  (X Y : Type*)
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (hAD : AxiomOfDeterminacy)
  (hDC : PrincipleOfDependentChoices)
  (A : X →ₗ[ℝ] Y) :
  Continuous A := by
  sorry

theorem theorem_165449_problem (m n : ℕ) (A B : Matrix (Fin m) (Fin n) ℝ)
  (hB : ∑ i, ∑ j, (B i j)^2 ≠ 0) :
  let F : ℝ → ℝ := fun x ↦ ∑ i, ∑ j, (A i j - x * B i j)^2
  let x_star : ℝ := (∑ i, ∑ j, A i j * B i j) / (∑ i, ∑ j, (B i j)^2)
  IsMinOn F Set.univ x_star := by
  sorry



theorem theorem_165906_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  (e : Basis n K V)
  (g : Matrix n n K)
  (h_g_symm : g.IsSymm)
  (h_g_inv : Invertible g)
  (A : V →ₗ[K] V)
  (AT : V →ₗ[K] V)
  (x : V)
  (inner : V → V → K)
  (h_inner : ∀ u v, inner u v = ∑ i, ∑ j, (e.repr u i) * g i j * (e.repr v j))
  (h_transpose : ∀ u v, inner (A u) v = inner u (AT v)) :
  AT x = ∑ j, (∑ i, ∑ p, ∑ q, (e.repr x i) * g i p * (LinearMap.toMatrix e e A p q) * (⅟g q j)) • e j := by
  sorry



theorem theorem_165971_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [Nontrivial H]
  (B C : H →L[ℂ] H)
  (hB : IsSelfAdjoint B) (hC : IsSelfAdjoint C)
  (h_no_common : ¬ ∃ v : H, v ≠ 0 ∧ (∃ b : ℂ, B v = b • v) ∧ (∃ c : ℂ, C v = c • v)) :
  ∃ v : H, v ≠ 0 ∧ (∃ a : ℂ, (B + C) v = a • v) ∧
  ¬ ((∃ b : ℂ, B v = b • v) ∨ (∃ c : ℂ, C v = c • v)) := by
  sorry



theorem theorem_166562_problem (n : ℕ) (M Q : Matrix (Fin n) (Fin n) ℝ)
  (hM : M.IsSymm)
  (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ)
  (hComm : Q * M = M * Q) :
  ∀ (μ : ℝ), Submodule.map (Matrix.toLin' Q) (Module.End.eigenspace (Matrix.toLin' M) μ) =
    Module.End.eigenspace (Matrix.toLin' M) μ := by
  sorry

theorem theorem_166548_problem (n : ℕ) (x : Fin n → ℝ) (hn : n ≠ 0) :
  Filter.Tendsto (fun p : ℝ => (∑ i, |x i| ^ p) ^ (1 / p)) Filter.atTop (nhds (⨆ i, |x i|)) := by
  sorry

theorem theorem_166507_problem
  (n : ℕ)
  (V : Type*)
  [AddCommGroup V]
  [Module ℂ V]
  [FiniteDimensional ℂ V]
  (h_dim : FiniteDimensional.finrank ℂ V = 2 * n)
  (I J K : Module.End ℂ V)
  (hI : I ^ 2 = -1)
  (hJ : J ^ 2 = -1)
  (hK : K ^ 2 = -1)
  (hIJK : I * J * K = -1) :
  Nonempty (Module (Quaternion ℝ) V) := by
  sorry



theorem theorem_166442_problem
  (v : Quaternion ℝ)
  (q q1 : Quaternion ℝ)
  (T T1 : Quaternion ℝ)
  (hq : ‖q‖ = 1)
  (hq1 : ‖q1‖ = 1) :
  q1 * (q * v * q⁻¹ + T) * q1⁻¹ + T1 = (q1 * q) * v * (q1 * q)⁻¹ + q1 * T * q1⁻¹ + T1 := by
  sorry





theorem theorem_166311_problem 
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (X Y : Submodule K V) 
  (h : IsCompl X Y)
  (f : V →ₗ[K] V)
  -- We define P_X and P_Y as endomorphisms on V derived from the direct sum decomposition.
  -- This aligns with the problem's usage of "projection maps" in the operator sum equation.
  (P_X : V →ₗ[K] V := X.subtype.comp (Submodule.linearProjOfIsCompl X Y h))
  (P_Y : V →ₗ[K] V := Y.subtype.comp (Submodule.linearProjOfIsCompl Y X h.symm)) :
  f = P_X * f * P_X + P_X * f * P_Y + P_Y * f * P_X + P_Y * f * P_Y := by
  sorry





theorem theorem_166191_problem (m b : ℝ) (xi_tilde xj_tilde yi_tilde yj_tilde ci cj : ℝ)
  (hci : ci ≠ 0) (hcj : cj ≠ 0)
  (h_diff : xj_tilde ≠ xi_tilde)
  (hyi : yi_tilde = m * xi_tilde + b * ci⁻¹)
  (hyj : yj_tilde = m * xj_tilde + b * cj⁻¹) :
  (yj_tilde - yi_tilde) / (xj_tilde - xi_tilde) =
  m + (b * (cj⁻¹ - ci⁻¹)) / (xj_tilde - xi_tilde) := by
  sorry





theorem theorem_167026_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (F : V →ₗ[ℝ] ℝ)
  (M : Submodule ℝ V)
  (h : ∃ v ∈ M, F v ≠ 0) :
  Function.Surjective (F.domRestrict M) := by
  sorry



theorem theorem_166756_problem (n k : ℕ) (r : Fin k → ℕ)
  (h_mono : StrictMono r)
  (h_bounds : ∀ i, 1 ≤ r i ∧ r i ≤ n) :
  ∑ i : Fin k, (n - r i - (k - 1 - (i : ℕ))) =
  ∑ j : Fin k, (n - r (Fin.rev j) - (j : ℕ)) := by
  sorry









theorem theorem_166680_problem
  (N D : ℕ)
  (t : Fin N → ℝ)
  (x : Fin N → Fin D → ℝ)
  (C : ℝ)
  (hC : C > 0) :
  ∀ w : Fin D → ℝ,
    C * (∑ n : Fin N, (t n - ∑ i : Fin D, w i * x n i)^2) +
      (1 / 2) * (∑ i : Fin D, ((w i)^2 / |w i| + |w i|)) =
    C * ((∑ n : Fin N, (t n - ∑ i : Fin D, w i * x n i)^2) +
      (1 / C) * (∑ i : Fin D, |w i|)) := by
  sorry

theorem theorem_166971_problem
  {K : Type*} [Field K]
  {A B C A' B' C' : Type*}
  [AddCommGroup A] [Module K A] [FiniteDimensional K A]
  [AddCommGroup B] [Module K B] [FiniteDimensional K B]
  [AddCommGroup C] [Module K C] [FiniteDimensional K C]
  [AddCommGroup A'] [Module K A'] [FiniteDimensional K A']
  [AddCommGroup B'] [Module K B'] [FiniteDimensional K B']
  [AddCommGroup C'] [Module K C'] [FiniteDimensional K C']
  (i : A →ₗ[K] B) (p : B →ₗ[K] C)
  (i' : A' →ₗ[K] B') (p' : B' →ₗ[K] C')
  (h1 : Function.Injective i)
  (h2 : Function.Surjective p)
  (h3 : LinearMap.range i = LinearMap.ker p)
  (h1' : Function.Injective i')
  (h2' : Function.Surjective p')
  (h3' : LinearMap.range i' = LinearMap.ker p')
  (h_comm : ∃ (f : A →ₗ[K] A') (g : C →ₗ[K] C') (h : B →ₗ[K] B'),
    h.comp i = i'.comp f ∧ g.comp p = p'.comp h) :
  Nonempty (LinearMap.range p ≃ₗ[K] LinearMap.range p') := by
  sorry

theorem theorem_167727_problem (A : Matrix (Fin 3) (Fin 3) ℝ)
  (h_ortho : A * A.transpose = 1)
  (h_skew : A.transpose = -A) :
  False := by
  sorry



theorem theorem_167271_problem
  (k : ℕ) [Fact (0 < k)]
  (F : EuclideanSpace ℝ (Fin k) → ℝ)
  (hF : ContDiff ℝ 1 F)
  (x : ℝ) (hx : 0 < x) :
  let box : ℝ → Set (EuclideanSpace ℝ (Fin k)) := fun t ↦ {y | ∀ i, 0 ≤ y i ∧ y i ≤ t}
  let I := fun (t : ℝ) ↦ ∫ y in box t, F y
  HasDerivAt I
    ( (k : ℝ) / x * I x +
      (1 / x) * ∫ y in box x, inner (gradient F y) y )
    x := by
  sorry











theorem theorem_167598_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (v : ℝ × E → E)
  (t dt : ℝ)
  (r dr : E)
  (h : DifferentiableAt ℝ v (t, r)) :
  fderiv ℝ v (t, r) (dt, dr) =
    fderiv ℝ (fun τ => v (τ, r)) t dt +
    fderiv ℝ (fun ρ => v (t, ρ)) r dr := by
  sorry











theorem theorem_167747_problem
  (u : ℕ → ℝ → ℝ)
  (σ : ℝ → ℝ)
  (φ : ℝ → ℝ)
  (h_bound : ∃ M, ∀ k x, |u k x| ≤ M)
  (h_cont_u : ∀ k, Continuous (u k))
  (h_cont_σ : Continuous σ)
  (h_nz : ∀ x, σ x ≠ 0)
  (h_conv : TendstoUniformly (fun n x ↦ ∑ k in Finset.range n, (1 / 2 : ℝ) ^ k * u k x) φ Filter.atTop) :
  Continuous (fun x ↦ (1 / σ x) * φ x) := by
  sorry

