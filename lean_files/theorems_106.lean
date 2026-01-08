import Mathlib
import Mathlib.Tactic



theorem theorem_572818_problem
  {X : Type*} [AddCommGroup X] [Module ℝ X]
  (p : X → ℝ)
  (hp_add : ∀ x y : X, p (x + y) ≤ p x + p y)
  (hp_mul : ∀ (c : ℝ) (x : X), 0 ≤ c → p (c • x) = c * p x)
  (Y : Submodule ℝ X)
  (f : Y →ₗ[ℝ] ℝ)
  (hf : ∀ y : Y, f y ≤ p y) :
  ∃ g : X →ₗ[ℝ] ℝ, (∀ y : Y, g y = f y) ∧ (∀ x : X, g x ≤ p x) := by
  sorry

theorem theorem_573309_problem
  (k : Type*) [Field k]
  (A : Type*) [CommRing A] [Algebra k A]
  (h_fg : Algebra.FiniteType k A) :
  ∃ (d : ℕ) (y : Fin d → A),
    AlgebraicIndependent k y ∧
    Module.Finite (Algebra.adjoin k (Set.range y)) A := by
  sorry

theorem theorem_573451_problem {n : ℕ} {K : Type*} [Field K]
  (d : Fin n → K)
  (D : Matrix (Fin n) (Fin n) K)
  (hD : D = Matrix.diagonal d)
  (B : Matrix (Fin n) (Fin n) K)
  (hB : Invertible B)
  (M : Matrix (Fin n) (Fin n) K)
  (hM : M = B * D * B⁻¹) :
  M.charpoly = D.charpoly := by
  sorry



theorem theorem_573236_problem {G : Type*} [Group G] (H : Subgroup G) :
  MonoidHom.ker (MulAction.toPermHom G (G ⧸ H)) = ⨅ x : G, H.map (MulAut.conj x).toMonoidHom := by
  sorry



theorem theorem_573386_problem (p₁ p₂ : ℝ)
  (hp₁ : 0 < p₁ ∧ p₁ ≤ 1)
  (hp₂ : 0 < p₂ ∧ p₂ ≤ 1)
  (prob_X : ℕ → ℝ)
  (hX : ∀ k, prob_X k = p₁ * (1 - p₁) ^ k)
  (prob_Y : ℕ → ℝ)
  (hY : ∀ k, prob_Y k = p₂ * (1 - p₂) ^ k)
  (prob_Z : ℕ → ℝ)
  (hZ : ∀ z, prob_Z z = ∑' (x : ℕ), ∑' (y : ℕ), if max x y = z then prob_X x * prob_Y y else 0) :
  ∀ z : ℕ, prob_Z z = (1 - (1 - p₁) ^ (z + 1)) * (1 - (1 - p₂) ^ (z + 1)) - 
                      (1 - (1 - p₁) ^ z) * (1 - (1 - p₂) ^ z) := by
  sorry

theorem theorem_573184_problem (n : ℕ) (x : Fin (n + 1) → ℝ × ℝ)
  (h_distinct : Function.Injective x) (hn : n > 0) :
  ∃ (φ : ℝ → ℝ × ℝ) (t : Fin (n + 1) → ℝ),
    ContinuousOn φ (Set.Icc 0 1) ∧
    Set.InjOn φ (Set.Icc 0 1) ∧
    StrictMono t ∧
    t 0 = 0 ∧
    t (Fin.last n) = 1 ∧
    ∀ i, φ (t i) = x i := by
  sorry

theorem theorem_573143_problem
  -- S is a smooth algebraic variety (modeled here as a Type)
  (S : Type*)
  -- iota is an involution on S
  (iota : S → S)
  (h_iota : Function.Involutive iota)
  -- The field and vector space representing global sections H^0(S, O_S(D))
  (K : Type*) [Field K]
  (V : Type*) [AddCommGroup V] [Module K V]
  -- D is iota-invariant, which induces a linear automorphism on the space of sections V
  -- We denote this induced map as iota_star
  (iota_star : V ≃ₗ[K] V)
  -- The functoriality implies iota_star is compatible with the group structure of the involution
  (h_iota_star_inv : iota_star.trans iota_star = LinearEquiv.refl K V)
  -- The complete linear system |D| defines an embedding into Projective Space P(V*)
  -- represented here by the linear map to the dual space before projectivization
  (phi_linear : S → (V →ₗ[K] K))
  -- The map is well-defined into projective space (never zero)
  (h_phi_nonzero : ∀ x, phi_linear x ≠ 0)
  -- The compatibility condition: the evaluation of the section at iota(x) 
  -- corresponds to the evaluation of the pulled-back section at x.
  -- i.e. (iota^* s)(x) = s(iota x)
  (h_compat : ∀ (x : S) (v : V), phi_linear (iota x) v = phi_linear x (iota_star v)) :
  -- Conclusion: The embedding is iota-invariant.
  -- This means there exists a projective automorphism Psi on P^d such that 
  -- the action of iota on S is equivariant with Psi on the image.
  ∃ (Psi : Projectivization K (V →ₗ[K] K) ≃ Projectivization K (V →ₗ[K] K)),
    ∀ x, Psi (Projectivization.mk K (phi_linear x) (h_phi_nonzero x)) = 
         Projectivization.mk K (phi_linear (iota x)) (h_phi_nonzero (iota x)) := by
  sorry

theorem theorem_573732_problem :
  ∃ h : ℕ → {q : ℚ // 0 < q}, Function.Bijective h := by
  sorry

theorem theorem_573344_problem (a b c s : ℝ)
  (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
  (s^2 + a) / ((s + b)^2 + c^2) =
  1 - 2 * b * ((s + b) / ((s + b)^2 + c^2)) +
  ((a + b^2 - c^2) / c^2) * (c^2 / ((s + b)^2 + c^2)) := by
  sorry



theorem theorem_574047_problem
  {X : Type*} [MetricSpace X]
  (x : X)
  (r : ℝ)
  (hr : r > 0) :
  IsClosed {y : X | dist x y ≤ r} := by
  sorry

theorem theorem_574200_problem (n : ℕ) (F : Type*) [LinearOrderedField F] [Fintype F]
  (h1 : Fintype.card F = n) (h2 : n > 1) : False := by
  sorry



theorem theorem_573959_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (bracket : V → V → V)
  (nabla nabla_tilde : V → V → V)
  (Q : V → V → V)
  (sigma sigma_tilde : V → V → V)
  (Q_antisym : V → V → V)
  (h_trans : ∀ u v, nabla_tilde u v - nabla u v = - Q u v)
  (h_sigma : ∀ u v, sigma u v = nabla u v - nabla v u - bracket u v)
  (h_sigma_tilde : ∀ u v, sigma_tilde u v = nabla_tilde u v - nabla_tilde v u - bracket u v)
  (h_antisym : ∀ u v, Q_antisym u v = (1 / 2 : ℝ) • (Q u v - Q v u)) :
  ∀ u v, sigma_tilde u v - sigma u v = (-2 : ℝ) • Q_antisym u v := by
  sorry











theorem theorem_574393_problem
  (K : Type*) [Field K] [CharZero K]
  (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
  (F : Type*) [Field F] [Algebra K F]
  (x y : F)
  (h_curve : y^2 = x^3 + a • x + algebraMap K F b)
  (v : AddValuation F (WithTop ℤ))
  (hv_triv : ∀ k : K, k ≠ 0 → v (algebraMap K F k) = 0)
  (hv_inf : v x < 0)
  (hv_unif : v (x / y) = 1)
  (D : Derivation K F F)
  (hD_unif : D (x / y) = 1) :
  v (D x) = -3 := by
  sorry

theorem theorem_574664_problem (x : ℝ) (h : 0 < x) :
  deriv (fun x => x ^ x) x = x ^ x * (1 + Real.log x) := by
  sorry

theorem theorem_574221_problem (n k : ℕ) :
  Nonempty (Sym (Fin n) k ≃ { s : Finset (Fin (n + k - 1)) // s.card = k }) := by
  sorry

theorem theorem_574480_problem
  (x₁ y₁ x₂ y₂ x₃ y₃ : ℝ)
  (h_distinct : (x₁, y₁) ≠ (x₂, y₂) ∧ (x₁, y₁) ≠ (x₃, y₃) ∧ (x₂, y₂) ≠ (x₃, y₃))
  (a_star b_star : ℝ) :
  IsMinOn (fun (p : ℝ × ℝ) => max (|p.1 * x₁ + p.2 - y₁|) (max (|p.1 * x₂ + p.2 - y₂|) (|p.1 * x₃ + p.2 - y₃|))) Set.univ (a_star, b_star) ↔
  ∀ a b : ℝ,
    max (|a_star * x₁ + b_star - y₁|) (max (|a_star * x₂ + b_star - y₂|) (|a_star * x₃ + b_star - y₃|)) ≤
    max (|a * x₁ + b - y₁|) (max (|a * x₂ + b - y₂|) (|a * x₃ + b - y₃|)) := by
  sorry

theorem theorem_574242_problem
  {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L]
  {n : ℕ} (x : Basis (Fin n) F L)
  (A : Fin n → Fin n → Fin n → F)
  (h_str : ∀ i j, ⁅x i, x j⁆ = ∑ k, (A i j k) • x k)
  (a b : L)
  (a_coeffs b_coeffs : Fin n → F)
  (ha : a = ∑ i, (a_coeffs i) • x i)
  (hb : b = ∑ j, (b_coeffs j) • x j) :
  ⁅a, b⁆ = ∑ i, ∑ j, ∑ k, (a_coeffs i * b_coeffs j * A i j k) • x k := by
  sorry





theorem theorem_574606_problem (p x : ℝ) (hp : 0 < p) (hx : |x| < 1) :
  (1 + x) ^ (-p) = ∑' i : ℕ, (-1 : ℝ) ^ i * (Real.Gamma (p + i) / (Real.Gamma (i + 1) * Real.Gamma p)) * x ^ i := by
  sorry

theorem theorem_574456_problem (x : ℝ → ℝ)
  (h_diff : DifferentiableOn ℝ x (Set.Ioi 0))
  (h_ode : ∀ y ∈ Set.Ioi 0, deriv x y = (1 / y) * x y) :
  ∃ C : ℝ, ∀ y ∈ Set.Ioi 0, x y = C * y := by
  sorry





theorem theorem_573951_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) (C : Finset (Fin n))
  (hm : m > 0)
  (h : ∀ i : Fin m, (Finset.univ.val.map (A i)) = (C.val.map (A i))) :
  C = Finset.univ := by
  sorry



theorem theorem_573894_problem
  (n : ℕ)
  (f : ℕ → ℝ)
  (x : ℕ → ℝ)
  (k : ℝ)
  (hf_nonneg : ∀ i, i ≤ n → 0 ≤ f i)
  (hf_sum : ∑ i in Finset.range (n + 1), f i = 1)
  (hk : 0 ≤ k ∧ k ≤ 1)
  (S : Finset ℕ)
  (hS_def : S = (Finset.range (n + 1)).filter (fun j => ∑ i in Finset.range (j + 1), f i ≤ k))
  (hS_nonempty : S.Nonempty)
  (j_star : ℕ)
  (hj_star : j_star = S.max' hS_nonempty) :
  (∑ i in Finset.range (j_star + 1), f i ≤ k) ∧
  (j_star < n → ∑ i in Finset.range (j_star + 2), f i > k) := by
  sorry







theorem theorem_574806_problem (X : Type*) [TopologicalSpace X]
  [RegularSpace X] [SecondCountableTopology X] :
  NormalSpace X := by
  sorry













theorem theorem_575076_problem 
  (n : ℕ) (hn : Odd n) (x y : ℝ)
  (P₁ : ℝ := ∑ k in Finset.range ((n - 1) / 2 + 1), ((Nat.choose ((n + 1) / 2) k) : ℝ) * (x ^ 2 - y) ^ k * x ^ (n - 2 * k - 1))
  (P₂ : ℝ := ∑ k in Finset.range ((n - 1) / 2 + 1), ((Nat.choose ((n + 1) / 2) k) : ℝ) * (y ^ 2 - x) ^ k * y ^ (n - 2 * k - 1)) :
  ∃ e f : ℝ, 
    x ^ n - e = n * (x * y - 1) * P₁ ∧ 
    y ^ n - f = n * (x * y - 1) * P₂ := by
  sorry



theorem theorem_575170_problem
  {Ω : Type*}
  (T S : Ω → ℝ)
  (hT : ∀ ω, 0 ≤ T ω)
  (hS : ∀ ω, 0 ≤ S ω)
  (h_cond : ∀ t : ℝ, 0 ≤ t → ∃ f : ℝ → ℝ, ∀ ω, (if S ω ≤ t then (1 : ℝ) else 0) = f (min (T ω) t)) :
  ∀ ω₁ ω₂, S ω₁ < T ω₁ → S ω₂ < T ω₂ → S ω₁ = S ω₂ := by
  sorry







theorem theorem_575104_problem
  (F L : Type*) [Field F] [Field L] [Algebra F L]
  (E K : IntermediateField F L)
  (h_comp : E ⊔ K = ⊤)
  (h_solv : IsSolvable (E ≃ₐ[F] E)) :
  IsSolvable (L ≃ₐ[K] L) := by
  sorry





theorem theorem_575915_problem
  {K : Type*} [Field K]
  {L : Type*} [LieRing L] [LieAlgebra K L]
  (Roots : Type*)
  (simple : Set Roots)
  (h : Roots → ℕ)
  (x y : Roots → L)
  (σ : L ≃ₗ[K] L)
  (h_simple : ∀ α ∈ simple, σ (x α) = - y α)
  (h_structure : ∀ γ : Roots, γ ∉ simple →
    ∃ α β : Roots, h α < h γ ∧ h β < h γ ∧
    ∃ c : K, x γ = c • ⁅x α, x β⁆ ∧ y γ = - c • ⁅y α, y β⁆) :
  ∀ γ : Roots, γ ∉ simple → σ (x γ) = - y γ := by
  sorry



theorem theorem_575683_problem
  {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (h_connected : G.Connected)
  (h_deg_nonzero : ∀ v, G.degree v ≠ 0)
  (h_deg_even : ∀ v, Even (G.degree v)) :
  ∃ (v : V) (w : G.Walk v v), w.IsEulerian := by
  sorry









theorem theorem_576052_problem
  (c : ℝ)
  (u : ℝ → ℝ → ℝ)
  (u₀ : ℝ → ℝ)
  (h_diff_t : ∀ x, Differentiable ℝ (fun t ↦ u t x))
  (h_diff_x : ∀ t, Differentiable ℝ (fun x ↦ u t x))
  (h_pde : ∀ t x, deriv (fun t ↦ u t x) t + c * deriv (fun x ↦ u t x) x = 0)
  (h_init : ∀ x, u 0 x = u₀ x) :
  ∀ t x, u t x = u₀ (x - c * t) := by
  sorry

theorem theorem_576333_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : Type*} [Fintype n] [DecidableEq n]
  (T : V →ₗ[K] V)
  (γ α β δ : Basis n K V) :
  LinearMap.toMatrix γ δ T =
    (Basis.toMatrix δ β)⁻¹ * LinearMap.toMatrix α β T * Basis.toMatrix γ α := by
  sorry



























theorem theorem_576497_problem
  (S T : Type*)
  [Fintype S]
  (P : (S × T) → (S × T) → ℝ)
  (h_dep : ∃ q : S → S → ℝ, ∀ (s1 s2 : S) (t1 t2 : T), P (s1, t1) (s2, t2) = q s1 s2) :
  ∀ (s1 s2 : S) (t1 t2 t3 t4 : T), P (s1, t1) (s2, t2) = P (s1, t3) (s2, t4) := by
  sorry

theorem theorem_576967_problem
  {X : Type*} [MetricSpace X]
  (x_seq : ℕ → X)
  (x : X)
  (nk : ℕ → ℕ)
  (hnk : StrictMono nk)
  (h : ∀ ε > 0, ∃ N₁, ∀ k ≥ N₁, dist (x_seq (nk k)) x < ε / 2) :
  Filter.Tendsto (x_seq ∘ nk) Filter.atTop (nhds x) := by
  sorry









theorem theorem_576930_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ) (x : E) (hf : ContDiff ℝ 2 f)
  (v : E) (hv : ‖v‖ = 1) :
  ∃ c : ℝ, c ≥ 0 ∧ iteratedFDeriv ℝ 2 f x ![v, v] ≥ -c := by
  sorry







theorem theorem_577029_problem
  (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (L : Type*) [LieRing L] [LieAlgebra ℂ L]
  (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V)
  (n : ℕ)
  (v : Basis (Fin n) ℂ V)
  (X : L) :
  ∃! A : Matrix (Fin n) (Fin n) ℂ,
    ∀ i : Fin n, ρ X (v i) = ∑ j : Fin n, A j i • v j := by
  sorry

theorem theorem_576681_problem (r : ℝ)
  (B4 : Set (Fin 4 → ℝ)) (hB4 : B4 = { x | ∑ i, (x i)^2 ≤ r^2 })
  (D2 : Set (Fin 2 → ℝ)) (hD2 : D2 = { x | ∑ i, (x i)^2 ≤ r^2 }) :
  Nonempty (↥B4 ≃ₜ ↥D2 × ↥D2) := by
  sorry

theorem theorem_577663_problem {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (Γ : Set (Submodule F V))
  (h_closed : ∀ α β, α ∈ Γ → β ∈ Γ → α + β ∈ Γ) :
  ∀ α β, α ∈ Γ → β ∈ Γ → α + β ∈ Γ := by
  sorry









theorem theorem_569330_problem
  {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (D : R → M)
  (h_add : ∀ a b : R, D (a + b) = D a + D b)
  (h_leibniz : ∀ a b : R, D (a * b) = a • D b + b • D a)
  (n : ℕ)
  (a : Fin n → R) :
  D (∏ i, a i) = ∑ i, (∏ j in Finset.univ.erase i, a j) • D (a i) := by
  sorry

theorem theorem_577718_problem (δ : ℝ) (hδ : 0 < δ) :
  Set.Icc (-1) 1 ⊆ g '' (Set.Ioo 0 δ) := by
  sorry







theorem theorem_577595_problem
  (Sentence : Type)
  [Primcodable Sentence]
  (g : Sentence ≃ ℤ)
  (hg : Computable g)
  (hg_symm : Computable g.symm)
  (V : Set Sentence)
  (N : Set ℤ)
  (hN : N = g '' V)
  (h_N_not_rec : ¬ ComputablePred N) :
  ¬ ComputablePred V := by
  sorry

