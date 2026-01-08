import Mathlib
import Mathlib.Tactic

theorem theorem_427012_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {X : Type*}
  (m : ℕ) (hm : (m : ℝ) ≠ 0)
  (y : Fin m → ℝ)
  (x : Fin m → X)
  (eval : X → V →L[ℝ] ℝ)
  (γ : ℝ)
  (f f_bar : V) :
  let J := fun (g : V) ↦ (1 / (m : ℝ)) * (∑ i, (y i - eval (x i) g)^2) + γ * ‖g‖^2;
  HasDerivAt (fun ε : ℝ ↦ J (f + ε • f_bar))
    (- (2 / (m : ℝ)) * (∑ i, (y i - eval (x i) f) * eval (x i) f_bar) + 2 * γ * inner f f_bar) 0 := by
  sorry

theorem theorem_427399_problem
  (n : ℕ)
  (K : Type*) [Field K] [NumberField K]
  (x : Fin n → K)
  (A : Matrix (Fin n) (Fin n) ℚ) :
  let x' := fun i => ∑ j, (algebraMap ℚ K (A i j)) * x j
  let Λ : Matrix (Fin n) (Fin n) ℚ := Matrix.of (fun i j => Algebra.trace ℚ K (x i * x j))
  let Λ' : Matrix (Fin n) (Fin n) ℚ := Matrix.of (fun i j => Algebra.trace ℚ K (x' i * x' j))
  Λ'.det = (A.det) ^ 2 * Λ.det := by
  sorry

theorem theorem_427375_problem
  (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (h_symm : ∀ u v, g u v = g v u)
  (h_pos : ∀ v, v ≠ 0 → g v v > 0)
  (h_def : ∀ v, g v v = 0 ↔ v = 0)
  (W : Submodule ℝ V) (hW : W ≠ ⊥) :
  ∀ (w : W), g (w : V) (w : V) = 0 ↔ w = 0 := by
  sorry







theorem theorem_427598_problem (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) (μ : ℝ) (hμ : 0 < μ) :
  (μ / 2) * ‖x‖^2 + (μ / 2) * ‖y‖^2 - μ * inner y x = (μ / 2) * ‖x - y‖^2 := by
  sorry





theorem theorem_427447_problem (k : ℕ) (z a : Fin k → ℂ)
  (h_distinct : Function.Injective z)
  (h_nonzero : ∀ i, z i ≠ 0)
  (h_eq : ∀ n : ℕ, n < k → ∑ i : Fin k, a i * (z i) ^ n = 0) :
  ∀ i, a i = 0 := by
  sorry







theorem theorem_427999_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (A B : X →L[𝕜] X) :
  ‖A.comp B‖ ≤ ‖A‖ * ‖B‖ := by
  sorry





theorem theorem_427779_problem
  (F : Type*) [Field F]
  (p : ℕ)
  (n : ℕ) (hn : n = p + 1)
  (V : Type*) [AddCommGroup V] [Module F V]
  (β : Basis (Fin n) F V)
  (L : V →ₗ[F] V)
  (A : Matrix (Fin n) (Fin n) F)
  (h : ∀ j : Fin n, L (β j) = ∑ i : Fin n, (A i j) • (β i)) :
  A = LinearMap.toMatrix β β L := by
  sorry







theorem theorem_427679_problem (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  (n : ℕ)
  (h : ∃ s : Finset B, s.card ≤ n ∧ Submodule.span A (s : Set B) = ⊤) :
  ∀ p : PrimeSpectrum A, {q : PrimeSpectrum B | PrimeSpectrum.comap (algebraMap A B) q = p}.Finite ∧
    {q : PrimeSpectrum B | PrimeSpectrum.comap (algebraMap A B) q = p}.ncard ≤ n := by
  sorry

theorem theorem_427232_problem
  {n : ℕ} {K : Type*} [Field K]
  (A D : Matrix (Fin n) (Fin n) K)
  (p : ℕ)
  (S : Finset (Fin n))
  (hS_card : S.card = p)
  (hD : D.IsDiag)
  (hA_sparse : ∀ j ∈ S, ∃! i, A i j ≠ 0)
  (hA_diag : ∀ j ∈ S, A j j ≠ 0) :
  ∀ j ∈ S, Module.End.HasEigenvalue (Matrix.toLin' (A + D)) (A j j + D j j) := by
  sorry



theorem theorem_427742_problem (n : ℕ) (Y Z : Matrix (Fin n) (Fin n) ℂ)
  (hY : Y.det ≠ 0) (hZ : Z ≠ 0) :
  (∀ X : Matrix (Fin n) (Fin n) ℂ, ∃! A : Matrix (Fin n) (Fin n) ℂ,
    Y⁻¹ * A - A * Z = Y⁻¹ * X) ↔
  (∀ μ : ℂ, ¬ (Module.End.HasEigenvalue (Matrix.toLin' Y⁻¹) μ ∧
               Module.End.HasEigenvalue (Matrix.toLin' Z) μ)) := by
  sorry



theorem theorem_428124_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (T : E →ₗ[ℝ] E)
  (x y : E)
  (δ ε : ℝ)
  (hδ : 0 < δ) (hε : 0 < ε)
  (h : Metric.ball y ε ⊆ T '' (Metric.ball x δ))
  (α : ℝ) (hα : 0 < α) :
  Metric.ball (α • y) (α * ε) ⊆ T '' (Metric.ball (α • x) (α * δ)) := by
  sorry

theorem theorem_427877_problem (n : ℕ) :
  let X := { i : ℕ // i ∈ Set.Icc 1 n }
  Nonempty ((X → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) := by
  sorry









theorem theorem_428485_problem (R : Type*) [CommRing R] [Nontrivial R] (m n : ℕ)
  (h : (Fin m → R) ≃ₗ[R] (Fin n → R)) : m = n := by
  sorry



theorem theorem_428253_problem
  (n : ℕ)
  (v : Fin n → ℝ)
  (M : Matrix (Fin n) (Fin n) ℝ)
  (hM : M = Matrix.vecMulVec v v)
  (x : Fin n → ℝ) :
  0 ≤ Matrix.dotProduct x (Matrix.mulVec M x) := by
  sorry







theorem theorem_428173_problem (n : ℕ) (hn : n > 0) :
  ∃ A B C D : ℕ → ℝ, ∀ x : ℝ, x^4 - 1 ≠ 0 →
  1 / (x^4 - 1)^n =
    (∑ k in Finset.Icc 1 n, A k / (x - 1)^k) +
    (∑ k in Finset.Icc 1 n, B k / (x + 1)^k) +
    (∑ k in Finset.Icc 1 n, (C k * x + D k) / (x^2 + 1)^k) := by
  sorry

theorem theorem_428578_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f g : E → ℝ) (c : E)
  (hf : ContDiffAt ℝ 2 f c)
  (hg : ContDiffAt ℝ 2 g c) :
  fderiv ℝ (fderiv ℝ (f * g)) c =
    g c • fderiv ℝ (fderiv ℝ f) c +
    (fderiv ℝ f c).smulRight (fderiv ℝ g c) +
    (fderiv ℝ g c).smulRight (fderiv ℝ f c) +
    f c • fderiv ℝ (fderiv ℝ g) c := by
  sorry







theorem theorem_428637_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (P Q : Matrix n n ℝ)
  (hP : P.IsSymm)
  (hQ : Q.IsSymm)
  (c : ℝ)
  (h_posdef : (P + c • Q).PosDef)
  (c' : ℝ)
  (h_ge : c ≤ c') :
  (P + c' • Q).PosDef := by
  sorry















theorem theorem_429482_problem
  (R : Matrix (Fin 3) (Fin 3) ℝ)
  (h : ∀ (u v w : Fin 3 → ℝ),
    Matrix.dotProduct (crossProduct (Matrix.mulVec R u) (Matrix.mulVec R v)) (Matrix.mulVec R w) =
    Matrix.dotProduct (crossProduct u v) w) :
  Matrix.det R = 1 := by
  sorry

theorem theorem_428890_problem
  (n : ℕ)
  (ι : Type*)
  (p : ι)
  (c : ι → Fin n → ℝ)
  (b : ι → ℝ)
  (S : Set (Fin n → ℝ))
  (hS : S = {x | ∀ i, i ≠ p → Matrix.dotProduct (c i) x ≤ b i})
  (h_max : ∃ m, (∃ x₀ ∈ S, Matrix.dotProduct (c p) x₀ = m) ∧ 
                (∀ x ∈ S, Matrix.dotProduct (c p) x ≤ m) ∧ 
                m ≤ b p) :
  S ⊆ {x | Matrix.dotProduct (c p) x ≤ b p} := by
  sorry

theorem theorem_429185_problem (n : ℕ)
  (one : Fin n → ℝ)
  (h_one : one = fun _ => 1)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (h_A : A = Matrix.vecMulVec one one - 1)
  (x : Fin n → ℝ)
  (hx_ne_zero : x ≠ 0)
  (hx_ortho : Matrix.dotProduct one x = 0) :
  Matrix.dotProduct x (Matrix.mulVec A x) < 0 := by
  sorry











theorem theorem_429946_problem {K : Type*} [Field K] {n : ℕ}
  (A : Matrix (Fin n) (Fin n) K) (r : ℕ) (h : A.rank = r) :
  ∃ (rows : Fin r → Fin n) (cols : Fin r → Fin n), (A.submatrix rows cols).det ≠ 0 := by
  sorry



theorem theorem_430075_problem
  {R : Type*} [CommRing R]
  {m n p q : Type*} [Fintype n] [Fintype p]
  (A : Matrix m n R)
  (B : Matrix n p R)
  (C : Matrix p q R) :
  A * B * C = (C.transpose * B.transpose * A.transpose).transpose := by
  sorry



theorem theorem_430095_problem
  {α : Type*} [Semiring α]
  {l m n : ℕ}
  (R : Matrix (Fin l) (Fin m) α)
  (M : Matrix (Fin m) (Fin n) α)
  (i : Fin l)
  (h : ∀ k : Fin m, R i k = 0) :
  ∀ j : Fin n, (R * M) i j = 0 := by
  sorry









theorem theorem_429897_problem
  {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  (T : Module.End k V) :
  ∃! φ : Polynomial k →+* Module.End k V,
    ∀ p : Polynomial k, φ p = Polynomial.eval₂ (algebraMap k (Module.End k V)) T p := by
  sorry



theorem theorem_430392_problem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (x : V) (h : ∀ (f : V →ₗ[K] K), f x = 0) : x = 0 := by
  sorry

theorem theorem_430490_problem
  {X F ι : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (phi : X → F)
  (kappa : X → X → ℝ)
  (h_kappa : ∀ x z : X, kappa x z = inner (phi x) (phi z))
  (SV : Finset ι)
  (xs : ι → X)
  (ys : ι → ℝ)
  (h_ys : ∀ i ∈ SV, ys i = 1 ∨ ys i = -1)
  (alphas : ι → ℝ)
  (w : F)
  (h_w : w = ∑ i in SV, (alphas i * ys i) • phi (xs i)) :
  ∀ x : X, inner w (phi x) = ∑ i in SV, alphas i * ys i * kappa (xs i) x := by
  sorry



theorem theorem_430102_problem
  (n : ℕ)
  (Dom : Set (Fin n → ℝ))
  (hDom : IsOpen Dom)
  (f : (Fin n → ℝ) → ℝ)
  (hf : DifferentiableOn ℝ f Dom) :
  (∃ c : Fin n → ℝ, c ≠ 0 ∧ ∀ x ∈ Dom, fderivWithin ℝ f Dom x c = 0) ↔
  (∃ c : Fin n → ℝ, c ≠ 0 ∧ ∀ x ∈ Dom, ∀ t : ℝ, x + t • c ∈ Dom → f (x + t • c) = f x) := by
  sorry







theorem theorem_431256_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (f u v : V)
  (h : ∀ t : ℝ, t * B (f - u) v ≤ B (f - u) u) :
  B (f - u) v = 0 := by
  sorry



theorem theorem_431171_problem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (β : E) (t : ℝ) (ht : 0 ≤ t) :
  ‖β‖ ≤ t ↔ ‖β‖^2 ≤ t^2 := by
  sorry

theorem theorem_431197_problem
  (G : Type*) [Group G]
  (k : Type*) [Field k]
  (V : Type*) [AddCommGroup V] [Module k V]
  (F : Type*) [Field F]
  -- G acts on V, inducing an action on F(V) by field automorphisms
  [MulSemiringAction G F]
  (R : Type*) [Ring R]
  -- Embeddings of F and G into the skew group ring R
  (emb_F : F →+* R)
  (emb_G : G → R)
  -- The defining right action/commutation property: g f = (g • f) g
  (h_comm : ∀ (g : G) (f : F), emb_G g * emb_F f = emb_F (g • f) * emb_G g) :
  -- The property to prove
  ∀ (g : G) (f₁ f₂ : F), 
    emb_G g * emb_F (f₁ * f₂) = emb_F (g • f₁) * emb_F (g • f₂) * emb_G g := by
  sorry



theorem theorem_430796_problem (n : ℕ) (hn : 2 ≤ n) :
  let S : Set (Matrix (Fin n) (Fin n) ℂ) := {A | Matrix.det A ≠ 0} ∪ {0}
  ¬ ∃ (V : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)), ↑V = S := by
  sorry





theorem theorem_430769_problem
  (c : Polynomial ℝ)
  (h_even : Even c.natDegree)
  (h_pos : 0 < c.leadingCoeff)
  (h_ge2 : 2 ≤ c.natDegree) :
  Dense {f : ZeroAtInftyContinuousMap ℝ ℝ | ∃ p : Polynomial ℝ, ∀ x, f x = p.eval x * Real.exp (-c.eval x)} := by
  sorry









theorem theorem_431043_problem
  (F : Type*) [Field F] [Fintype F]
  (h_char : ringChar F ≠ 2)
  (P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F)) :
  ∃ n : ℕ, Nonempty (P ≃* QuaternionGroup n) := by
  sorry

theorem theorem_430913_problem (D d : ℕ) (L : (Fin D → ℝ) →ₗ[ℝ] (Fin d → ℝ)) :
  ∃ s : LinearMap.range L →ₗ[ℝ] (Fin D → ℝ), ∀ y : LinearMap.range L, L (s y) = y := by
  sorry





theorem theorem_431819_problem
  (U : Set ℂ)
  (f : ℂ → ℂ)
  (γ : ℝ → ℂ)
  (hU_open : IsOpen U)
  (hU_sc : SimplyConnectedSpace U)
  (hf_holo : DifferentiableOn ℂ f U)
  (hγ_diff : ContDiffOn ℝ 1 γ (Set.Icc 0 1))
  (hγ_img : Set.MapsTo γ (Set.Icc 0 1) U)
  (hγ_closed : γ 0 = γ 1) :
  ∫ t in (0:ℝ)..1, f (γ t) * deriv γ t = 0 := by
  sorry











theorem theorem_431748_problem (n : ℕ) (G : Subgroup (GL (Fin n) ℝ))
  (h_finite : Finite G)
  (h_symm : ∀ A ∈ G, (A : Matrix (Fin n) (Fin n) ℝ).IsSymm)
  (h_diag : ∃ P : GL (Fin n) ℝ, ∀ A ∈ G,
    ((P⁻¹ * (A : GL (Fin n) ℝ) * P) : Matrix (Fin n) (Fin n) ℝ).IsDiag) :
  ∃ f : G →* Multiplicative (Fin n → ZMod 2), Function.Injective f := by
  sorry

