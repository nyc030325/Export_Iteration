import Mathlib
import Mathlib.Tactic







theorem theorem_80437_problem
  (n : ℕ)
  (M : ℝ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : ∀ i j, 0 ≤ A i j ∧ A i j ≤ M)
  (t : ℕ)
  (ht : t > 0) :
  ∀ i j, (A ^ t) i j ≤ (n : ℝ) ^ (t - 1) * M ^ t := by
  sorry

theorem theorem_80926_problem (n : ℕ) (T : Matrix (Fin n) (Fin n) ℝ)
  (h : ∃ R : Matrix (Fin n) (Fin n) ℝ, R ^ 2 = T) :
  0 ≤ T.det := by
  sorry





theorem theorem_81273_problem
  (T : ℝ)
  (hT : 0 < T)
  (TestFunction : Type)
  (Distribution : Type)
  (pairing : Distribution → TestFunction → ℝ)
  (test_deriv : TestFunction → TestFunction)
  (dist_deriv : Distribution → Distribution)
  (h_def : ∀ (v : Distribution) (φ : TestFunction),
    pairing (dist_deriv v) φ = - pairing v (test_deriv φ))
  (u : Distribution)
  (E : Distribution → Distribution)
  (φ : TestFunction) :
  pairing (dist_deriv (E u)) φ = - pairing (E u) (test_deriv φ) := by
  sorry



theorem theorem_81314_problem
  (K : Set ℝ)
  (hK : IsCompact K)
  (gn : ℕ → K → ℝ)
  (g : K → ℝ)
  (h_cont : ∀ n, Continuous (gn n))
  (h_unif : TendstoUniformly gn g Filter.atTop) :
  Continuous g := by
  sorry



theorem theorem_81084_problem (A B : ℂ) (n : ℕ) :
  (Complex.abs (A - B) ^ (2 * n) : ℂ) =
  (∑ k in Finset.range (n + 1), (n.choose k : ℂ) * A ^ k * (-B) ^ (n - k)) *
  (∑ k in Finset.range (n + 1), (n.choose k : ℂ) * (star A) ^ k * (- star B) ^ (n - k)) := by
  sorry

theorem theorem_81101_problem (n m : ℕ)
  (S : Matrix (Fin n) (Fin m) ℝ)
  (D : Matrix (Fin n) (Fin n) ℝ)
  (hS : S.transpose * S = 1)
  (hD : D.PosSemidef) :
  (S.transpose * D * (1 - S * S.transpose) * D * S).PosSemidef := by
  sorry



theorem theorem_81592_problem (X : Type*) [Nonempty X]
  (f : ℕ → X → ℝ)
  (h_cauchy : ∀ x : X, CauchySeq (fun n ↦ f n x)) :
  ∃ g : X → ℝ, ∀ x : X, Filter.Tendsto (fun n ↦ f n x) Filter.atTop (nhds (g x)) := by
  sorry



theorem theorem_81550_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : ∀ i j, i > j → A i j = 0) :
  let A' := Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)
  ∀ i j : Sum (Fin n) (Fin 1), i > j → A' i j = 0 := by
  sorry

theorem theorem_81604_problem (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
  (h : x ≠ 0) :
  gradient (fun v => 1 / ‖v‖) x = - (1 / ‖x‖ ^ 3) • x := by
  sorry







theorem theorem_81467_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (R : Submodule ℝ V)
  (f₀ : V)
  (h_not_in : f₀ ∉ R)
  -- T corresponds to the continuous linear map defined on M = span(R ∪ {f₀})
  -- We define T on the span directly
  (T : (Submodule.span ℝ (insert f₀ (R : Set V))) →L[ℝ] ℝ)
  -- The definition T(f + a f₀) = a implies T is 0 on R and 1 on f₀
  (hT_R : ∀ (f : V) (hf : f ∈ R), T ⟨f, Submodule.subset_span (Set.mem_insert_of_mem f₀ hf)⟩ = 0)
  (hT_f₀ : T ⟨f₀, Submodule.subset_span (Set.mem_insert f₀ (R : Set V))⟩ = 1) :
  ∃ φ : V →L[ℝ] ℝ, (∀ f ∈ R, φ f = 0) ∧ φ f₀ = 1 := by
  sorry

theorem theorem_81670_problem
  (n : ℕ)
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  -- P_A and P_R represent the distributions of the random variables A and R
  (P_A : PMF (Matrix (Fin n) (Fin n) F))
  (P_R : PMF (Matrix (Fin n) (Fin n) F))
  -- R is a random matrix uniformly distributed over F (M_n(F))
  (hR_unif : P_R = PMF.uniformOfFintype (Matrix (Fin n) (Fin n) F))
  -- A is invertible (meaning A takes values in invertible matrices with probability 1)
  (hA_inv : ∀ a, P_A a ≠ 0 → IsUnit a) :
  -- The joint distribution of (A, RA) assuming A and R are independent
  let P_joint := P_A.bind (fun a => P_R.map (fun r => (a, r * a)))
  -- The marginal distribution of the ciphertext RA
  let P_RA := P_joint.map Prod.snd
  -- The security condition Pr[A | RA] = Pr[A] is equivalent to independence:
  -- P(A=a, RA=y) = P(A=a) * P(RA=y)
  ∀ a y, P_joint (a, y) = P_A a * P_RA y := by
  sorry

theorem theorem_81846_problem
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix m n ℝ)
  (d : ℝ)
  (k : ℕ)
  (hk : k > 0)
  (hd : d ≠ 0) :
  let M := (d⁻¹) • Matrix.fromBlocks 0 A.transpose A 0
  M ^ (2 * k) = (d ^ (-(2 * k : ℤ))) • Matrix.fromBlocks ((A.transpose * A) ^ k) 0 0 ((A * A.transpose) ^ k) := by
  sorry



theorem theorem_81736_problem {F : Type*} [Field F] :
  let e : ℕ → ℕ → F := fun n k => if k = n then 1 else 0
  let S : Set (ℕ → F) := { v | ∃ n, v = e n }
  (Submodule.span F S : Set (ℕ → F)) = { a | { n | a n ≠ 0 }.Finite } := by
  sorry











theorem theorem_82376_problem
  (α : ℕ → ℚ)
  (hα : Function.Bijective α) :
  LinearIndependent ℝ (fun (x : ℝ) (i : ℕ) => if (α i : ℝ) < x then (0 : ℝ) else 1) := by
  sorry





theorem theorem_82081_problem :
  let x : ℝ → ℝ := fun t ↦ 1
  let y : ℝ → ℝ := Real.cos
  let z : ℝ → ℝ := Real.sin
  let basis : Fin 3 → (ℝ → ℝ) := ![x, y, z]
  let f : (ℝ → ℝ) → (ℝ → ℝ) := fun g t ↦ g (t + Real.pi / 4)
  let M : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0;
                                         0, Real.sqrt 2 / 2, -Real.sqrt 2 / 2;
                                         0, Real.sqrt 2 / 2, Real.sqrt 2 / 2]
  ∀ j : Fin 3, f (basis j) = ∑ i : Fin 3, M i j • basis i := by
  sorry



theorem theorem_82474_problem (n : ℕ) (hn : n > 0)
  (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
  ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧ ‖A‖ = ‖A x‖ := by
  sorry









theorem theorem_82733_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (T : X →L[𝕜] X)
  (c : ℝ)
  (hc : c > 0)
  (h : ∀ x : X, c * ‖x‖ ≤ ‖T x‖) :
  LinearMap.ker T = ⊥ := by
  sorry

theorem theorem_82710_problem
  (F : Type*) [Field F]
  (V : Type*) [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (U : Submodule F V) :
  Submodule.map (Module.Dual.eval F V) U = U.dualAnnihilator.dualAnnihilator := by
  sorry









theorem theorem_82828_problem
  (v1 v2 c1 c2 : Fin 2 → ZMod 26)
  (h_no_sol : ¬ ∃ (H : Matrix (Fin 2) (Fin 2) (ZMod 26)), Matrix.mulVec H v1 = c1 ∧ Matrix.mulVec H v2 = c2) :
  ∀ (H : Matrix (Fin 2) (Fin 2) (ZMod 26)), ¬ (Matrix.mulVec H v1 = c1 ∧ Matrix.mulVec H v2 = c2) := by
  sorry

theorem theorem_82848_problem
  (d n m : ℕ)
  (h : Fin d → ℝ)
  (h_nonzero : ∀ i, h i ≠ 0)
  (T_orig : (Fin n → Fin d) → (Fin m → Fin d) → ℝ)
  (T_phys : (Fin n → Fin d) → (Fin m → Fin d) → ℝ)
  -- The physical components are defined by normalizing the basis vectors.
  -- This introduces a factor of h for each contravariant index and 1/h for each covariant index.
  (h_phys_def : ∀ (I : Fin n → Fin d) (J : Fin m → Fin d),
    T_phys I J = T_orig I J * ((∏ k, h (I k)) * (∏ k, (1 / h (J k))))) :
  -- Prove the transformation formula stated in the problem
  ∀ (I : Fin n → Fin d) (J : Fin m → Fin d),
    T_phys I J = ((∏ k, h (I k)) / (∏ k, h (J k))) * T_orig I J := by
  sorry







theorem theorem_83157_problem
  -- Context: A ringed topos with enough points, abstracted to its points and stalks
  (Pt : Type*) [TopologicalSpace Pt]
  (Stalk : Pt → Type*) [∀ p, CommRing (Stalk p)]
  -- Condition: The stalk rings have connected prime spectra
  (h_connected : ∀ p : Pt, ConnectedSpace (PrimeSpectrum (Stalk p)))
  -- The groups involved in the sequence (abstracted as types)
  (Pic_O_Mod : Type*) [AddCommGroup Pic_O_Mod]
  (Pic_D_O_Mod : Type*) [AddCommGroup Pic_D_O_Mod] :
  -- Conclusion: Existence of a split short exact sequence
  ∃ (f : Pic_O_Mod →+ Pic_D_O_Mod)
    (g : Pic_D_O_Mod →+ LocallyConstant Pt ℤ)
    (s : LocallyConstant Pt ℤ →+ Pic_D_O_Mod),
    Function.Injective f ∧
    Function.Surjective g ∧
    (∀ y, g y = 0 ↔ ∃ x, f x = y) ∧
    g.comp s = AddMonoidHom.id _ := by
  sorry

theorem theorem_82834_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (x : ℝ → X)
  (hx : Differentiable ℝ x)
  (t : ℝ)
  (ht : DifferentiableAt ℝ (fun u => ‖x u‖) t) :
  |deriv (fun u => ‖x u‖) t| ≤ ‖deriv x t‖ := by
  sorry









theorem theorem_83675_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ) (p : E) (hf : DifferentiableAt ℝ f p) :
  ∃! u : E, ∀ v : E, fderiv ℝ f p v = inner u v := by
  sorry





theorem theorem_83338_problem
  (R : Type*) [Field R]
  (B : Type*)
  (E₁ E₂ F₁ F₂ : B → Type*)
  [∀ b, AddCommGroup (E₁ b)] [∀ b, Module R (E₁ b)]
  [∀ b, AddCommGroup (E₂ b)] [∀ b, Module R (E₂ b)]
  [∀ b, AddCommGroup (F₁ b)] [∀ b, Module R (F₁ b)]
  [∀ b, AddCommGroup (F₂ b)] [∀ b, Module R (F₂ b)]
  (f₁ : ∀ b, E₁ b →ₗ[R] F₁ b)
  (f₂ : ∀ b, E₂ b →ₗ[R] F₂ b) :
  let whitney_sum_E := fun b ↦ E₁ b × E₂ b
  let whitney_sum_F := fun b ↦ F₁ b × F₂ b
  let induced_map := fun b (x : whitney_sum_E b) ↦ (f₁ b x.1, f₂ b x.2)
  ∀ b, IsLinearMap R (induced_map b) := by
  sorry

theorem theorem_83559_problem
  (n k : ℕ)
  (D : Set (Fin n → ℝ))
  (W : (Fin n → ℝ) → Matrix (Fin k) (Fin k) ℝ)
  (h_det : ∀ x ∈ D, (W x).det = 0)
  (x : Fin n → ℝ)
  (hx : x ∈ D) :
  ∃ c : Fin k → ℝ, c ≠ 0 ∧ Matrix.mulVec (W x) c = 0 := by
  sorry







theorem theorem_83716_problem
  {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]
  {n : ℕ} (e : Basis (Fin n) K V)
  (U : G →* (V ≃ₗ[K] V))
  (D : G → Matrix (Fin n) (Fin n) K)
  (hD : ∀ (g : G) (i : Fin n), U g (e i) = ∑ j, (D g) j i • e j)
  (x : V) (x_coords : Fin n → K)
  (hx : x = ∑ i, x_coords i • e i)
  (g : G) :
  U g x = ∑ j, (∑ i, (D g) j i * x_coords i) • e j := by
  sorry

theorem theorem_83541_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {n : ℕ}
  (b : Basis (Fin n) F V)
  (T : V →ₗ[F] V)
  (h : ∀ k : Fin n, T (b k) ∈ Submodule.span F (b '' {j | j ≤ k})) :
  ∀ i j : Fin n, j < i → (LinearMap.toMatrix b b T) i j = 0 := by
  sorry





theorem theorem_83886_problem
  {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace K X]
  (X₁ X₂ : Submodule K X)
  (h₁ : IsClosed (X₁ : Set X))
  (h₂ : FiniteDimensional K X₂) :
  IsClosed ((X₁ + X₂) : Set X) := by
  sorry

theorem theorem_83230_problem
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (φ : E → F)
  (h_diff : HasFDerivAt φ (0 : E →L[ℝ] F) 0)
  (h_zero : φ 0 = 0) :
  ∀ ε > 0, ∃ δ > 0, ∀ x, ‖x‖ < δ → ‖φ x‖ ≤ ε * ‖x‖ := by
  sorry



theorem theorem_83948_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
  (∏ j : Fin n, ∑ i : Fin n, |A i j|) ≥ 
  ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, |A i (σ i)| := by
  sorry



theorem theorem_84541_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  (h_dim : Module.rank F V ≥ 2)
  (π : V →ₗ[F] V)
  (h_proj : π ^ 2 = π)
  (h_ne_id : π ≠ 1)
  (h_ne_zero : π ≠ 0) :
  ¬ ∃ p : Polynomial F, Polynomial.aeval (1 : V →ₗ[F] V) p = π := by
  sorry

theorem theorem_84307_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (w x : E) (b y r : ℝ)
  (h_w : w ≠ 0)
  (h_y : y = 1 ∨ y = -1)
  (h_dist : inner w (x - (r * y / ‖w‖) • w) + b = 0) :
  r = y * (inner w x + b) / ‖w‖ := by
  sorry

theorem theorem_84013_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  (v : ℝ → V)
  (h_int : IntervalIntegrable v volume 0 1)
  (h_sq_int : IntervalIntegrable (fun t => ‖v t‖ ^ 2) volume 0 1) :
  ‖∫ t in (0:ℝ)..1, v t‖ ^ 2 ≤ ∫ t in (0:ℝ)..1, ‖v t‖ ^ 2 := by
  sorry













theorem theorem_84232_problem
  (K : Type*) [Field K]
  (n d : ℕ)
  (B : (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K))
  (h_nondeg : LinearMap.det B ≠ 0)
  (h_ker : FiniteDimensional.finrank K (LinearMap.ker B) = d + 1) :
  FiniteDimensional.finrank K (LinearMap.ker B) - 1 = d := by
  sorry

theorem theorem_84841_problem {n : ℕ} {R : Type*} [CommRing R]
  (A : Matrix (Fin n.succ) (Fin n.succ) R) (i : Fin n.succ) :
  A.det = ∑ j : Fin n.succ, A i j * (-1 : R) ^ ((i : ℕ) + (j : ℕ)) * (A.submatrix i.succAbove j.succAbove).det := by
  sorry



























theorem theorem_85633_problem
  {K : Type*} [Field K]
  {M : Type*} [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]
  (k l : ℕ)
  (n : Fin l → M)
  (h_dim : FiniteDimensional.finrank K M = k)
  (h_l : k < l) :
  ¬ LinearIndependent K n := by
  sorry

