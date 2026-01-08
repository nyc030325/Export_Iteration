import Mathlib
import Mathlib.Tactic

theorem theorem_174238_problem (n : ℕ) (hn : n > 0) (a : ℕ → ℂ)
  (A : Matrix (Fin n) (Fin n) ℂ)
  (hA : ∀ i j, A i j = a (((i : ℕ) + j) % n))
  (f : ℂ → ℂ)
  (hf : ∀ ω, f ω = ∑ k in Finset.range n, a k * ω ^ k)
  (ζ : ℂ)
  (hζ : ζ = Complex.exp (Real.pi * Complex.I / (n : ℂ))) :
  A.det = ∏ k in Finset.range n, f (ζ ^ (2 * k + 1)) := by
  sorry











theorem theorem_174171_problem
  {F : Type*} [Field F]
  {n : ℕ}
  {V : Type*} [AddCommGroup V] [Module F V]
  (e : Basis (Fin n) F V)
  (x : V)
  (y : Module.Dual F V) :
  y x = ∑ i : Fin n, (e.repr x i) * (e.dualBasis.repr y i) := by
  sorry

theorem theorem_174467_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (g : LinearMap.BilinForm ℝ V)
  (A : Basis n ℝ V)
  (B : Basis n ℝ V)
  (x y : V) :
  g x y = ∑ i, ∑ j, (g (A i) (A j)) * (A.repr x i) * (A.repr y j) ∧
  g x y = ∑ μ, ∑ ν, (g (B μ) (B ν)) * (B.repr x μ) * (B.repr y ν) := by
  sorry

theorem theorem_174930_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
  (h_le : m ≤ n)
  (h_id : ∀ (i : Fin m) (j : Fin m), A i (Fin.castLE h_le j) = if i = j then 1 else 0)
  (h_entries : ∀ (i : Fin m) (j : Fin n), m ≤ (j : ℕ) → A i j = 1 ∨ A i j = -1)
  (h_nonsing : ∀ (f : Fin m → Fin n), Function.Injective f →
    (A.submatrix id f).det = 1 ∨ (A.submatrix id f).det = -1) :
  n ≤ m + 1 := by
  sorry



theorem theorem_174864_problem
  {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (e : Basis (Fin n) K V)
  (T : V →ₗ[K] V)
  (vol : AlternatingMap K V K (Fin n))
  (hvol : vol e ≠ 0)
  (b : Basis (Fin n) K V) :
  vol (T ∘ b) / vol b = vol (T ∘ e) / vol e := by
  sorry

theorem theorem_174932_problem
  {K : Type*} [Field K]
  {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  (R : Matrix n n K) (Q : Matrix m m K) (W : Matrix m n K)
  (hR : Invertible R) (hQ : Invertible Q)
  (h1 : Invertible (W * R * W.transpose + Q))
  (h2 : Invertible (W.transpose * Q⁻¹ * W + R⁻¹)) :
  R * W.transpose * (W * R * W.transpose + Q)⁻¹ =
  (W.transpose * Q⁻¹ * W + R⁻¹)⁻¹ * W.transpose * Q⁻¹ := by
  sorry

theorem theorem_175252_problem
  (x w v : EuclideanSpace ℝ (Fin 2))
  (h_neq : w ≠ v)
  (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))
  (hL : L = affineSpan ℝ {w, v}) :
  x ∈ L.directionᗮ ↔ inner x (w - v) = (0 : ℝ) := by
  sorry



theorem theorem_174692_problem
  (R : Type*) [NormedRing R] [NormedAlgebra ℂ R] [StarRing R] [CompleteSpace R]
  (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (ι : R → H) (hι_dense : DenseRange ι)
  (L : R → H →L[ℂ] H)
  (R_op : R → H →L[ℂ] H)
  (hL_def : ∀ (x r : R), L x (ι r) = ι (x * r))
  (hR_def : ∀ (x r : R), R_op x (ι r) = ι (r * x)) :
  let Commutant (S : Set (H →L[ℂ] H)) := {T : H →L[ℂ] H | ∀ A ∈ S, T ∘L A = A ∘L T}
  Commutant {T | ∃ x, T = R_op x} = {T | ∃ x, T = L x} := by
  sorry





theorem theorem_175686_problem
  {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (F : V →ₗ[ℝ] W) :
  sSup {y | ∃ x : V, ‖x‖ ≤ 1 ∧ y = ‖F x‖} = sSup {y | ∃ x : V, ‖x‖ = 1 ∧ y = ‖F x‖} := by
  sorry





theorem theorem_175533_problem
  {K : Type*} [Field K] [Infinite K]
  {V : Type*} [AddCommGroup V] [Module K V]
  {n s : ℕ}
  (β : Basis (Fin n) K V)
  (α : Fin s → V)
  (h_indep : LinearIndependent K α)
  (h_sn : s ≤ n) :
  ∃ φ : V →ₗ[K] K, ∀ i, φ (α i) ≠ 0 := by
  sorry











theorem theorem_175857_problem (a b c : ℝ) 
  (A : Matrix (Fin 3) (Fin 3) ℝ)
  (hA : A = !![a, b, c; c, a, b; b, c, a]) :
  A.det = (a + b + c) * (a^2 + b^2 + c^2 - a * b - b * c - c * a) := by
  sorry

theorem theorem_175463_problem :
  let A : Matrix (Fin 4) (Fin 4) (Polynomial ℚ) := 
    !![7, X, 0, -X;
       0, X - 3, 0, 3;
       0, 0, X - 4, 0;
       X - 6, -1, 0, X + 1]
  let D : Matrix (Fin 4) (Fin 4) (Polynomial ℚ) := 
    !![1, 0, 0, 0;
       0, 1, 0, 0;
       0, 0, 1, 0;
       0, 0, 0, X^4 - 3*X^3 - 11*X^2 + 7*X + 84]
  ∃ (P Q : Matrix (Fin 4) (Fin 4) (Polynomial ℚ)),
    IsUnit P.det ∧ IsUnit Q.det ∧ 
    P * A * Q = D ∧
    (D 0 0 ∣ D 1 1) ∧ (D 1 1 ∣ D 2 2) ∧ (D 2 2 ∣ D 3 3) := by
  sorry







theorem theorem_176141_problem (a n m : ℝ) :
  ∃! ABC : ℝ × ℝ × ℝ,
    let A := ABC.1
    let B := ABC.2.1
    let C := ABC.2.2
    let Q := fun (r : ℝ) => -a * r^2 + r * (1 - a * n) + n - a * n^2 - 2 * m
    ∀ r : ℝ, r ≠ n → Q r ≠ 0 →
      (r^2) / ((r - n) * Q r) = A / (r - n) + (B * r + C) / Q r := by
  sorry





theorem theorem_176178_problem
  {F V : Type*} [NormedField F] [NormedAddCommGroup V] [NormedSpace F V]
  (A B : V) :
  |‖A‖ - ‖B‖| ≤ ‖A - B‖ := by
  sorry



theorem theorem_176157_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (e : Basis (Fin 4) K V)
  (F F' : Submodule K V)
  (hF : F = Submodule.span K {e 0, e 1})
  (hF' : F' = Submodule.span K {e 2, e 3}) :
  F ⊓ F' = ⊥ := by
  sorry





theorem theorem_176495_problem (x y x' y' theta : ℝ) :
  ∃! p : ℝ × ℝ, 
    let x₀ := p.1
    let y₀ := p.2
    x' = x₀ + x * Real.cos theta - y * Real.sin theta ∧
    y' = y₀ + x * Real.sin theta + y * Real.cos theta := by
  sorry

theorem theorem_176392_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (M : Submodule ℝ X)
  (h : ∀ (x_n : ℕ → X) (x : X),
    (∀ n, x_n n ∈ M) →
    Filter.Tendsto x_n Filter.atTop (nhds x) →
    x ≠ 0 →
    (Filter.Tendsto (fun n ↦ ‖x_n n‖⁻¹ • x_n n) Filter.atTop (nhds (‖x‖⁻¹ • x)) ∧
     (‖x‖⁻¹ • x) ∈ M ∧ ‖‖x‖⁻¹ • x‖ ≤ 1)) :
  IsClosed (M : Set X) := by
  sorry







theorem theorem_176838_problem 
  (F : Type*) [Field F]
  (X : Type*) [AddCommGroup X] [Module F X]
  (Y : Submodule F X)
  (Φ : X → F)
  (h : ∃ y ∈ Y, ∃ x : X, x ∉ Y ∧ Φ y ≠ 0 ∧ (x + y) ∉ Y ∧ Φ (x + y) ≠ Φ x + Φ y) :
  ¬ IsLinearMap F Φ := by
  sorry







theorem theorem_176988_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {ι : Type*} [Finite ι]
  (W : ι → Subspace ℂ V)
  (hW : ∀ i, W i ≠ ⊤) :
  IsConnected (Set.univ \ ⋃ i, (W i : Set V)) := by
  sorry

theorem theorem_177115_problem
  (X : Type*) [MetricSpace X] [CompactSpace X]
  (A : Subalgebra ℝ (ContinuousMap X ℝ))
  (h1 : ∀ (c : ℝ), (ContinuousMap.C c) ∈ A)
  (h2 : ∀ (x y : X), x ≠ y → ∃ f ∈ A, f x ≠ f y) :
  Dense (A : Set (ContinuousMap X ℝ)) := by
  sorry

theorem theorem_176590_problem
  (F : Type*) [Field F]
  (V : Type*) [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (x y : V) :
  (x + y) ⊗ₜ[F] (x + y) - x ⊗ₜ[F] x - y ⊗ₜ[F] y = x ⊗ₜ[F] y + y ⊗ₜ[F] x := by
  sorry





theorem theorem_177217_problem
  {K : Type*} [Field K]
  {G : Type*} [Group G]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (ρ : G →* (V ≃ₗ[K] V))
  (ρ_star : G → Module.Dual K V →ₗ[K] Module.Dual K V)
  (h_rho_star : ∀ g, ρ_star g = LinearMap.dualMap (ρ g).symm.toLinearMap) :
  ∀ (g : G) (v : V) (v_star : Module.Dual K V),
    (ρ_star g v_star) (ρ g v) = v_star v := by
  sorry





theorem theorem_177427_problem :
  ∃ (n : ℕ) (A B : Fin n → ℤ), A ≠ B ∧ ∑ i, A i = ∑ i, B i := by
  sorry





theorem theorem_177306_problem
  (α β : ℝ)
  (f g : ℕ → ℝ)
  (hβ : β ≠ 0)
  (hf : ∀ x, Summable (fun n => f n * (α + β * x) ^ n))
  (hg : ∀ x, Summable (fun n => g n * x ^ n))
  (h_eq : ∀ x, (∑' n, f n * (α + β * x) ^ n) = (∑' n, g n * x ^ n)) :
  ∀ i, g i = ∑' j, (if j ≥ i then (Nat.choose j i : ℝ) * α ^ (j - i) * β ^ i else 0) * f j := by
  sorry









theorem theorem_178145_problem (n : ℕ) (x y : ℕ → ℂ) :
  ∑ i in Finset.Icc 1 (n - 1), ∑ j in Finset.Icc (i + 1) n, Complex.abs (x i * star (y j) - x j * star (y i)) ^ 2 =
  ∑ p in (Finset.product (Finset.Icc 1 n) (Finset.Icc 1 n)).filter (fun p => p.1 < p.2),
    Complex.abs (x p.1 * star (y p.2) - x p.2 * star (y p.1)) ^ 2 := by
  sorry



theorem theorem_178160_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (A : E →L[ℝ] E)
  (x : ℝ → E)
  (f : E → ℝ)
  (hx : Differentiable ℝ x)
  (hf : Differentiable ℝ f)
  (h_ode : ∀ t, deriv x t = A (x t))
  (h_jac : ∀ v, fderiv ℝ f v (A v) = f v) :
  ∀ t, f (x t) = Real.exp t * f (x 0) := by
  sorry

theorem theorem_178019_problem (n : ℕ) (a : Fin n → ℤ) (hn : 2 ≤ n)
  (h_gcd : Finset.univ.gcd a = 1) :
  ∃ A : Matrix (Fin n) (Fin n) ℤ, A ⟨0, by linarith⟩ = a ∧ A.det = 1 := by
  sorry



theorem theorem_178240_problem (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (v : Basis (Fin n) ℝ (Fin n → ℝ)) :
  Submodule.span ℝ (Set.range (fun i => Matrix.mulVec A (Pi.basisFun ℝ (Fin n) i))) =
  Submodule.span ℝ (Set.range (fun i => Matrix.mulVec A (v i))) := by
  sorry

theorem theorem_178196_problem (n d : ℕ) (u : Fin n → EuclideanSpace ℝ (Fin d))
  (h : ∀ i, ‖u i‖ ≤ 1) :
  ∃ ε : Fin n → ℝ, (∀ i, ε i = -1 ∨ ε i = 1) ∧ 
  ∀ j : Fin d, |(∑ i, ε i • u i) j| ≤ Real.sqrt n := by
  sorry











theorem theorem_178685_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
  (T : V →ₗ[F] W) :
  (LinearMap.dualMap (LinearMap.dualMap T)).comp (Module.Dual.eval F V) =
  (Module.Dual.eval F W).comp T := by
  sorry



theorem theorem_179003_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (w : E) (w₀ : ℝ) (r : ℝ)
  (h_w_ne_zero : w ≠ 0)
  (h_r_def : inner w (r • (‖w‖⁻¹ • w)) + w₀ = 0) :
  r = -w₀ / ‖w‖ := by
  sorry

theorem theorem_178678_problem (a : ℕ → ℕ → ℝ)
  (h_lower : ∀ i j, i < j → a i j = 0)
  (h_diag : ∀ i, a i i = 1) :
  ∃! b : ℕ → ℕ → ℝ,
    (∀ i j, i < j → b i j = 0) ∧
    (∀ i j, ∑ k in Finset.range (i + 1), a i k * b k j = if i = j then 1 else 0) := by
  sorry

theorem theorem_179052_problem {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (A : V →ₗ[F] V) (h : A ∘ₗ A = A) :
  IsCompl (LinearMap.range A) (LinearMap.ker A) := by
  sorry



theorem theorem_178953_problem (N : ℝ) (hN : N > 0) (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1)
  (C : ℝ) (hC : C = 4 * (N - 1) / N)
  (term : ℝ → ℝ) (hterm : term = fun x ↦ 1 - C * x + C * x^2)
  (eigenvalues : ℝ → Set ℝ)
  (heig : eigenvalues = fun x ↦ {1, (1 / 2) * (1 + Real.sqrt (term x)), (1 / 2) * (1 - Real.sqrt (term x))}) :
  eigenvalues s = eigenvalues (1 - s) := by
  sorry

theorem theorem_178892_problem
  (x y : ℝ → ℝ)
  (α : ℝ → ℝ × ℝ)
  (h_def : ∀ t, α t = (x t, y t))
  (h_smooth_x : ContDiff ℝ ⊤ x)
  (h_smooth_y : ContDiff ℝ ⊤ y)
  (h_inj : Function.Injective α)
  (h_deriv_ne : ∀ t, deriv α t ≠ 0)
  (h_fderiv_inj : ∀ t, Function.Injective (fderiv ℝ α t)) :
  Embedding α := by
  sorry

theorem theorem_179268_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (T : Module.End K V)
  (cs : List K)
  (α : V)
  (h_comm : ∀ c1 ∈ cs, ∀ c2 ∈ cs, Commute (T - c1 • (1 : Module.End K V)) (T - c2 • (1 : Module.End K V)))
  (h_eigen : ∃ c ∈ cs, T α = c • α) :
  (cs.map (fun c => T - c • (1 : Module.End K V))).prod α = 0 := by
  sorry







theorem theorem_179824_problem
  {n : ℕ} [NeZero n]
  {K : Type*} [Field K]
  (M : Matrix (Fin n) (Fin n) K)
  [Invertible M]
  (v : Fin n → K)
  (h : M.transpose.mulVec v = Pi.single 0 1) :
  v = (⅟M) 0 := by
  sorry





theorem theorem_179455_problem
  (F : Type*) [Field F]
  (V : Type*) [AddCommGroup V] [Module F V]
  (h_dim : FiniteDimensional.finrank F V = 1)
  (θ : F) (hθ : θ ≠ 0)
  (T : V ≃ₗ[F] V)
  (h_rep : ∃ v₀ : V, v₀ ≠ 0 ∧ T v₀ = θ • v₀) :
  ∀ v : V, T v = θ • v := by
  sorry

theorem theorem_179717_problem (A B C x y z A' B' C' M : ℝ)
  (hA' : A' = (A + B) / 2)
  (hB' : B' = (B + C) / 2)
  (hC' : C' = (A + C) / 2)
  (hM : M = x * A + y * B + z * C) :
  M = (x + y - z) * A' + (y - x + z) * B' + (x - y + z) * C' := by
  sorry

theorem theorem_180025_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA_symm : A.IsSymm)
  (hB_symm : B.IsSymm)
  (hA_pos : A.PosSemidef)
  (hB_pos : B.PosSemidef)
  (h_comm : A * B = B * A)
  (h_diff_pos : (A - B).PosSemidef) :
  (A ^ 2 - B ^ 2).PosSemidef := by
  sorry







theorem theorem_179954_problem (a b c : Fin 3 → ℝ) :
  crossProduct a (crossProduct b c) = (Matrix.dotProduct a c) • b - (Matrix.dotProduct a b) • c := by
  sorry





