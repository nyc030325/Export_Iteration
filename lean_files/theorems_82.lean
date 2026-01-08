import Mathlib
import Mathlib.Tactic



theorem theorem_441962_problem 
  (k_t k_x k_y k_z : ℝ) 
  (x_t x_x x_y x_z : ℝ) :
  let k : Fin 4 → ℝ := ![k_t, k_x, k_y, k_z]
  let x : Fin 4 → ℝ := ![x_t, x_x, x_y, x_z]
  let g : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![-1, 1, 1, 1]
  ∑ i, ∑ j, g i j * x i * k j = -k_t * x_t + k_x * x_x + k_y * x_y + k_z * x_z := by
  sorry





theorem theorem_441907_problem {n : ℕ} {F : Type*} [Field F]
  (A B : Matrix (Fin n) (Fin n) F)
  (hA : ∀ i j, i > j → A i j = 0)
  (hB : ∀ i j, i > j → B i j = 0) :
  ∀ i j, i ≥ j → (A * B - B * A) i j = 0 := by
  sorry













theorem theorem_442310_problem 
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (f : V) (S : Set V)
  (g₀ : V) (hg₀ : g₀ ∈ S)
  (h : ∀ g_seq : ℕ → V, (∀ n, g_seq n ∈ S) → ∀ n, ‖f - g₀‖ ≤ ‖f - g_seq n‖ + ‖g_seq n - g₀‖) :
  ‖f - g₀‖ ≤ sInf ((fun g => ‖f - g‖) '' S) := by
  sorry





theorem theorem_442503_problem
  (n : ℕ)
  (M K : Matrix (Fin n) (Fin n) ℝ)
  (hM_symm : M.IsSymm)
  (hM_pos : M.PosDef)
  (hK_symm : K.IsSymm)
  (M_half : Matrix (Fin n) (Fin n) ℝ)
  (hM_half_symm : M_half.IsSymm)
  (hM_half_pos : M_half.PosDef)
  (hM_half_sq : M_half ^ 2 = M)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : A = M_half⁻¹ * K * M_half⁻¹) :
  A.IsSymm := by
  sorry



theorem theorem_442905_problem
  (n : ℕ)
  (x : Fin n → (Fin n → ℝ))
  (β : Fin n → ℕ → ℝ)
  (y : ℕ → (Fin n → ℝ))
  (h_def : ∀ m, y m = ∑ i, (β i m) • (x i))
  (h_bound : ∀ i, ∃ M, ∀ m, |β i m| ≤ M) :
  ∃ (φ : ℕ → ℕ) (L : Fin n → ℝ), StrictMono φ ∧ Filter.Tendsto (y ∘ φ) Filter.atTop (nhds L) := by
  sorry

theorem theorem_443033_problem (S P : Matrix (Fin 3) (Fin 3) ℝ)
  (hS : S.rank = 1)
  (hP : P.rank = 1) :
  (Matrix.of (fun i => Sum.elim (S i) (P i))).rank ≤ 2 := by
  sorry





theorem theorem_443119_problem (n : ℕ) (v : Fin n → ℝ) (x : Fin n → ℝ)
  (hn : 0 < n)
  (hx : x = fun i => if i.val = 0 then 1 else 0) :
  ∃ M : Matrix (Fin n) (Fin n) ℝ, Matrix.mulVec M x = v := by
  sorry











theorem theorem_443760_problem
  (n : ℕ)
  (P : Matrix (Fin n) (Fin n) ℝ)
  (t : Matrix (Fin n) (Fin 1) ℝ)
  (h_inv : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) - P))
  (h_denom : 1 + (t.transpose * ((1 : Matrix (Fin n) (Fin n) ℝ) - P)⁻¹ * (P * t)) 0 0 ≠ 0) :
  ((1 : Matrix (Fin n) (Fin n) ℝ) - P + P * t * t.transpose)⁻¹ =
    ((1 : Matrix (Fin n) (Fin n) ℝ) - P)⁻¹ -
    (1 + (t.transpose * ((1 : Matrix (Fin n) (Fin n) ℝ) - P)⁻¹ * (P * t)) 0 0)⁻¹ •
    (((1 : Matrix (Fin n) (Fin n) ℝ) - P)⁻¹ * (P * t) * t.transpose * ((1 : Matrix (Fin n) (Fin n) ℝ) - P)⁻¹) := by
  sorry

















theorem theorem_443865_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (X Z : H →L[𝕜] H) (ψ : H) (x z : 𝕜)
  (hψ : ψ ≠ 0)
  (hx : x ≠ 0)
  (hz : z ≠ 0)
  (hX : X ψ = x • ψ)
  (hZ : Z ψ = z • ψ) :
  (1 / 2 : 𝕜) * (inner ψ ((X * Z) ψ) - inner ψ ((Z * X) ψ)) = 0 := by
  sorry









theorem theorem_444466_problem
  (F : Type*) [Field F]
  (V : Type*) [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (W : Submodule F V)
  (h : FiniteDimensional.finrank F W = FiniteDimensional.finrank F V) :
  W = ⊤ := by
  sorry

theorem theorem_444722_problem
  {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [ContinuousAdd X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  (A B : Set X)
  (hA_nonempty : A.Nonempty)
  (hB_nonempty : B.Nonempty)
  (h_disj : Disjoint A B)
  (hA_convex : Convex ℝ A)
  (hB_convex : Convex ℝ B)
  (hA_compact : IsCompact A)
  (hB_closed : IsClosed B) :
  ∃ (f : X →L[ℝ] ℝ) (r : ℝ), (∀ a ∈ A, f a > r) ∧ (∀ b ∈ B, f b ≤ r) := by
  sorry



theorem theorem_444972_problem (d N : ℕ)
  (x : Fin N → Fin d → ℝ)
  (y : Fin N → ℝ)
  (hy : ∀ i, y i = 0 ∨ y i = 1)
  (C0 C1 : ℝ)
  (hC0 : 0 < C0)
  (hC1 : 0 < C1)
  (h : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
  (h_def : ∀ w xi, h w xi = 1 / (1 + Real.exp (- Matrix.dotProduct w xi)))
  (J : (Fin d → ℝ) → ℝ)
  (J_def : ∀ w, J w = ∏ i : Fin N, (h w (x i)) ^ ((C1 / C0) * y i) * (1 - h w (x i)) ^ ((C0 / C1) * (1 - y i)))
  (w_star : Fin d → ℝ)
  (h_opt : IsMaxOn J Set.univ w_star) :
  IsMaxOn J Set.univ w_star := by
  sorry

theorem theorem_444611_problem
  (D : Set (ℝ → ℝ))
  (A : (ℝ → ℝ) → (ℝ → ℝ))
  (hD : ∀ f ∈ D, f 0 = 0 ∧ f Real.pi = 0)
  (f : ℝ → ℝ)
  (hf : f ∈ D)
  (c : ℝ)
  (hAf : ∀ x, A f x = c) :
  A f ∈ D → c = 0 := by
  sorry

theorem theorem_444440_problem
  (n : ℕ)
  (K : Type*) [Field K]
  (q : K) (hq_inv : q - q⁻¹ ≠ 0)
  (q_half : K) (hq_half : q_half ^ 2 = q)
  (V : Type*) [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]
  (v : Basis (Fin (n + 1)) K V)
  (E F : Module.End K V)
  (hE : IsNilpotent E)
  (hF : IsNilpotent F) :
  let weight (k : Fin (n + 1)) : ℤ := (n : ℤ) - 2 * (k : ℤ)
  let vv := Basis.tensorProduct v v
  let diag_op := vv.constr K (fun (ij : Fin (n + 1) × Fin (n + 1)) ↦
    (q_half ^ (weight ij.1 * weight ij.2)) • vv ij)
  let q_num (k : ℕ) : K := (q ^ k - (q⁻¹) ^ k) / (q - q⁻¹)
  let q_fact (k : ℕ) : K := ∏ i in Finset.range k, q_num (i + 1)
  let X := ((q - q⁻¹) ^ 2)⁻¹ • TensorProduct.map E F
  let exp_op := ∑ k in Finset.range ((n + 1) * (n + 1) + 1),
    (q ^ (Nat.choose k 2) * (q_fact k)⁻¹) • (X ^ k)
  let R := diag_op * exp_op
  LinearMap.det R = 1 := by
  sorry



theorem theorem_444935_problem
  (K : Set ℝ) (hK : IsCompact K)
  (A : Type*) (hA : Nonempty A)
  (f : A → K → ℝ)
  (h_pointwise : ∀ (x : K) (ε : ℝ), 0 < ε → ∃ δ > 0, ∀ (y : K) (α : A),
    dist y x < δ → dist (f α y) (f α x) < ε) :
  ∀ (ε : ℝ), 0 < ε → ∃ δ > 0, ∀ (x y : K) (α : A),
    dist x y < δ → dist (f α x) (f α y) < ε := by
  sorry

theorem theorem_445110_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  [FiniteDimensional ℝ V]
  (P : V →ₗ[ℝ] V)
  (k : ℕ)
  (hk_odd : Odd k)
  (h_proj : (P ^ k) ^ 2 = P ^ k) :
  P ^ 2 = P := by
  sorry



theorem theorem_445292_problem
  (K : Type*) [Field K]
  (E : Type*) [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
  (f : E →ₗ[K] E)
  (h : ∃ N : ℕ, FiniteDimensional K (LinearMap.ker (f ^ N))) :
  ∀ n : ℕ, 1 ≤ n → FiniteDimensional K (LinearMap.ker (f ^ n)) := by
  sorry

theorem theorem_445054_problem
  (m : ℕ)
  (alpha : Fin m → Fin m → ℤ)
  (t : Fin m → ℂ)
  (ht : ∀ j, t j ≠ 0)
  (w : Fin m → ℂ)
  (supp : Set (Fin m))
  (h_supp : supp = { i | w i ≠ 0 })
  (h_cond : ∀ i ∈ supp, (∏ j, (t j) ^ (alpha i j)) * w i = 0) :
  w = 0 := by
  sorry

theorem theorem_445431_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (W₁ W₂ : Submodule F V) :
  (W₁ ⊔ W₂).dualAnnihilator = W₁.dualAnnihilator ⊓ W₂.dualAnnihilator := by
  sorry



theorem theorem_445287_problem (n : ℕ)
  (A B X Y Q_B R_B Q_x R_x : Matrix (Fin n) (Fin n) ℝ)
  (h1 : B = Q_B * R_B)
  (h2 : X.transpose = Q_x * R_x)
  (h3 : Q_B.transpose * Q_B = 1)
  (h4 : Q_x.transpose * Q_x = 1)
  (h5 : IsUnit R_B)
  (h6 : IsUnit R_x)
  (h7 : B * A * X = Y) :
  A = R_B⁻¹ * Q_B.transpose * Y * Q_x * (R_x.transpose)⁻¹ := by
  sorry





theorem theorem_445643_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (u_plus v_plus u_minus v_minus : Matrix n (Fin 1) ℂ)
  (h : u_plus * u_plus.conjTranspose + v_plus * v_plus.conjTranspose + 
       u_minus * u_minus.conjTranspose + v_minus * v_minus.conjTranspose = 1) :
  let A : Matrix n (Fin 4) ℂ := Matrix.of (fun i j => 
    (![u_plus, v_plus, u_minus, v_minus] j) i 0)
  A * A.conjTranspose = 1 := by
  sorry



















theorem theorem_445921_problem
  {n K : Type*} [Fintype n] [Fintype K] [DecidableEq n] [DecidableEq K]
  (A : Matrix n n ℝ) (U : Matrix n K ℝ) (V : Matrix K n ℝ) (C : Matrix K K ℝ)
  (B : Matrix n n ℝ)
  [Invertible A]
  [Invertible C]
  (hC_diag : ∀ i j, i ≠ j → C i j = 0)
  (hB : B = A + U * C * V)
  (h_inv : Invertible (C⁻¹ + V * A⁻¹ * U)) :
  B⁻¹ = A⁻¹ - A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ := by
  sorry



theorem theorem_446022_problem
  (d eta e q2 E2 r theta a b c q1 E1 upsilon epsilon m gamma1 gamma2 n : ℝ)
  (he : e ≠ 0) (hb : b ≠ 0) :
  ∃ α β γ : ℝ, ∀ x y P : ℝ,
    (d * x - eta - e * P - q2 * E2 = 0) →
    (r - theta * P - a * x - b * y - c * P - q1 * E1 = 0) →
    (upsilon + epsilon * x * y * (1 - m) - gamma1 * x * P - gamma2 * y * P - n * P = 0) →
    α * x^2 + β * x + γ = 0 := by
  sorry

theorem theorem_446164_problem
  {I J : Type*} [Fintype I] [Fintype J]
  (x : J → ℝ) (A : I → J → ℝ) :
  sInf { v : ℝ | ∃ (yp ym : I → J → ℝ),
    (∀ i j, yp i j - ym i j = x j - A i j) ∧
    (∀ i j, 0 ≤ yp i j) ∧
    (∀ i j, 0 ≤ ym i j) ∧
    v = ∑ i, ∑ j, (yp i j + ym i j) } =
  sInf { v : ℝ | ∃ (y : I → J → ℝ),
    (∀ i j, -y i j ≤ x j - A i j ∧ x j - A i j ≤ y i j) ∧
    (∀ i j, 0 ≤ y i j) ∧
    v = ∑ i, ∑ j, y i j } := by
  sorry





theorem theorem_446388_problem (a11 a12 a22 b11 b12 b22 φ : ℝ)
  (A : Matrix (Fin 2) (Fin 2) ℝ)
  (B : Matrix (Fin 2) (Fin 2) ℝ)
  (hA : A = !![a11, a12; a12, a22])
  (hB : B = !![b11, b12; b12, b22])
  (R : Matrix (Fin 2) (Fin 2) ℝ)
  (hR : R = !![Real.cos φ, -Real.sin φ; Real.sin φ, Real.cos φ])
  (h_rot : B = R.transpose * A * R)
  (h_denom1 : a11 - a22 ≠ 0)
  (h_denom2 : Real.cos (2 * φ) ≠ 0) :
  Real.tan (2 * φ) = (2 * (a12 - b12 / Real.cos (2 * φ))) / (a11 - a22) := by
  sorry



theorem theorem_446632_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  (x_n : ℕ → X) (x y : X)
  (h_strong : Filter.Tendsto x_n Filter.atTop (nhds x))
  (h_weak : ∀ f : NormedSpace.Dual 𝕜 X, Filter.Tendsto (fun n ↦ f (x_n n)) Filter.atTop (nhds (f y))) :
  x = y := by
  sorry

theorem theorem_446303_problem (X Y : Type*)
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  (L : X →ₗ[ℝ] Y)
  (h : ∀ φ : Y →L[ℝ] ℝ, Continuous (φ ∘ L)) :
  Continuous L := by
  sorry



theorem theorem_446695_problem
  (r g w U : ℝ)
  (h_w : 0 < w)
  (utility : ℝ → ℝ → ℝ)
  (h_utility : ∀ (x y : ℝ), utility x y = w * x + y) :
  utility r g = U ↔ w * r + g = U := by
  sorry

theorem theorem_446381_problem
  (T : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
  (B : Basis (Fin 3) ℝ (Fin 3 → ℝ))
  (C : Basis (Fin 2) ℝ (Fin 2 → ℝ))
  (PB : Matrix (Fin 3) (Fin 3) ℝ)
  (hPB : PB = B.toMatrix (Pi.basisFun ℝ (Fin 3)))
  (PC : Matrix (Fin 2) (Fin 2) ℝ)
  (hPC : PC = C.toMatrix (Pi.basisFun ℝ (Fin 2)))
  (T_CB : Matrix (Fin 2) (Fin 3) ℝ)
  (hT_CB : T_CB = LinearMap.toMatrix B C T)
  (T_std : Matrix (Fin 2) (Fin 3) ℝ)
  (hT_std : T_std = LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 2)) T) :
  T_CB = PC⁻¹ * T_std * PB := by
  sorry





theorem theorem_447048_problem (g : ℂ → ℂ) (p : ℂ) (s : ℝ)
  (hs : 0 < s)
  (h_holo : ∃ U, IsOpen U ∧ Metric.closedBall p s ⊆ U ∧ DifferentiableOn ℂ g U) :
  Complex.abs (deriv g p) ≤ (1 / s) * sSup ((Complex.abs ∘ g) '' Metric.sphere p s) := by
  sorry





theorem theorem_447195_problem (N : ℕ) (hN : N > 0) (k : ℤ) (x : ℤ → ℂ)
  (hx : ∀ n : ℤ, x (n + N) = x n) :
  ∑ n in Finset.range N, x (-(n : ℤ)) * Complex.exp (Complex.I * 2 * Real.pi * k * n / N) =
  ∑ n in Finset.range N, x n * Complex.exp (-Complex.I * 2 * Real.pi * k * n / N) := by
  sorry

theorem theorem_447256_problem (X : Type*) [Finite X]
  (f : ℕ → X → ℝ) (g : X → ℝ)
  (h_pt : ∀ x, Filter.Tendsto (fun n ↦ f n x) Filter.atTop (nhds (g x))) :
  TendstoUniformly f g Filter.atTop := by
  sorry

theorem theorem_447316_problem
  (R : Type*) [CommRing R]
  (M : Type*) [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]
  (n : ℕ)
  (hM_rank : FiniteDimensional.finrank R M = n)
  (φ : M →ₗ[R] M)
  (h_exists : ∃ N : Submodule R M,
    Module.Free R N ∧
    Module.Finite R N ∧
    FiniteDimensional.finrank R N < n ∧
    LinearMap.range φ ≤ N) :
  LinearMap.det φ = 0 := by
  sorry







theorem theorem_447872_problem (a b c d e f x_p y_p : ℝ)
  (h1 : a * x_p + b * y_p + c = 0)
  (h2 : d * x_p + e * y_p + f = 0) :
  (a * x_p + b * y_p + c)^2 + (d * x_p + e * y_p + f)^2 = 0 := by
  sorry



theorem theorem_448068_problem (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] (v₁ v₂ : V)
  (h : LinearIndependent F ![v₁, v₂]) :
  ∃ T : V →ₗ[F] F, T v₁ ≠ T v₂ := by
  sorry



theorem theorem_447735_problem
  (V : Type*) [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
  (I1 I2 : InnerProductSpace.Core ℝ V)
  (h_distinct : I1 ≠ I2) :
  ∃ (W : Submodule ℝ V) (v : V) (p1 p2 : V),
    (p1 ∈ W ∧ ∀ w ∈ W, I1.inner (v - p1) w = 0) ∧
    (p2 ∈ W ∧ ∀ w ∈ W, I2.inner (v - p2) w = 0) ∧
    p1 ≠ p2 := by
  sorry









