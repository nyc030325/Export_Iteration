import Mathlib
import Mathlib.Tactic







theorem theorem_85814_problem 
  {K V W : Type*} [Field K] 
  [AddCommGroup V] [Module K V] 
  [AddCommGroup W] [Module K W]
  (A B : V →ₗ[K] W) 
  (h1 : LinearMap.range A ≤ LinearMap.range B)
  (h2 : Module.rank K (Submodule.map (LinearMap.range A).mkQ (LinearMap.range B)) = 0) :
  LinearMap.range B = LinearMap.range A := by
  sorry

theorem theorem_85459_problem (n : ℕ)
  (f : ZeroAtInftyContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ g : ZeroAtInftyContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ,
    ContDiff ℝ ⊤ g ∧ HasCompactSupport g ∧ ‖f - g‖ < ε := by
  sorry

theorem theorem_85945_problem (A : Matrix (Fin 3) (Fin 3) ℝ) :
  ∃! p : Matrix (Fin 3) (Fin 3) ℝ × Matrix (Fin 3) (Fin 3) ℝ,
    A = p.1 + p.2 ∧
    (∀ i j : Fin 3, i ≤ j → p.1 i j = 0) ∧
    (∀ i j : Fin 3, i > j → p.2 i j = 0) := by
  sorry







theorem theorem_86293_problem
  (K : Type*) [Field K]
  (tau : K →+* K) (h_tau_inv : ∀ x, tau (tau x) = x)
  (K0 : Subfield K)
  (h_K0_fixed : (K0 : Set K) = {x | tau x = x})
  [LinearOrderedField K0]
  (h_euclid : ∀ x : K0, 0 ≤ x → ∃ y : K0, y^2 = x)
  (V : Type*) [AddCommGroup V] [Module K V]
  (h : V → V → K)
  (h_lin : ∀ (a : K) (x y : V), h (a • x) y = a * h x y)
  (h_add : ∀ (x y z : V), h (x + y) z = h x z + h y z)
  (h_herm : ∀ (x y : V), h y x = tau (h x y))
  (h_pos : ∀ (x : V), x ≠ 0 → ∃ k : K0, (k : K) = h x x ∧ 0 < k) :
  ∃ N : V → K0,
    (∀ x, (N x : K)^2 = h x x) ∧
    (∀ x, 0 ≤ N x) ∧
    (∀ x, N x = 0 ↔ x = 0) ∧
    (∀ (c : K) (x : V), ∃ (mod_c : K0), (mod_c : K)^2 = c * tau c ∧ 0 ≤ mod_c ∧ N (c • x) = mod_c * N x) ∧
    (∀ x y, N (x + y) ≤ N x + N y) := by
  sorry

theorem theorem_86333_problem
  {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : E → F)
  (h_hom : ∀ (c : ℝ) (x : E), f (c • x) = c • f x)
  (h_diff : DifferentiableAt ℝ f 0) :
  IsLinearMap ℝ f := by
  sorry

theorem theorem_86466_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (A B C : Matrix n n ℝ)
  (φ : Matrix n n ℝ → Matrix n n ℝ)
  (hφ : ∀ X, φ X = B * X * B - A * X * C)
  (M_φ : Matrix (n × n) (n × n) ℝ)
  (hM_φ : M_φ = B.transpose.kronecker B - C.transpose.kronecker A)
  (h_psd : (M_φ + M_φ.transpose).PosSemidef) :
  ∀ X : Matrix n n ℝ, X.IsSymm → (φ X * X.transpose).trace ≥ 0 := by
  sorry



theorem theorem_86622_problem (n : ℕ) (x : Fin n → ℝ)
  (h : Real.sqrt (∑ i, |x i|^2) = 1) :
  ∑ j, ∑ k, |x j| * |x k| ≤ (n : ℝ) := by
  sorry



theorem theorem_87143_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
  Matrix.dotProduct x (Matrix.mulVec (A.transpose * A) x) = 
  Matrix.dotProduct (Matrix.mulVec A x) (Matrix.mulVec A x) := by
  sorry







theorem theorem_87248_problem (n : ℕ) (x : Fin n → ℝ) (k : ℝ) (hk : 2 ≤ k) :
  (∑ i, |x i| ^ 2) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2 - 1 / k) * (∑ i, |x i| ^ k) ^ (1 / k) := by
  sorry



theorem theorem_87376_problem
  (n : ℕ)
  (p k : ℕ)
  (hp : p.Prime)
  (hk : k ≥ 1)
  (a b : Fin n → ZMod (p ^ k))
  (A B P : Matrix (Fin n) (Fin n) (ZMod (p ^ k)))
  (hA : A = Matrix.diagonal a)
  (hB : B = Matrix.diagonal b)
  (hP : IsUnit P.det)
  (h_conj : P * A * P⁻¹ = B) :
  ∃ σ : Equiv.Perm (Fin n), ∀ i, b i = a (σ i) := by
  sorry



theorem theorem_87654_problem
  (m n : ℕ)
  (K : Type*) [Field K]
  (P : Matrix (Fin m) (Fin n) K)
  (h_rank : P.rank = n) :
  ∃ C : Matrix (Fin n) (Fin m) K, C * P = 1 := by
  sorry

theorem theorem_87458_problem (n : ℕ) (a : Fin n → ℂ) (b : ℂ)
  (hn : 0 < n)
  (h_im : ∀ i, 0 < (a i).im)
  (h_sum : ∑ i, (1 / (b - a i)).im = 0) :
  0 < b.im := by
  sorry

theorem theorem_87987_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (p₁ p₂ p₃ : V) :
  {x : V | ∃ u v : ℝ, u ∈ Set.Icc 0 1 ∧ v ∈ Set.Icc 0 1 ∧
    x = (1 - u) • p₁ + u • ((1 - v) • p₂ + v • p₃)} =
  convexHull ℝ {p₁, p₂, p₃} := by
  sorry





theorem theorem_87614_problem
  (n m : ℕ)
  (X : Matrix (Fin n) (Fin m) ℝ)
  (w : Matrix (Fin m) (Fin 1) ℝ)
  (hw : w ≠ 0)
  (z : Matrix (Fin m) (Fin 1) ℝ)
  (hz : z = (Real.sqrt ((w.transpose * w) 0 0))⁻¹ • w) :
  (w.transpose * X.transpose * X * w) 0 0 / (w.transpose * w) 0 0 =
  (z.transpose * X.transpose * X * z) 0 0 := by
  sorry

theorem theorem_87702_problem
  (K : Type*) [Field K]
  (L : Type*) [AddCommGroup L] [Module K L]
  (M : Type*) [AddCommGroup M] [Module K M]
  (φ : L →+ M) :
  IsLinearMap K φ ↔ ∀ (k : K) (l : L), φ (k • l) = k • φ l := by
  sorry





theorem theorem_87807_problem
  {R : Type*} [CommRing R]
  {m1 m2 r1 r2 : Type*}
  [Fintype m1] [Fintype m2] [Fintype r1] [Fintype r2]
  [DecidableEq m1] [DecidableEq m2] [DecidableEq r1] [DecidableEq r2]
  (e1 : Matrix r1 m1 R) (e2 : Matrix r2 m2 R)
  (M11 : Matrix m1 m1 R) (M12 : Matrix m1 m2 R)
  (M21 : Matrix m2 m1 R) (M22 : Matrix m2 m2 R) :
  let E := Matrix.fromBlocks e1 0 0 e2
  let M := Matrix.fromBlocks M11 M12 M21 M22
  let ET := Matrix.fromBlocks e1.transpose 0 0 e2.transpose
  E * M * ET = Matrix.fromBlocks
    (e1 * M11 * e1.transpose) (e1 * M12 * e2.transpose)
    (e2 * M21 * e1.transpose) (e2 * M22 * e2.transpose) := by
  sorry







theorem theorem_88176_problem (f : ℂ → ℝ)
  (h1 : ∀ (r : ℝ) (θ : ℝ), 0 < r → f (↑r * Complex.exp (Complex.I * ↑θ)) = r * f (Complex.exp (Complex.I * ↑θ)))
  (h2 : ∀ (z1 z2 : ℂ), z1.re ≤ z2.re → z1.im ≤ z2.im → f z1 ≤ f z2)
  (B : ℂ) :
  ContinuousAt f B := by
  sorry





theorem theorem_88674_problem
  (N D M : ℕ)
  (hN : 0 < N)
  (hM_ge : 1 ≤ M)
  (hM_le : M ≤ D)
  (x : Fin N → EuclideanSpace ℝ (Fin D))
  (u : Fin D → EuclideanSpace ℝ (Fin D))
  (hu : Orthonormal ℝ u)
  (z : Fin N → Fin M → ℝ) :
  let x_tilde (b : Fin D → ℝ) (n : Fin N) : EuclideanSpace ℝ (Fin D) :=
    (∑ i : Fin M, z n i • u (Fin.castLE hM_le i)) +
    (∑ i : Fin D, if i ≥ M then b i • u i else 0)
  let J (b : Fin D → ℝ) : ℝ := (1 / N : ℝ) * ∑ n : Fin N, ‖x n - x_tilde b n‖^2
  let x_mean : EuclideanSpace ℝ (Fin D) := (1 / N : ℝ) • ∑ n : Fin N, x n
  ∀ b : Fin D → ℝ, IsMinOn J Set.univ b →
    ∀ i : Fin D, i ≥ M → b i = inner x_mean (u i) := by
  sorry



theorem theorem_88719_problem {n : ℕ} {R : Type*} [CommRing R]
  (b U : Matrix (Fin n) (Fin n) R)
  (i : Fin n)
  (hb : ∀ j k, b j k = -b k j)
  (hU : ∀ j k, U j k = -U k j) :
  ∑ j, b i j * U i j = ∑ j, b j i * U j i := by
  sorry

theorem theorem_88310_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {p : ℕ}
  (u_vec : Fin p → V)
  (h_indep : LinearIndependent K u_vec)
  (u : V)
  (h_cond : ∀ i : Fin p, u ∈ Submodule.span K (u_vec '' {j | j ≠ i})) :
  u = 0 := by
  sorry











theorem theorem_88807_problem (n : ℕ) (u v : Matrix (Fin n) (Fin 1) ℝ) :
  let I : Matrix (Fin n) (Fin n) ℝ := 1
  let one : Matrix (Fin 1) (Fin 1) ℝ := 1
  (Matrix.fromBlocks I 0 v.transpose one) *
  (Matrix.fromBlocks I u 0 one) *
  (Matrix.fromBlocks (I + u * v.transpose) 0 0 one) *
  (Matrix.fromBlocks I 0 (-v.transpose) one) *
  (Matrix.fromBlocks I (-u) 0 one) =
  Matrix.fromBlocks I 0 0 (one + v.transpose * u) := by
  sorry



theorem theorem_89253_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [Field K]
  (A B S : Matrix n n K)
  (hS : Invertible S)
  (h : A = S⁻¹ * B * S) :
  ∀ μ : K, Module.End.HasEigenvalue (Matrix.toLin' A) μ ↔ Module.End.HasEigenvalue (Matrix.toLin' B) μ := by
  sorry

theorem theorem_89274_problem {V : Type*} [AddCommGroup V] [Module ℝ V]
  (e : Basis (Fin 3) ℝ V)
  (T : V →ₗ[ℝ] V)
  (h1 : T (e 0) = -2 • e 0 - 2 • e 1 + 7 • e 2)
  (h2 : T (e 1) = 12 • e 0 + 8 • e 1 - 13 • e 2)
  (h3 : T (e 2) = 4 • e 2) :
  LinearMap.toMatrix e e T = !![-2, 12, 0; -2, 8, 0; 7, -13, 4] := by
  sorry





















theorem theorem_88984_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  (n : ℕ)
  (v : Basis (Fin n) K V)
  (σ : Equiv.Perm (Fin n)) :
  (∏ i, v.dualBasis (σ i) (v i)) ≠ 0 ↔ σ = 1 := by
  sorry



theorem theorem_89037_problem
  (n t j : ℕ)
  (A : ℕ → ℕ → ℝ)
  (W : ℕ → ℕ → ℝ)
  (f : ℝ → ℝ)
  (k1 k2 : ℝ)
  (h_update : A t j = f (k1 * (∑ i in (Finset.range (n + 1)).filter (λ x => x ≠ j), A (t - 1) i * W i j) + k2 * A (t - 1) j)) :
  A t j = f (k1 * (∑ i in (Finset.range (n + 1)).filter (λ x => x ≠ j), A (t - 1) i * W i j) + k2 * A (t - 1) j) := by
  sorry

theorem theorem_88912_problem (n : ℕ) (a b : Fin n → ℝ) (c : ℝ)
  (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : 0 < c) :
  sInf {v | ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧ (∑ i, x i = c) ∧ v = ∑ i, (a i * b i) / (x i + a i)} =
  sInf {v | ∃ (x t : Fin n → ℝ), (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ t i) ∧ (∑ i, x i = c) ∧
    (∀ i, a i * b i ≤ t i * (x i + a i)) ∧ v = ∑ i, t i} := by
  sorry

theorem theorem_88821_problem
  (n : ℕ)
  (R : Type*) [CommRing R]
  (p S G : Matrix (Fin n) (Fin 1) R)
  (ones : Matrix (Fin n) (Fin 1) R)
  (h_ones : ones = fun _ _ => 1)
  (h_p : p.transpose * ones = 1)
  (h_G : G = ((1 : Matrix (Fin n) (Fin n) R) - ones * p.transpose) * S) :
  p.transpose * G = 0 := by
  sorry

theorem theorem_89810_problem (a b : ℝ) (f : ℝ → ℝ) (M : ℝ)
  (hab : a ≤ b)
  (hbdd : BddAbove (f '' Set.Icc a b))
  (hM : M = sSup (f '' Set.Icc a b))
  (ε : ℝ) (hε : 0 < ε) :
  ∃ c ∈ Set.Icc a b, f c > M - ε := by
  sorry









theorem theorem_89581_problem (k : Type*) [Field k] (n : ℕ)
  (V : Type*) [AddCommGroup V] [Module k V]
  (B : Basis (Fin n) k V) :
  ∃ Φ : LieEquiv k (Module.End k V) (Matrix (Fin n) (Fin n) k),
    ∀ f, Φ f = LinearMap.toMatrix B B f := by
  sorry

theorem theorem_89728_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (n : ℕ)
  (h_dim : FiniteDimensional.finrank F V = n)
  (v : Fin (n + 1) → V) :
  ¬ LinearIndependent F v := by
  sorry



















theorem theorem_90432_problem
  (n : ℕ)
  (k : ℕ)
  (x : Fin n → ℝ)
  (h_k_ge_1 : 1 ≤ k)
  (h_k_le_n : k ≤ n) :
  sSup {s : ℝ | ∃ I : Finset (Fin n), I.card = k ∧ s = ∑ i in I, x i} =
  sSup {v : ℝ | ∃ w : Fin n → ℝ, (∑ i, w i = (k : ℝ)) ∧ (∀ i, 0 ≤ w i ∧ w i ≤ 1) ∧ v = ∑ i, w i * x i} := by
  sorry



















theorem theorem_91412_problem (A B C D E F α : ℝ) :
  ∃ B' C' D' E' F' : ℝ, ∀ x' y' : ℝ,
    let x := x' * Real.cos α - y' * Real.sin α
    let y := x' * Real.sin α + y' * Real.cos α
    A * x^2 + B * x * y + C * y^2 + D * x + E * y + F = 
    (A * (Real.cos α)^2 + B * Real.sin α * Real.cos α + C * (Real.sin α)^2) * x'^2 + 
    B' * x' * y' + C' * y'^2 + D' * x' + E' * y' + F' := by
  sorry

theorem theorem_91399_problem
  (f : (Fin 2 → ℝ) → (Fin 2 → ℝ))
  (hf : ContDiff ℝ ⊤ f)
  (p : Fin 2 → ℝ)
  (u v : Fin 2 → ℝ) :
  let X := fun (a : Fin 2 → ℝ) => f a 0
  let T := fun (a : Fin 2 → ℝ) => f a 1
  let dX := fderiv ℝ X p
  let dT := fderiv ℝ T p
  let df := fderiv ℝ f p
  dX u * dT v - dX v * dT u = (LinearMap.det df.toLinearMap) * (u 0 * v 1 - u 1 * v 0) := by
  sorry



theorem theorem_91021_problem
  (yR yI HR HI sR sI nR nI : ℝ)
  (y H s n : ℂ)
  (hy : y = Complex.mk yR yI)
  (hH : H = Complex.mk HR HI)
  (hs : s = Complex.mk sR sI)
  (hn : n = Complex.mk nR nI)
  (h_eq : y = H * s + n) :
  !![yR; yI] = !![HR, -HI; HI, HR] * !![sR; sI] + !![nR; nI] := by
  sorry



theorem theorem_90723_problem
  (F : Type*) [Field F]
  (E₁ E₂ E₁' E₂' : Type*)
  [AddCommGroup E₁] [Module F E₁]
  [AddCommGroup E₂] [Module F E₂]
  [AddCommGroup E₁'] [Module F E₁']
  [AddCommGroup E₂'] [Module F E₂'] :
  Nonempty ((E₁ × E₂ →ₗ[F] E₁' × E₂') ≃ₗ[F]
    ((E₁ →ₗ[F] E₁') × (E₂ →ₗ[F] E₁') × (E₁ →ₗ[F] E₂') × (E₂ →ₗ[F] E₂'))) := by
  sorry



