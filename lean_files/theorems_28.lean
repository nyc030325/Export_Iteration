import Mathlib
import Mathlib.Tactic



theorem theorem_148155_problem (n : ℕ) (A : Matrix (Fin 3) (Fin n) ℝ)
  (h : A 0 + A 2 = 2 • A 1) :
  ¬ LinearIndependent ℝ (fun i => A i) := by
  sorry







theorem theorem_148251_problem
  {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
  (T : V →ₗ[F] W)
  (n k : ℕ) (hk : k ≤ n)
  (b : Basis (Fin n) F V)
  (b_ker : Basis (Fin k) F (LinearMap.ker T))
  (h_ker_eq : ∀ i : Fin k, (b_ker i).val = b (Fin.castLE hk i)) :
  LinearIndependent F (fun (j : Fin (n - k)) ↦ T (b (Fin.cast (Nat.add_sub_of_le hk) (Fin.natAdd k j)))) := by
  sorry





theorem theorem_148281_problem (n : ℕ) (J : Matrix (Fin n) (Fin n) ℝ) :
  let b := Pi.basisFun ℝ (Fin n)
  let dy := fun i => ExteriorAlgebra.ι ℝ (b i)
  let dx := fun i => ExteriorAlgebra.ι ℝ (∑ j, J i j • b j)
  (List.finRange n).map dx |>.prod = J.det • ((List.finRange n).map dy |>.prod) := by
  sorry

















theorem theorem_148575_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : Matrix.PosDef (-A)) :
  ∃ L U : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j, i < j → L i j = 0) ∧
    (∀ i, L i i = 1) ∧
    (∀ i j, j < i → U i j = 0) ∧
    A = L * (-U) := by
  sorry









theorem theorem_148739_problem
  (N : ℕ)
  (hN : 0 < N)
  (x : Matrix (Fin N) (Fin 1) ℂ)
  (W : Matrix (Fin N) (Fin N) ℂ)
  (hW : W.conjTranspose * W = (1 / (N : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ))
  (y : Matrix (Fin N) (Fin 1) ℂ)
  (hy : y = W * x)
  (σ_x_sq : ℂ)
  (hσx : σ_x_sq = (1 / (N : ℂ)) * (x.conjTranspose * x) 0 0)
  (σ_y_sq : ℂ)
  (hσy : σ_y_sq = (1 / (N : ℂ)) * (y.conjTranspose * y) 0 0) :
  σ_y_sq = (1 / (N : ℂ)) * σ_x_sq := by
  sorry



theorem theorem_149019_problem
  (n : ℕ)
  (p : ℝ)
  (hp : 0 ≤ p ∧ p ≤ 1)
  (x : Fin n → ℝ)
  (W : Fin n → Fin n → ℝ)
  -- The output of the network where weights are scaled by p (Inference Rule)
  (f_scaled : Fin n → ℝ := fun i => ∑ j, (p * W i j) * x j)
  -- The expected output of the ensemble of subnetworks (Dropout Rule)
  -- Modeled as the expectation of the linear combination: E[M * W * x] = p * W * x
  (f_subnet_expected : Fin n → ℝ := fun i => p * (∑ j, W i j * x j)) :
  -- The claim is that the expected subnetwork output equals the scaled inference output
  f_subnet_expected = f_scaled := by
  sorry





theorem theorem_148900_problem
  (v : (Fin 3 → ℝ) → (Fin 3 → ℝ))
  (x : Fin 3 → ℝ)
  (hv : DifferentiableAt ℝ v x) :
  fderiv ℝ v x (v x) = 
  ∑ j : Fin 3, (∑ i : Fin 3, (v x i) * (fderiv ℝ (fun y => v y j) x (Pi.basisFun ℝ (Fin 3) i))) • (Pi.basisFun ℝ (Fin 3) j) := by
  sorry









theorem theorem_149242_problem
  {R : Type*} [CommRing R]
  (n : ℕ) (hn : n ≥ 1)
  (t : R)
  (a : Fin n → R) :
  let A : Matrix (Fin n) (Fin n) R := fun i j =>
    if j.val = n - 1 then
      if i.val = n - 1 then t + a i else a i
    else if i.val = j.val then
      t
    else if i.val = j.val + 1 then
      -1
    else
      0
  A.det = (∑ k : Fin n, a k * t ^ (k : ℕ)) + t ^ n := by
  sorry

theorem theorem_149117_problem (K : Type*) [Field K] (n : ℕ)
  (π : {v : Fin (n + 1) → K // v ≠ 0} → Projectivization K (Fin (n + 1) → K))
  (hπ : ∀ v, π v = Projectivization.mk K v.1 v.2)
  (h_inj : Function.Injective π) :
  Nonempty (K ≃+* ZMod 2) := by
  sorry

theorem theorem_149232_problem (n : ℕ) (A B C D : Matrix (Fin n) (Fin n) ℝ) :
  ∃ At Bt Ct Dt : Matrix (Fin n) (Fin n) ℝ,
    Dt * Ct * Bt * At = 1 ∧
    ∀ Ap Bp Cp Dp : Matrix (Fin n) (Fin n) ℝ,
      Dp * Cp * Bp * Ap = 1 →
      (∑ i, ∑ j, ((A - At) i j) ^ 2) + (∑ i, ∑ j, ((B - Bt) i j) ^ 2) +
      (∑ i, ∑ j, ((C - Ct) i j) ^ 2) + (∑ i, ∑ j, ((D - Dt) i j) ^ 2) ≤
      (∑ i, ∑ j, ((A - Ap) i j) ^ 2) + (∑ i, ∑ j, ((B - Bp) i j) ^ 2) +
      (∑ i, ∑ j, ((C - Cp) i j) ^ 2) + (∑ i, ∑ j, ((D - Dp) i j) ^ 2) := by
  sorry

theorem theorem_149263_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  (T : X →L[𝕜] Y)
  (h : IsCompactOperator T) :
  TopologicalSpace.SeparableSpace (Set.range T) := by
  sorry

theorem theorem_149130_problem (a b : ℝ) (A B : Matrix (Fin 2) (Fin 2) ℝ)
  (hA : A = !![a, 0; 0, 1])
  (hB : B = !![0, -b; 1, 0]) :
  Matrix.det (Matrix.hadamard A B) = 0 := by
  sorry

theorem theorem_149255_problem (f : ℂ → ℂ) (h_def : ∀ z, f z = Complex.I * z) :
  ¬ ∃ w : ℂ, ∀ z : ℂ, f z = w * star z := by
  sorry

theorem theorem_149558_problem (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
  (h_symm : B.IsSymm)
  (h_odd : ∀ (S : Finset (Fin n)), Odd S.card → (B.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det = 0)
  (h_even : ∀ (S : Finset (Fin n)), Even S.card → (B.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det ≥ 0) :
  B = 0 := by
  sorry

theorem theorem_149381_problem
  (n : ℕ)
  (Is Ic : Type*) [Fintype Is] [Fintype Ic]
  (Ns Nc Tc : ℝ)
  (y y_star : Is → Ic → ℝ → ℝ)
  (sigma : Is → ℝ)
  (d2y : Fin n → Fin n → Is → Ic → ℝ → ℝ)
  (hNs : Ns > 0) (hNc : Nc > 0) (hTc : Tc > 0)
  (hsigma : ∀ s, sigma s ≠ 0)
  (h_diff_symm : ∀ (j k : Fin n) (s : Is) (c : Ic) (t : ℝ), d2y j k s c t = d2y k j s c t) :
  let H (j k : Fin n) := (1 / (2 * Nc * Ns)) * ∑ s : Is, ∑ c : Ic, (1 / Tc) * ∫ t in (0)..Tc,
    ((y s c t - y_star s c t) / (sigma s)^2) * d2y j k s c t
  ∀ j k, H j k = H k j := by
  sorry

theorem theorem_149452_problem
  {R : Type*} [Field R]
  {n : Type*} [Fintype n] [DecidableEq n]
  {V : Type*} [AddCommGroup V] [Module R V]
  (b : Basis n R V)
  (b' : Basis n R V)
  (S : Matrix n n R)
  (hS : Invertible S)
  (h_trans : ∀ i, b' i = ∑ j, S j i • b j)
  (x : V) :
  ∀ i, b'.repr x i = ∑ j, (S⁻¹ i j) * b.repr x j := by
  sorry



theorem theorem_149630_problem
  {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (DX : Submodule ℝ X) (DY : Submodule ℝ Y)
  (hDX : Dense (DX : Set X))
  (hDY : Dense (DY : Set Y))
  (T : DX →L[ℝ] DY) :
  ∀ y ∈ closure (DY : Set Y), ∃ x : ℕ → DX, Filter.Tendsto (fun n ↦ (T (x n) : Y)) Filter.atTop (nhds y) := by
  sorry











theorem theorem_149959_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
  A.rank = A.transpose.rank := by
  sorry

theorem theorem_149814_problem (f : (Fin 3 → ℝ) → ℝ) (g : (Fin 3 → ℝ) → (Fin 3 → ℝ))
  (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
  let h := f ∘ g
  ∀ (x : Fin 3 → ℝ) (j : Fin 3),
  fderiv ℝ h x (Pi.single j 1) =
    ∑ i : Fin 3, (fderiv ℝ f (g x) (Pi.single i 1)) * (fderiv ℝ (fun y => g y i) x (Pi.single j 1)) := by
  sorry









theorem theorem_150415_problem {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (S : Matrix m n ℂ) :
  S.rank = S.conjTranspose.rank := by
  sorry



theorem theorem_150199_problem (a x : ℝ) (ha : 0 < a) :
  ∫ k : ℝ, Complex.exp (Complex.I * k * x) / ((k : ℂ) ^ 2 + (a : ℂ) ^ 2) =
  ((Real.pi / a) * Real.exp (-a * |x|) : ℂ) := by
  sorry

theorem theorem_150104_problem (n : ℕ) (x : Fin n → ℝ)
  (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
  x = ∑ p : Fin n → Fin 2, (∏ i : Fin n, (1 - |x i - (p i : ℝ)|)) • (fun i ↦ (p i : ℝ)) := by
  sorry











theorem theorem_150621_problem
  (n : ℕ) (hn : 0 < n)
  (x : ℝ → ℝ)
  (G : ℝ → (Fin n → ℝ) → ℝ)
  (h_diff : ContDiff ℝ n x) :
  (∀ t, iteratedDeriv n x t = G t (fun i ↦ iteratedDeriv i x t)) ↔
  (∀ t, ∀ i : Fin n,
    deriv (fun τ ↦ iteratedDeriv i x τ) t =
      if h : i.val + 1 < n then
        iteratedDeriv (i.val + 1) x t
      else
        G t (fun j ↦ iteratedDeriv j x t)) := by
  sorry



theorem theorem_150809_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (h_symm : A.IsSymm)
  (h_psd : A.PosSemidef) :
  ∀ i : Fin n, 0 ≤ A i i := by
  sorry

theorem theorem_150843_problem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (e₁ e₂ : V) (h₁ : e₁ ≠ 0) (h₂ : e₂ ≠ 0)
  (X : Submodule K V) (hX : X = Submodule.span K {e₁, e₂})
  (Y : Submodule K V) (hY : Y = Submodule.span K {e₁ + e₂}) :
  Y ≤ X ↔ e₁ + e₂ ∈ Submodule.span K {e₁, e₂} := by
  sorry





theorem theorem_150794_problem (a : ℕ → ℝ) 
  (h_bound : ∃ M, ∀ n, |a n| ≤ M) : 
  ∃ (φ : ℕ → ℕ) (y : ℝ), StrictMono φ ∧ Filter.Tendsto (a ∘ φ) Filter.atTop (nhds y) := by
  sorry

theorem theorem_151044_problem
  (f : ℝ → ℝ → ℝ → ℝ)
  (x_star y_star : ℝ → ℝ)
  (L : ℝ → ℝ → ℝ → ℝ)
  (ξ₀ : ℝ)
  -- Condition: f is a smooth objective function (C^1 assumed for derivatives)
  (hf : ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2))
  -- Condition: L is the Lagrangian. In the absence of explicit constraints in the problem description,
  -- this is the unconstrained Lagrangian (L = f).
  (hL : L = f)
  -- Condition: x*, y* denote the solution to the maximization problem.
  -- This implies the first-order conditions (partial derivatives w.r.t x and y are 0).
  (h_opt_x : ∀ ξ, deriv (fun x => f x (y_star ξ) ξ) (x_star ξ) = 0)
  (h_opt_y : ∀ ξ, deriv (fun y => f (x_star ξ) y ξ) (y_star ξ) = 0)
  -- Implicit Condition: Smoothness of the optimal path (required for the total derivative to exist)
  (hx_diff : Differentiable ℝ x_star)
  (hy_diff : Differentiable ℝ y_star) :
  -- Conclusion: The derivative of the value function equals the partial derivative of the Lagrangian
  deriv (fun ξ => f (x_star ξ) (y_star ξ) ξ) ξ₀ =
  deriv (fun ξ => L (x_star ξ₀) (y_star ξ₀) ξ) ξ₀ := by
  sorry

theorem theorem_151083_problem
  (n : ℕ)
  (x_beta : Fin n → ℝ)
  (d : Fin n → ℝ)
  (t : Fin n → ℝ) :
  (∑ i : Fin n, (Real.log (Real.exp (x_beta i) / (∑ j : Fin n, (if t j ≥ t i then (1 : ℝ) else 0) * Real.exp (x_beta i)))) * d i) =
  (∑ i : Fin n, d i * x_beta i) - (∑ i : Fin n, d i * Real.log (∑ j : Fin n, (if t i ≤ t j then (1 : ℝ) else 0) * Real.exp (x_beta i))) := by
  sorry







theorem theorem_151138_problem
  (k : ℕ)
  (hk : 0 < k)
  (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  -- T is a linear map from l_infty^k to Y
  (T : (PiLp ⊤ (fun _ : Fin k ↦ ℝ)) →L[ℝ] Y)
  -- C is the cotype 2 constant of Y (L1)
  (C : ℝ)
  (hC : 0 < C)
  -- The definition of Cotype 2 with constant C
  (h_cotype : ∀ (x : Fin k → Y),
    (∑ ε : Fin k → Bool, ‖∑ i, (if ε i then (1 : ℝ) else -1) • x i‖) / (2 ^ k : ℝ) ≥
    (1 / C) * Real.sqrt (∑ i, ‖x i‖ ^ 2))
  -- inv_T corresponds to ||T^{-1}||, characterizing the embedding
  (inv_T : ℝ)
  (h_inv : ∀ v, ‖v‖ ≤ inv_T * ‖T v‖) :
  ‖T‖ * inv_T ≥ Real.sqrt k / C := by
  sorry

theorem theorem_151299_problem
  {n : ℕ} {R : Type*} [CommRing R]
  (A B : Matrix (Fin n) (Fin n) R)
  (h : A ^ 2 = B) :
  (Matrix.transpose A) ^ 2 = Matrix.transpose B := by
  sorry





theorem theorem_151276_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  (T : X →ₗ[ℝ] Y)
  (h : IsClosed (Set.range (fun x => (x, T x)))) :
  Continuous T := by
  sorry



theorem theorem_151641_problem
  {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  (u₀ : U) (hu₀ : u₀ ≠ 0) (x : U)
  (φ : ℝ → ℝ) (hφ : ∀ α, φ α = ‖x + α • u₀‖) :
  Continuous φ := by
  sorry





theorem theorem_151181_problem (n : ℕ) (M₁ M₂ : Matrix (Fin n) (Fin n) ℝ)
  (h₁ : M₁ = 1)
  (h₂ : ¬ ∃ (k : ℝ), M₂ = k • (1 : Matrix (Fin n) (Fin n) ℝ)) :
  ¬ ∃ (α : ℝ), M₂ = α • M₁ := by
  sorry













theorem theorem_151751_problem
  {K V W : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  (p : ℕ)
  (T : MultilinearMap K (fun _ : Fin p => V) W)
  (Alt_T : MultilinearMap K (fun _ : Fin p => V) W)
  (h_Alt_def : Alt_T = (p.factorial : K)⁻¹ • ∑ σ : Equiv.Perm (Fin p), (Equiv.Perm.sign σ : K) • T.domDomCongr σ)
  (h_alternating : ∀ σ : Equiv.Perm (Fin p), T.domDomCongr σ = (Equiv.Perm.sign σ : K) • T) :
  Alt_T = T := by
  sorry







theorem theorem_151935_problem :
  ∃ (n : ℕ) (a b c d : Fin n → ℝ),
    (∑ i, |a i - b i| = ∑ i, |c i - d i|) ∧
    (∑ i, |a i - b i|^2 ≠ ∑ i, |c i - d i|^2) := by
  sorry

theorem theorem_151905_problem
  (n : ℕ)
  (a b : ℝ)
  (F : (Fin n → ℝ) → (Fin n → ℝ))
  (phi : ℝ → (Fin n → ℝ))
  (hF : Continuous F)
  (hphi : ContDiff ℝ 1 phi) :
  ∫ t in a..b, (∑ i : Fin n, F (phi t) i * (deriv phi t) i) =
  ∑ i : Fin n, ∫ t in a..b, F (phi t) i * deriv (fun x ↦ phi x i) t := by
  sorry





theorem theorem_152185_problem
  (n k : ℕ)
  (P F : Matrix (Fin n) (Fin n) ℝ)
  (Q : Matrix (Fin n) (Fin k) ℝ)
  (P' : Matrix (Fin n) (Fin n) ℝ)
  (X Y : Matrix (Fin n) (Fin n) ℝ)
  (hP_symm : P.IsSymm)
  (hQ_orth : Q.transpose * Q = 1)
  (hP_prime : P' = -P)
  (h_decomp : P' * F + F.transpose * P' = X + Y)
  (hX : (-X).PosSemidef)
  (hY : Y.PosSemidef)
  (hY_cond : Q.transpose * Y * Q = 0) :
  ∃ L : Matrix (Fin n) (Fin k) ℝ,
    Q.transpose * (P' * F + F.transpose * P' + L * L.transpose) * Q = 0 := by
  sorry

