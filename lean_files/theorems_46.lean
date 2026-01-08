import Mathlib
import Mathlib.Tactic











theorem theorem_247734_problem (a b : ℝ) (f : ℂ → ℂ) (γ : ℝ → ℂ)
  (hf : Continuous f)
  (hγ : ∀ t ∈ Set.Icc a b, γ t = ↑t) :
  ∫ t in a..b, f (γ t) * deriv γ t = ∫ t in a..b, f ↑t := by
  sorry

theorem theorem_247746_problem (n : ℕ) {R : Type*} [CommRing R]
  (A : Matrix (Fin n) (Fin n) R)
  (h : Fin n → R)
  (h_symm : A.IsSymm)
  (j : Fin n) :
  ∑ k : Fin n, h k * (∑ i : Fin n, A.adjugate i j * A k i) = A.det * h j := by
  sorry

theorem theorem_248061_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  (A : X →L[𝕜] Y)
  (h_bij : Function.Bijective A) :
  Continuous (Function.invFun A) := by
  sorry

theorem theorem_247507_problem
  {n k : ℕ} (hkn : k ≤ n)
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (e : Basis (Fin n) ℝ V)
  (c : Fin k → ℝ)
  (hc : ∀ i, c i ≠ 1)
  (A : V →ₗ[ℝ] V)
  (hA₁ : ∀ (i : Fin k), A (e (Fin.castLE hkn i)) = c i • e (Fin.castLE hkn i))
  (hA₂ : ∀ (i : Fin n), k ≤ i → A (e i) = e i)
  (b : V) :
  let V₁ := Submodule.span ℝ (Set.range (fun (i : Fin k) ↦ e (Fin.castLE hkn i)))
  (∃ x, A x = x + b) ↔ b ∈ V₁ := by
  sorry

theorem theorem_247597_problem (n : ℕ) (r : ℕ) (F : Type*) [Field F]
  (h_r : r ≤ n)
  (dim : Set (Matrix (Fin n) (Fin n) F) → ℕ) :
  dim { A : Matrix (Fin n) (Fin n) F | A.rank = r } = n^2 - (n - r)^2 := by
  sorry



theorem theorem_247195_problem
  (n : ℕ)
  (Ω : Set ℝ)
  (a : ℝ → ℝ)
  (ha_cont : ContinuousOn a Ω)
  (ha_pos : ∀ x ∈ Ω, 0 < a x)
  (phi : Fin n → ℝ → ℝ)
  (B : (ℝ → ℝ) → (ℝ → ℝ) → ℝ)
  (hB : ∀ u v, B u v = ∫ x in Ω, a x * (deriv u x) * (deriv v x))
  (K : Matrix (Fin n) (Fin n) ℝ)
  (hK : ∀ i j, K i j = B (phi j) (phi i)) :
  ∀ i j, K i j = ∫ x in Ω, a x * (deriv (phi i) x) * (deriv (phi j) x) := by
  sorry





























theorem theorem_248304_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  (φ : V →ₗᵢ[𝕜] W) :
  IsClosed (Set.range φ) := by
  sorry

theorem theorem_248331_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (v a : E) (h : a ≠ 0) :
  inner (v - (inner a v / ‖a‖ ^ 2) • a) a = (0 : ℝ) := by
  sorry



theorem theorem_248176_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (hn : (Fintype.card n : ℝ) ≠ 0)
  (S : Matrix n n ℝ)
  (hS : S.IsSymm) :
  ∃! p : ℝ × Matrix n n ℝ,
    S = p.1 • (1 : Matrix n n ℝ) + p.2 ∧
    p.2.IsSymm ∧
    Matrix.trace p.2 = 0 := by
  sorry

theorem theorem_248195_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (f : X →ₗ[ℝ] ℝ)
  (hf : ¬ Continuous f) :
  ∃ x₀ : X, f x₀ ≠ 0 ∧ ¬ Continuous (fun h => 2 * f x₀ * f h) := by
  sorry





theorem theorem_248559_problem (N : ℕ) (K : Matrix (Fin N) (Fin N) ℝ) (η : ℝ)
  (ones : Fin N → ℝ) (h_ones : ones = fun _ ↦ 1) :
  Matrix.trace (K * (η • Matrix.vecMulVec ones ones)) =
  η * Matrix.dotProduct ones (Matrix.mulVec K ones) := by
  sorry



theorem theorem_248165_problem (x₀ y₀ z₀ : ℝ)
  (γ : ℝ → ℝ × ℝ × ℝ)
  (h_init : γ 0 = (x₀, y₀, z₀))
  (h_ode : ∀ t, HasDerivAt γ (let (x, y, z) := γ t; (y, x, z)) t) :
  ∀ t, γ t = (
    (x₀ + y₀) / 2 * Real.exp t + (x₀ - y₀) / 2 * Real.exp (-t),
    (x₀ + y₀) / 2 * Real.exp t - (x₀ - y₀) / 2 * Real.exp (-t),
    z₀ * Real.exp t
  ) := by
  sorry











theorem theorem_249013_problem {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
  (h : IsUnit (A.transpose * A)) :
  Submodule.span ℝ (Set.range A) = ⊤ := by
  sorry



theorem theorem_248980_problem
  (n m : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ) :
  sInf { v | ∃ x : Fin n → ℝ, Matrix.mulVec A x ≤ b ∧ v = ⨆ i, |x i| } =
  sInf { z | ∃ x : Fin n → ℝ, Matrix.mulVec A x ≤ b ∧ ∀ i, -z ≤ x i ∧ x i ≤ z } := by
  sorry

theorem theorem_249161_problem
  {D C M : Type*}
  [Monoid M] [MulAction M D]
  (S T : M)
  (f : D → C)
  (hS : ∀ z : D, f (S • z) = f z)
  (hT : ∀ z : D, f (T • z) = f z)
  (β : M)
  (hβ : β ∈ Submonoid.closure ({S, T} : Set M)) :
  ∀ z : D, f (β • z) = f z := by
  sorry



theorem theorem_248974_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (A : ℕ → (X →L[𝕜] X))
  (x : X)
  (h : CauchySeq A) :
  CauchySeq (fun n ↦ A n x) := by
  sorry





theorem theorem_249747_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (x_seq y_seq : ℕ → V) (x y : V)
  (h1 : Filter.Tendsto x_seq Filter.atTop (nhds x))
  (h2 : Filter.Tendsto y_seq Filter.atTop (nhds y))
  (h3 : Filter.Tendsto (fun n => ‖y_seq n‖) Filter.atTop (nhds ‖y‖)) :
  Filter.Tendsto (fun n => ‖x_seq n - x‖ + ‖y_seq n - y‖) Filter.atTop (nhds 0) := by
  sorry

theorem theorem_249811_problem
  (K : Type*) [Field K]
  (X Y : Type*) [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  (A : X →ₗ[K] Y) :
  LinearMap.ker (LinearMap.dualMap A) = (LinearMap.range A).dualAnnihilator := by
  sorry















theorem theorem_249430_problem (A : Matrix (Fin 2) (Fin 2) ℝ)
  (J : Matrix (Fin 2) (Fin 2) ℝ)
  (hJ : J = !![0, 1; -1, 0])
  (h_sp : A.transpose * J + J * A = 0) :
  ∃ a b c : ℝ, A = !![a, b; c, -a] := by
  sorry







theorem theorem_250397_problem
  (k : ℕ)
  (c : ℝ)
  (hk : 0 < k)
  (hc : 0 < c)
  (Y : Fin k → ℝ)
  (hY : 0 < ∑ i, (Y i)^2)
  (X : Fin k → ℝ)
  (hX : ∀ i, X i = (c / Real.sqrt (∑ j, (Y j)^2)) * Y i) :
  Real.sqrt (∑ i, (X i)^2) = c := by
  sorry



theorem theorem_250345_problem
  {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
  (n k : ℕ) (hkn : k ≤ n)
  (T : V →ₗ[F] W)
  (v : Basis (Fin n) F V)
  (h_ker : LinearMap.ker T = Submodule.span F (v '' {i | i.val < k})) :
  LinearMap.range T = Submodule.span F ((T ∘ v) '' {i | k ≤ i.val}) := by
  sorry

theorem theorem_249644_problem 
  {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (K : E →L[𝕜] E) 
  (hK : IsCompactOperator K)
  (h_inv : IsUnit ((1 : E →L[𝕜] E) - K))
  (A : E →L[𝕜] E)
  (hA_rank : FiniteDimensional 𝕜 (LinearMap.range A))
  (hA_eq : A = (h_inv.unit.inv : E →L[𝕜] E) - 1)
  (det_a : 𝕜)
  (h_det : det_a ≠ 0) :
  (1 : E →L[𝕜] E) - (h_inv.unit.inv : E →L[𝕜] E) = (det_a)⁻¹ • A := by
  sorry









theorem theorem_250108_problem
  (A B C : Fin 3 → ℝ)
  (b : Basis (Fin 3) ℝ (Fin 3 → ℝ))
  (hA_def : b 0 = A)
  (hB_def : b 1 = B)
  (hC_def : b 2 = C)
  (φ : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
  (h1 : φ A = -A)
  (h2 : φ B = -B)
  (h3 : φ C = -C) :
  ∀ v : Fin 3 → ℝ, φ v = -v := by
  sorry

theorem theorem_250464_problem (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (x : Fin m → ℝ)
  (hx : ∀ i, x i = 1) :
  Matrix.dotProduct (A.mulVec (A.transpose.mulVec x)) x =
  ∑ i : Fin n, (A.transpose.mulVec x i) ^ 2 := by
  sorry



theorem theorem_250284_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : Set E) (x_n : ℕ → E) (x : E)
  (hK : IsCompact K)
  (h_seq : ∀ n, x_n n ∈ K)
  (hx : x ∈ K)
  (h_weak : ∀ φ : NormedSpace.Dual ℝ E, Filter.Tendsto (fun n ↦ φ (x_n n)) Filter.atTop (nhds (φ x))) :
  Filter.Tendsto x_n Filter.atTop (nhds x) := by
  sorry







theorem theorem_250791_problem :
  ∃ (n : ℕ) (P L U : Matrix (Fin n) (Fin n) ℝ),
    (∃ σ : Equiv.Perm (Fin n), P = Matrix.of (fun i j => if i = σ j then 1 else 0)) ∧
    P ≠ 1 ∧
    (∀ i j, i < j → L i j = 0) ∧
    (∀ i j, i > j → U i j = 0) ∧
    let M := U.transpose * P⁻¹ * L
    ¬ ((∀ i j, i > j → M i j = 0) ∨ (∀ i j, i < j → M i j = 0)) := by
  sorry



theorem theorem_251019_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (A dA : E →L[ℝ] E)
  (x dx b : E)
  (Ainv : E →L[ℝ] E)
  (hA_inv : A ∘L Ainv = 1 ∧ Ainv ∘L A = 1)
  (h_AdA_nonsing : ∃ B : E →L[ℝ] E, (A + dA) ∘L B = 1 ∧ B ∘L (A + dA) = 1)
  (hAx : A x = b)
  (hAdx : (A + dA) (x + dx) = b)
  (kA : ℝ)
  (hkA : kA = ‖A‖ * ‖Ainv‖) :
  ‖dx‖ ≤ (kA / ‖A‖) * ‖dA‖ * ‖x + dx‖ := by
  sorry

theorem theorem_251092_problem
  (X : Type*)
  (k : X → X → ℝ)
  (h_symm : ∀ x y, k x y = k y x)
  (h_pos : ∀ (n : ℕ) (c : Fin n → ℝ) (x : Fin n → X),
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, c i * c j * k (x i) (x j)) :
  ∃ (H : Type*) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H) (ϕ : X → H),
    ∀ x y, k x y = inner (ϕ x) (ϕ y) := by
  sorry



theorem theorem_251095_problem
  (L₁ L₂ : Set (ℝ × ℝ))
  (C : Set (ℝ × ℝ))
  (hL₁ : ∃ v₁ : ℝ × ℝ, v₁ ≠ 0 ∧ L₁ = {p | ∃ t : ℝ, p = t • v₁})
  (hL₂ : ∃ v₂ : ℝ × ℝ, v₂ ≠ 0 ∧ L₂ = {p | ∃ t : ℝ, p = t • v₂})
  (hC : C = {p : ℝ × ℝ | p.1^2 + p.2^2 = 1})
  (h_distinct : L₁ ≠ L₂) :
  L₁ ∩ L₂ ∩ C = ∅ := by
  sorry



theorem theorem_251297_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (n : ℕ)
  (A : V →ₗ[K] V)
  (x : Fin n → V)
  (lam : Fin n → K)
  (a : Fin n → K)
  (hx : ∀ k, x k ≠ 0)
  (h_eigen : ∀ k, A (x k) = lam k • x k)
  (h_distinct : Function.Injective lam)
  (h_sum_is_eigen : ∃ μ : K, (∑ k, a k • x k) ≠ 0 ∧ A (∑ k, a k • x k) = μ • (∑ k, a k • x k)) :
  ∃! k, a k ≠ 0 := by
  sorry

theorem theorem_251726_problem
  {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]
  (d m : ℕ)
  (H A : AffineSubspace k V)
  (hV : FiniteDimensional.finrank k V = d)
  (hH : FiniteDimensional.finrank k H.direction = d - 1)
  (hA : FiniteDimensional.finrank k A.direction = m)
  (h_inter : Set.Nonempty ((A : Set V) ∩ (H : Set V)))
  (h_not_para : ¬ (A.direction ≤ H.direction ∨ H.direction ≤ A.direction)) :
  FiniteDimensional.finrank k (A ⊓ H).direction = m - 1 := by
  sorry

theorem theorem_251200_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (x : H →L[ℂ] H) (n : ℝ)
  (hx : IsSelfAdjoint x)
  (hn : 0 < 1 / n)
  (h_pos : 0 ≤ x - (1 / n : ℂ) • (1 : H →L[ℂ] H)) :
  spectrum ℂ x ⊆ Complex.ofReal '' Set.Ici (1 / n) := by
  sorry

theorem theorem_251205_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA : IsUnit A) (hB : IsUnit B) :
  (A⁻¹ + B⁻¹)⁻¹ = A * (A + B)⁻¹ * B := by
  sorry







theorem theorem_251173_problem (n m : ℕ)
  (a : Fin m → Fin n → ℝ)
  (k : Fin m → ℝ)
  (p : Fin n → ℝ) :
  (∀ i : Fin m, (∑ j : Fin n, a i j * p j - k i) * (∑ j : Fin n, a i j * 0 - k i) > 0) ↔
  (∀ i : Fin m, (∑ j : Fin n, a i j * p j - k i) * k i < 0) := by
  sorry









theorem theorem_251520_problem (n : ℕ) (M : Type*)
  [AddCommGroup M] [Module GaussianInt M]
  (φ : M →ₗ[GaussianInt] M)
  (h : M ≃ₗ[GaussianInt] (Fin n → GaussianInt)) :
  ∃ U : Matrix (Fin n) (Fin n) GaussianInt,
  ∀ v : Fin n → GaussianInt, h (φ (h.symm v)) = Matrix.mulVec U v := by
  sorry







