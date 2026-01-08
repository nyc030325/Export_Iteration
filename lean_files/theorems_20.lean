import Mathlib
import Mathlib.Tactic

theorem theorem_102222_problem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (δ₁ : V →ₗ[K] V) (f : ℕ → V)
  (h : ∀ n m : ℕ, f m - f n ∈ LinearMap.ker δ₁) :
  ∃ g : V, ∀ n : ℕ, f n - g ∈ LinearMap.ker δ₁ := by
  sorry

theorem theorem_102726_problem
  (n : ℕ)
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (hS_conv : Convex ℝ S)
  (hS_closed : IsClosed S) :
  S = ⋂₀ {H : Set (EuclideanSpace ℝ (Fin n)) |
    (∃ (f : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ H = {x | f x ≤ c}) ∧ S ⊆ H} := by
  sorry

theorem theorem_102623_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (U W : Submodule K V) (a b : V)
  (h : {v | ∃ u ∈ U, v = a + u} = {v | ∃ w ∈ W, v = b + w}) :
  U = W := by
  sorry

theorem theorem_103127_problem
  (n : ℕ)
  (v : Fin n → (Fin n → ℤ))
  (h_indep : LinearIndependent ℤ v) :
  let V := Matrix.of (fun i j => v j i)
  let H := AddSubgroup.closure (Set.range v)
  H.index = Int.natAbs V.det := by
  sorry







theorem theorem_102789_problem
  {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (h_open : IsOpen S)
  (h_smooth : ContDiffOn ℝ ⊤ f S)
  (z_k z_k_prev : EuclideanSpace ℝ (Fin n))
  (h_seg : segment ℝ z_k_prev z_k ⊆ S)
  (h_neq : z_k ≠ z_k_prev) :
  ∃ y ∈ segment ℝ z_k_prev z_k,
    f z_k - f z_k_prev = inner (gradient f y) (z_k - z_k_prev) := by
  sorry



theorem theorem_103271_problem
  (K A A' : Type*)
  [Field K]
  [CommRing A] [Algebra K A]
  [Field A'] [Algebra K A']
  (f : A →ₐ[K] A')
  (h_inj : Function.Injective f)
  (h_fin : Algebra.FiniteType K A') :
  IsField A := by
  sorry

theorem theorem_103079_problem
  (n : ℕ)
  (f g : (Fin n → ℝ) → (Fin n → ℝ))
  (ε : ℝ)
  (x₀ x₀' : Fin n → ℝ)
  (h_smooth_f : ContDiff ℝ ⊤ f)
  (h_smooth_g : ContDiff ℝ ⊤ g)
  (h_f_x₀ : f x₀ = 0)
  (h_pert : f x₀' + ε • g x₀' = 0)
  (J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
  (hJ : J = fderiv ℝ f x₀)
  (J_inv : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
  (h_inv_left : J_inv ∘L J = ContinuousLinearMap.id ℝ (Fin n → ℝ))
  (h_inv_right : J ∘L J_inv = ContinuousLinearMap.id ℝ (Fin n → ℝ)) :
  x₀' - x₀ = -ε • (J_inv (g x₀)) := by
  sorry

















theorem theorem_103212_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (A B : Module.End K V)
  (v : V) (lam : K)
  (h_comm : A * B - B * A = A)
  (h_eig : B v = lam • v) :
  B (A v) = (lam - 1) • (A v) := by
  sorry



theorem theorem_103671_problem
  (n m p : ℕ)
  (f : (Fin n → ℝ) → (Fin m → ℝ))
  (g : (Fin m → ℝ) → (Fin p → ℝ))
  (hf : ContDiff ℝ ⊤ f)
  (hg : ContDiff ℝ ⊤ g) :
  ContDiff ℝ ⊤ (g ∘ f) := by
  sorry



theorem theorem_103891_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (A B : E →L[ℂ] E)
  (hA : IsSelfAdjoint A)
  (hB : IsSelfAdjoint B)
  (hAB : Commute A B) :
  ∃ (ι : Type) (_ : Fintype ι) (b : OrthonormalBasis ι ℂ E),
    ∀ i, ∃ (α β : ℝ),
      A (b i) = (α : ℂ) • b i ∧
      B (b i) = (β : ℂ) • b i ∧
      (A + B) (b i) = ((α + β) : ℂ) • b i := by
  sorry



theorem theorem_103884_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (A : E →L[ℂ] E)
  (hA : spectralRadius ℂ A < 1) :
  ∃ C > 0, ∃ ε > 0, ∀ k : ℕ, ‖A ^ k‖ ≤ C * (1 - ε) ^ k := by
  sorry

theorem theorem_103481_problem
  (R1 R2 : Matrix (Fin 3) (Fin 3) ℝ)
  (t1 t2 : Fin 3 → ℝ)
  (hR1 : R1 * R1.transpose = 1)
  (hR2 : R2 * R2.transpose = 1)
  (q1 q2 qW : Fin 3 → ℝ)
  (h1 : qW = R1.mulVec q1 + t1)
  (h2 : qW = R2.mulVec q2 + t2) :
  q2 = (R2.transpose * R1).mulVec q1 + R2.transpose.mulVec (t1 - t2) := by
  sorry



theorem theorem_103851_problem
  {F : Type*} [Field F]
  (n : ℕ)
  (t : Fin n → F)
  (h_distinct : Function.Injective t) :
  LinearIndependent F (fun (i : Fin n) => (fun (j : Fin n) => t i ^ (j : ℕ))) := by
  sorry



theorem theorem_104152_problem {F : Type*} [Field F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
  ∃ U V : Matrix (Fin n) (Fin n) F, IsUnit U ∧ IsUnit V ∧
  ∀ i j : Fin n, i ≠ j → (U * A * V) i j = 0 := by
  sorry









theorem theorem_104589_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
  (∀ x : Fin n → ℝ, A.mulVec x = 0 → x = 0) ↔
  Set.Finite { x : Fin n → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ (∀ j, ∃ k : ℤ, A.mulVec x j = k) } := by
  sorry







theorem theorem_104809_problem :
  ∃ B : Matrix.GeneralLinearGroup (Fin 3) ℝ,
    (B.1 * N2 * (B⁻¹).1 = N2) ∧
    (B.1 * N1 * (B⁻¹).1 ≠ J_N1) := by
  sorry





theorem theorem_104623_problem (p q : ℕ) (hp : p ≥ 2) (hq : q ≥ 2)
  (f : ℕ → ℕ)
  (hf : ∀ x y, x < p → y < q → f (x + p * y) = q * x + y) :
  (Finset.filter (fun z : ℕ × ℕ => z.1 < z.2 ∧ f z.1 > f z.2)
    (Finset.product (Finset.range (p * q)) (Finset.range (p * q)))).card =
    (Nat.choose p 2) * (Nat.choose q 2) := by
  sorry













theorem theorem_105077_problem {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (B : Set V)
  (h_indep : LinearIndependent F ((↑) : B → V))
  (h_span : Submodule.span F B = ⊤)
  (S T : Set V)
  (hS : S ⊆ B)
  (hT : T ⊆ B) :
  Submodule.span F (S ∩ T) = Submodule.span F S ⊓ Submodule.span F T := by
  sorry



theorem theorem_105072_problem (x_m1 x_0 x_1 x_2 : ℝ) :
  let M : Matrix (Fin 4) (Fin 4) ℝ := !![
    0, 1, 0, 0;
    -0.5, 0, 0.5, 0;
    1, -2.5, 2, -0.5;
    -0.5, 1.5, -1.5, 0.5
  ]
  let X : Matrix (Fin 4) (Fin 1) ℝ := !![x_m1; x_0; x_1; x_2]
  let y : ℝ → ℝ := fun t => (!![1, t, t^2, t^3] * M * X) 0 0
  (y 0 = x_0) ∧
  (y 1 = x_1) ∧
  (deriv y 0 = (x_1 - x_m1) / 2) ∧
  (deriv y 1 = (x_2 - x_0) / 2) := by
  sorry

theorem theorem_105060_problem (n : ℕ) (Y lam : ℝ) (hn : n > 0) :
  let U : Matrix (Fin n) (Fin n) ℝ := fun _ _ ↦ 1
  let I : Matrix (Fin n) (Fin n) ℝ := 1
  let T := U - (1 - Real.exp Y) • I
  Matrix.det (T - lam • I) = (Real.exp Y - 1 - lam) ^ (n - 1) * ((n : ℝ) + Real.exp Y - 1 - lam) := by
  sorry

theorem theorem_104931_problem (n : ℕ) (x₀ s y : Fin n → ZMod 2) :
  Matrix.dotProduct (x₀ + s) y = Matrix.dotProduct x₀ y + Matrix.dotProduct s y := by
  sorry

theorem theorem_105353_problem :
  let A : Matrix (Fin 3) (Fin 3) ℝ := 1
  let B : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 2; 0, 2, 0; 2, 0, 0]
  let C := B
  let D := A
  let M := Matrix.fromBlocks A B C D
  M.det = -27 := by
  sorry

























theorem theorem_106311_problem (n : ℕ) (V : Type*)
  [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace V] [TopologicalAddGroup V] [ContinuousSMul ℝ V]
  [T1Space V]
  [FiniteDimensional ℝ V]
  (h_dim : FiniteDimensional.finrank ℝ V = n) :
  Nonempty (V ≃ₜ (Fin n → ℝ)) := by
  sorry









theorem theorem_106293_problem
  (L1 L2 y1 y2 : ℝ)
  (x1 x2 : Fin 3 → ℝ)
  (w : Fin 3 → ℝ)
  (h_w : ∀ i, w i = L1 * y1 * x1 i + L2 * y2 * x2 i) :
  Matrix.dotProduct w w = ∑ i : Fin 3, (L1 * y1 * x1 i + L2 * y2 * x2 i)^2 := by
  sorry



theorem theorem_105972_problem (n : ℕ) (T : Fin n → Fin n → Fin n → Fin n → ℝ)
  (i j k : Fin n) :
  ∑ l : Fin n, T i j k l = ∑ l : Fin n, T i j k l := by
  sorry



theorem theorem_106197_problem (n : ℕ) (a : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
  (hM : ∀ i j, M i j = if i = j then (a i)^2 + 1 else (a i) * (a j)) :
  M.det = 1 + ∑ i, (a i)^2 := by
  sorry



















theorem theorem_106823_problem (m n : Type*) [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n] (X : Matrix m n ℝ)
  (h : Invertible (X.transpose * X)) :
  (X * (X.transpose * X)⁻¹ * (X.transpose * X)⁻¹ * X.transpose)⁻¹ * X * (X.transpose * X)⁻¹ = X := by
  sorry

theorem theorem_106784_problem :
  ∃ (n : ℕ) (F : Type) (_ : Field F) (A B : Matrix (Fin n) (Fin n) F),
    A * B = A ∧ B ≠ 1 := by
  sorry













theorem theorem_108197_problem (n : ℕ) (L : Matrix (Fin n) (Fin n) ℝ)
  (h_lower : ∀ i j, i < j → L i j = 0)
  (h_unit : ∀ i, L i i = 1)
  (h_pivot : ∀ i j, i > j → |L i j| ≤ 1) :
  ∀ i, ∑ j, |L i j| ≤ (n : ℝ) := by
  sorry



theorem theorem_107752_problem
  (n : ℕ)
  (A₁ A₂ : Matrix (Fin n) (Fin n) ℝ)
  (hA₁ : A₁.PosDef)
  (hA₂ : A₂.PosDef)
  (r : ℝ)
  (hr : 0 ≤ r ∧ r ≤ 1) :
  (r • A₁ + (1 - r) • A₂).PosDef := by
  sorry





theorem theorem_108121_problem
  {X : Type*} [MetricSpace X]
  (f_n : ℕ → X → ℝ) (f : X → ℝ)
  (h_unif : TendstoUniformly f_n f Filter.atTop)
  (h_cont : ∀ n, Continuous (f_n n)) :
  Continuous f := by
  sorry

