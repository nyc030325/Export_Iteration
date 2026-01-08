import Mathlib
import Mathlib.Tactic

theorem theorem_192213_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (n : ℕ)
  (a : Fin (n + 1) → V)
  (h_geo : ∀ (t : Fin (n + 1) → K), ∑ i, t i = 0 → ∑ i, t i • a i = 0 → t = 0) :
  LinearIndependent K (fun (i : Fin n) ↦ a i.succ - a 0) := by
  sorry

theorem theorem_192217_problem
  (S : Type*) [AddCommGroup S] [Module ℝ S]
  (X : Finset (Set S))
  (T : S →ₗ[ℝ] ℝ)
  (beta : Set S → ℝ)
  (u : S)
  (Supp : Set S)
  (hSupp : Supp = {x : S | ∀ V ∈ X, x ∈ V → beta V * (T u) ≠ 0})
  (x : S) :
  x ∉ Supp ↔ ∃ V ∈ X, x ∈ V ∧ beta V * (T u) = 0 := by
  sorry



theorem theorem_192195_problem
  (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (t : ℝ)
  (h_diff : Differentiable ℝ f) :
  deriv (fun s ↦ f (s • x)) t = inner (gradient f (t • x)) x := by
  sorry



theorem theorem_192763_problem
  {K V : Type*} [NormedField K] [NormedAddCommGroup V] [NormedSpace K V]
  (f : V →ₗ[K] K)
  (x : ℕ → V)
  (y : V)
  (hx_unit : ∀ n, ‖x n‖ = 1)
  (hx_lim : Filter.Tendsto (fun n ↦ ‖f (x n)‖) Filter.atTop Filter.atTop) :
  ∀ᶠ n in Filter.atTop, f ((f y * (f (x n))⁻¹) • x n - y) = 0 := by
  sorry





theorem theorem_192581_problem
  (n : ℕ)
  (x u : Fin n → ℝ)
  (α : ℝ)
  (h_bound : ∀ i, x i ≤ u i)
  (h_alpha : 0 < α) :
  sInf {p | ∃ y : Fin n → ℝ,
    (∀ i, x i + y i ≤ u i) ∧
    (∀ i, 0 ≤ y i) ∧
    p = (∑ i, ∑ j, if i < j then |(x i + y i) - (x j + y j)| else 0) + α * (∑ i, y i)} =
  sInf {p | ∃ (y : Fin n → ℝ) (z : Fin n → Fin n → ℝ),
    (∀ i, x i + y i ≤ u i) ∧
    (∀ i, 0 ≤ y i) ∧
    (∀ i j, i < j → (x i + y i) - (x j + y j) ≤ z i j) ∧
    (∀ i j, i < j → -((x i + y i) - (x j + y j)) ≤ z i j) ∧
    p = (∑ i, ∑ j, if i < j then z i j else 0) + α * (∑ i, y i)} := by
  sorry





theorem theorem_193453_problem
  {m1 m2 n : Type*} [Fintype m1] [Fintype m2] [Fintype n]
  [DecidableEq m1] [DecidableEq m2] [DecidableEq n]
  {R : Type*} [CommRing R]
  (G1 : Matrix m1 n R) (G2 : Matrix m2 n R)
  (D : Matrix n n R)
  (B : Matrix (Sum m1 m2) (Sum m1 m2) R)
  (G : Matrix (Sum m1 m2) (Sum n n) R)
  (D' : Matrix (Sum n n) (Sum n n) R)
  (A : Matrix (Sum m1 m2) (Sum m1 m2) R)
  (hG : G = Matrix.fromBlocks G1 0 0 G2)
  (hD' : D' = Matrix.fromBlocks D 0 0 D)
  (hA : A = G * D' * G.transpose) :
  (A * B).trace = (D' * G.transpose * B * G).trace := by
  sorry

theorem theorem_193552_problem
  {K : Type*} [Field K]
  {m n : ℕ}
  (C : Matrix (Fin m) (Fin 1) K)
  (A : Matrix (Fin n) (Fin 1) K)
  (R : Matrix (Fin m) (Fin 1) K)
  (hC : C ≠ 0)
  (hR : (Matrix.transpose R * C) 0 0 ≠ 0) :
  ∀ B : Matrix (Fin n) (Fin m) K,
  B * C = A ↔ 
  ∃ N : Matrix (Fin n) (Fin m) K, 
    N * C = 0 ∧ 
    B = ((Matrix.transpose R * C) 0 0)⁻¹ • (A * Matrix.transpose R) + N := by
  sorry









theorem theorem_193578_problem (n : ℕ) (a b : ℕ → ℝ) :
  ∑ i in Finset.range n, a i * b i ≤
  Real.sqrt (∑ i in Finset.range n, (a i)^2) * Real.sqrt (∑ i in Finset.range n, (b i)^2) := by
  sorry



theorem theorem_193768_problem
  (M : ℝ)
  (Y : Type*) [TopologicalSpace Y] [CompactSpace Y] [Nonempty Y]
  (f : (Set.Icc (-M) M) × Y → ℝ)
  (hf : Continuous f)
  (x : ℕ → Set.Icc (-M) M)
  (x_inf : Set.Icc (-M) M)
  (h_conv : Filter.Tendsto x Filter.atTop (nhds x_inf))
  (h_cond : ∀ y : Y, Filter.liminf (fun n ↦ f (x n, y)) Filter.atTop ≥ 0) :
  Filter.liminf (fun n ↦ ⨅ y, f (x n, y)) Filter.atTop ≥ 0 := by
  sorry

theorem theorem_194322_problem
  {𝕜 : Type*} [NormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
  (T : E →ₗ[𝕜] E)
  (hT : ∀ v, ‖T v‖ = ‖v‖) :
  Function.Bijective T := by
  sorry



theorem theorem_194207_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (A P : H →L[ℂ] H)
  (hA_sa : IsSelfAdjoint A)
  (hA_ge_zero : 0 ≤ A)
  (hA_le_one : A ≤ 1)
  (hP_sa : IsSelfAdjoint P)
  (hP_idem : P ^ 2 = P)
  (h_eq : P * (1 - A) * P = 0) :
  (1 - A) * P = 0 := by
  sorry











theorem theorem_194297_problem :
  ∃ C : ℝ, C > 0 ∧
  ∀ (n : ℕ) (c : ℝ) (X : Matrix (Fin n) (Fin n) ℝ),
  (1 / (2 * Real.sqrt (n : ℝ)) < c) →
  (c < 1 / 4) →
  (∀ i j, |X i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j| < c) →
  (X.rank : ℝ) ≥ C * (Real.log (n : ℝ)) / (c^2 * Real.log (1 / c)) := by
  sorry



theorem theorem_193726_problem
  {F S T : Type*} [Field F]
  [Ring S] [Algebra F S]
  [Ring T] [Algebra F T]
  (m n : ℕ)
  (x : Fin m → S)
  (y : Fin n → T)
  (hS : Algebra.adjoin F (Set.range x) = ⊤)
  (hT : Algebra.adjoin F (Set.range y) = ⊤) :
  Algebra.adjoin F (Set.range (fun i => (x i, (0 : T))) ∪ Set.range (fun j => ((0 : S), y j))) = ⊤ := by
  sorry

theorem theorem_193781_problem (n : ℝ) (hn : 1 ≤ n) (f : ℝ → ℂ)
  (hf : ContinuousOn f (Set.Icc (1 / n) n))
  (phi : ℂ → ℂ)
  (hphi : ∀ z, phi z = ∫ t in (1 / n)..n, (t : ℂ) ^ (z - 1) * f t) :
  Differentiable ℂ phi := by
  sorry

theorem theorem_194280_problem
  (K : Type*) [Field K]
  (a1 b1 c1 a2 b2 c2 a3 b3 c3 : K) :
  (∃ x1 x2 x0 : K, (x1 ≠ 0 ∨ x2 ≠ 0 ∨ x0 ≠ 0) ∧
    a1 * x1 + b1 * x2 + c1 * x0 = 0 ∧
    a2 * x1 + b2 * x2 + c2 * x0 = 0 ∧
    a3 * x1 + b3 * x2 + c3 * x0 = 0) ↔
  Matrix.det !![a1, b1, c1; a2, b2, c2; a3, b3, c3] = 0 := by
  sorry

theorem theorem_194400_problem (x : ℕ → ℚ)
  (h1 : ∀ n : ℕ, 0 < n → ∃ k : ℤ, x n ∈ Set.Icc ((k : ℚ) / n) ((k + 1 : ℚ) / n))
  (a : ℕ → ℝ)
  (h2 : Filter.Tendsto a Filter.atTop (nhds 0))
  (h3 : ∀ n m : ℕ, n < m → |(x n : ℝ) - (x m : ℝ)| ≤ a n) :
  CauchySeq x := by
  sorry

theorem theorem_194484_problem
  {n : ℕ}
  {k K : Type*} [Field k] [Field K] [Algebra k K]
  (A : Matrix (Fin n) (Fin n) k)
  (b : Fin n → k)
  (x : Fin n → K)
  (h_sol : Matrix.mulVec (A.map (algebraMap k K)) x = fun i => algebraMap k K (b i))
  (π : K →ₗ[k] k)
  (h_proj : ∀ a : k, π (algebraMap k K a) = a) :
  Matrix.mulVec A (fun i => π (x i)) = b := by
  sorry





theorem theorem_194905_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (A : E →L[ℂ] E)
  (h_normal : Commute (Star.star A) A) :
  spectralRadius ℂ A = ENNReal.ofReal ‖A‖ := by
  sorry





theorem theorem_194593_problem (θ₁ θ₂ θ₃ : ℝ) :
  let c₁ := Real.cos θ₁
  let s₁ := Real.sin θ₁
  let c₂ := Real.cos θ₂
  let s₂ := Real.sin θ₂
  let c₃ := Real.cos θ₃
  let s₃ := Real.sin θ₃
  let Z₁ : Matrix (Fin 3) (Fin 3) ℝ := !![c₁, -s₁, 0; s₁, c₁, 0; 0, 0, 1]
  let Y₂ : Matrix (Fin 3) (Fin 3) ℝ := !![c₂, 0, s₂; 0, 1, 0; -s₂, 0, c₂]
  let X₃ : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, c₃, -s₃; 0, s₃, c₃]
  let R_target : Matrix (Fin 3) (Fin 3) ℝ := !![
    c₁ * c₂, c₁ * s₂ * s₃ - c₃ * s₁, s₁ * s₃ + c₁ * c₃ * s₂;
    c₂ * s₁, c₁ * c₃ + s₁ * s₂ * s₃, c₃ * s₁ * s₂ - c₁ * s₃;
    -s₂,     c₂ * s₃,                c₂ * c₃
  ]
  Z₁ * Y₂ * X₃ = R_target := by
  sorry

theorem theorem_194499_problem
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  (M : Submodule ℝ X)
  (f : M →L[ℝ] ℝ)
  (p : Seminorm ℝ X)
  (h : ∀ x : M, |f x| ≤ p x) :
  ∃ F : X →ₗ[ℝ] ℝ, (∀ x : M, F x = f x) ∧ (∀ x : X, |F x| ≤ p x) := by
  sorry



theorem theorem_194963_problem (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n)))
  (h_nonempty : C.Nonempty)
  (h_closed : IsClosed C)
  (h_convex : Convex ℝ C) :
  ∃ (I : Type) (a : I → EuclideanSpace ℝ (Fin n)) (b : I → ℝ),
    C = ⋂ i : I, {x | inner (a i) x ≤ b i} := by
  sorry



theorem theorem_195205_problem
  (n m : ℕ)
  (a : Fin m → Fin n → ℝ)
  (b : Fin m → ℝ)
  (x : Fin n → ℝ)
  (h_feas : ∀ i, Matrix.dotProduct (a i) x ≤ b i)
  (Ix : Set (Fin m))
  (hIx : Ix = {i | Matrix.dotProduct (a i) x = b i})
  (h_card : Ix.ncard = n)
  (h_indep : LinearIndependent ℝ (fun (i : Ix) ↦ a i)) :
  ∀ y : Fin n → ℝ, (∀ i ∈ Ix, Matrix.dotProduct (a i) y = b i) → y = x := by
  sorry

theorem theorem_194882_problem :
  ∀ M : ℝ, ∃ x₁ x₂ x₃ : ℝ,
    (2 * x₁ + x₂ + 3 * x₃ > 3) ∧
    (-x₁ + x₂ ≥ 1) ∧
    (-x₁ - 5 * x₂ + x₃ < 4) ∧
    (x₁ ≥ 0 ∧ x₂ ≥ 0 ∧ x₃ ≥ 0) ∧
    (x₁ + 3 * x₂ - x₃ < M) := by
  sorry













theorem theorem_195570_problem (n : ℕ) (V : Set (Fin n → ℝ)) (hV : IsCompact V) :
  IsCompact (convexHull ℝ V) := by
  sorry

theorem theorem_195743_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [CommRing R]
  (W : Matrix n n R)
  (z : Matrix (Fin 1) n R)
  (z' : Matrix n (Fin 1) R)
  (h : W * W = W) :
  z * W * z' = z * W * W * z' := by
  sorry

theorem theorem_195812_problem (n d : ℕ) (hn : n > 0)
  (x : Fin n → Fin d → ℝ)
  (x_bar : Fin d → ℝ)
  (h_x_bar : x_bar = (n : ℝ)⁻¹ • ∑ i, x i) :
  ∑ i, Matrix.vecMulVec (x i - x_bar) (x i - x_bar) =
  (∑ i, Matrix.vecMulVec (x i) (x i)) - (n : ℝ) • Matrix.vecMulVec x_bar x_bar := by
  sorry





theorem theorem_195762_problem (n : ℕ) (x y : Matrix (Fin n) (Fin 1) ℂ) :
  ((x.conjTranspose * y + y.conjTranspose * x) 0 0).re ≤ 
  ((x.conjTranspose * x + y.conjTranspose * y) 0 0).re := by
  sorry



















theorem theorem_195827_problem (z₁ z₂ : ℂ) (h : z₁ ≠ z₂) :
  {z : ℂ | ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ z = (1 - (t : ℂ)) * z₁ + (t : ℂ) * z₂} = segment ℝ z₁ z₂ := by
  sorry



theorem theorem_196021_problem 
  (e_plus e_minus : ℂ × ℂ)
  (h_indep : LinearIndependent ℂ ![e_plus, e_minus]) :
  FiniteDimensional.finrank ℝ (Submodule.span ℝ 
    { p : ℂ × ℂ | (p.1 • e_plus + p.2 • e_minus).1.im = 0 ∧ 
                  (p.1 • e_plus + p.2 • e_minus).2.im = 0 }) = 2 := by
  sorry







theorem theorem_196244_problem (z₁ z₂ z₃ a b : ℂ)
  (ha : a ≠ 0)
  (f : ℂ → ℂ → ℂ → ℂ)
  (hf : ∀ w₁ w₂ w₃, f w₁ w₂ w₃ = (w₁ - w₂) / (w₃ - w₂))
  (φ : ℂ → ℂ)
  (hφ : ∀ z, φ z = a * z + b) :
  f (φ z₁) (φ z₂) (φ z₃) = f z₁ z₂ z₃ := by
  sorry





theorem theorem_196486_problem (n : ℕ) (A : Set (Fin n → ℝ)) (hA : Convex ℝ A) :
  Convex ℝ (closure A) := by
  sorry

theorem theorem_195401_problem
  (d n m k l : ℕ)
  (U : Matrix (Fin d) (Fin n) ℝ)
  (W : Matrix (Fin d) (Fin m) ℝ)
  (X : Matrix (Fin d) (Fin k) ℝ)
  (Y : Matrix (Fin d) (Fin l) ℝ)
  (Z : Matrix (Fin d) (Sum (Fin k) (Fin l)) ℝ)
  (hX_range : LinearMap.range (Matrix.toLin' X) = LinearMap.ker (Matrix.toLin' U.transpose))
  (hX_indep : LinearMap.ker (Matrix.toLin' X) = ⊥)
  (hY_range : LinearMap.range (Matrix.toLin' Y) = LinearMap.ker (Matrix.toLin' W.transpose))
  (hY_indep : LinearMap.ker (Matrix.toLin' Y) = ⊥)
  (hZ : ∀ i j, Z i j = Sum.elim (X i) (Y i) j) :
  (LinearMap.range (Matrix.toLin' U)) ⊓ (LinearMap.range (Matrix.toLin' W)) =
  LinearMap.ker (Matrix.toLin' Z.transpose) := by
  sorry



theorem theorem_196498_problem
  {K V I : Type*}
  [Field K] [AddCommGroup V] [Module K V]
  (b : Basis I K V)
  (op : V → V → V) :
  ∀ i j : I, ∃! γ : I →₀ K, op (b i) (b j) = Finsupp.total I V K b γ := by
  sorry





theorem theorem_196701_problem
  (n : ℕ)
  (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (v_param : ℝ → EuclideanSpace ℝ (Fin n))
  (r : ℝ)
  (i : Fin n)
  (hv : Differentiable ℝ v)
  (hp : DifferentiableAt ℝ v_param r) :
  deriv (fun t => v (v_param t) i) r =
    inner (gradient (fun x => v x i) (v_param r)) (deriv v_param r) := by
  sorry



theorem theorem_196529_problem
  {R : Type*} [CommRing R]
  {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  (A₁ : Matrix m n R)
  (B : Matrix m m R)
  (hB : Invertible B) :
  (⅟B) * (Matrix.of (fun i => Sum.elim (A₁ i) ((1 : Matrix m m R) i))) =
  Matrix.of (fun i => Sum.elim ((⅟B * A₁) i) ((⅟B) i)) := by
  sorry

theorem theorem_196706_problem
  {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  (fn : ℕ → X → Y) (f : X → Y)
  (h_cont : ∀ n, Continuous (fn n))
  (h_unif : TendstoUniformly fn f Filter.atTop) :
  Continuous f := by
  sorry



theorem theorem_197395_problem
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  (M : ℝ) (hM : M > 0)
  (B : Set X) (hB : B = {x | ‖x‖ ≤ 1})
  (I : Set ℝ) (hI : I = Set.Icc 0 M)
  (S : Set X) (hS : S = {x | ‖x‖ ≤ M})
  (F : B × I → S)
  (hF : ∀ (p : B × I), (F p).val = p.2.val • p.1.val) :
  Continuous F := by
  sorry









theorem theorem_197311_problem
  {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  (v : Basis I K V)
  (A B : Set I)
  (hI : Infinite I)
  (h_disjoint : Disjoint A B)
  (h_union : A ∪ B = Set.univ)
  (σ : A ≃ B)
  (J : V →ₗ[K] V)
  (hJ_A : ∀ a : A, J (v a) = v (σ a))
  (hJ_B : ∀ b : B, J (v b) = - v (σ.symm b)) :
  J ^ 2 = - LinearMap.id := by
  sorry



theorem theorem_197627_problem (f : ℝ → ℝ) 
  (h : ∀ x, f x = Real.cos (x ^ 3) / x) : 
  UniformContinuousOn f (Set.Ici 1) := by
  sorry







theorem theorem_197858_problem 
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (x₀ : E) (r : ℝ) (hr : r > 0) :
  let B_unit := Metric.ball (0 : E) 1
  let B_xr := Metric.ball x₀ r
  let φ : E → E := fun y ↦ x₀ + r • y
  ∃ (e : B_unit ≃ₜ B_xr), ∀ (y : B_unit), (e y : E) = φ y := by
  sorry

