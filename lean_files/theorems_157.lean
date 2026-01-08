import Mathlib
import Mathlib.Tactic







theorem theorem_853668_problem
  (f : ℝ × ℝ → ℝ)
  (g : ℝ → ℝ)
  (hf : Differentiable ℝ f)
  (hg : Differentiable ℝ g)
  (h : ℝ → ℝ)
  (h_def : ∀ x, h x = f (x, g x)) :
  ∀ x, deriv h x = deriv (fun u ↦ f (u, g x)) x + deriv (fun v ↦ f (x, v)) (g x) * deriv g x := by
  sorry

theorem theorem_853567_problem
  (X Y : Type*) [MetricSpace X] [MetricSpace Y] [CompleteSpace Y]
  (f : X → Y) (hf : UniformContinuous f) :
  ∃! g : UniformSpace.Completion X → Y,
    Continuous g ∧ ∀ x : X, g (x : UniformSpace.Completion X) = f x := by
  sorry

theorem theorem_853533_problem
  {Formula : Type*}
  (ProvableN : Formula → Prop)
  (ProvableH : Formula → Prop)
  (Valid : Formula → Prop)
  (h_N_sound_complete : ∀ ϕ, ProvableN ϕ ↔ Valid ϕ)
  (h_H_sound_complete : ∀ ϕ, ProvableH ϕ ↔ Valid ϕ)
  (ϕ : Formula) :
  ProvableN ϕ ↔ ProvableH ϕ := by
  sorry



theorem theorem_854024_problem
  (T : ℝ) (hT : T > 0)
  (f : ℝ → ℝ)
  (h_per : Function.Periodic f T)
  (h_series : ∃ (N : ℕ) (c : ℤ → ℂ),
    (∀ n : ℤ, abs n > N → c n = 0) ∧
    (∀ x : ℝ, (f x : ℂ) = ∑ n in Finset.Icc (-(N : ℤ)) (N : ℤ), c n * Complex.exp (2 * Real.pi * Complex.I * n * x / T))) :
  ∃ (N : ℕ) (a₀ : ℝ) (a b : ℕ → ℝ),
    ∀ x : ℝ, f x = a₀ + ∑ n in Finset.Icc 1 N, (a n * Real.cos (2 * Real.pi * n * x / T) + b n * Real.sin (2 * Real.pi * n * x / T)) := by
  sorry





theorem theorem_854248_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [Nontrivial E]
  (A : E →L[𝕜] E)
  (h : ¬ IsUnit (1 + A)) :
  1 ≤ ‖A‖ := by
  sorry

theorem theorem_853917_problem (y1 y2 y3 b C y : ℝ)
  (h_roots : ∀ x : ℝ, x^3 - 12 * x^2 - 6 * x + 4/5 = (x - y1) * (x - y2) * (x - y3))
  (h_distinct : y1 ≠ y2 ∧ y1 ≠ y3 ∧ y2 ≠ y3)
  (hb : b ≠ 0)
  (hy : y ≠ y1 ∧ y ≠ y2 ∧ y ≠ y3) :
  deriv (fun y => - (81 / (5 * b)) * (
      (Real.log (abs (y - y1))) / ((y1 - y2) * (y1 - y3)) -
      (Real.log (abs (y - y2))) / ((y1 - y2) * (y2 - y3)) -
      (Real.log (abs (y - y3))) / ((y1 - y3) * (y3 - y2))
    ) + C) y =
  - (81 / (5 * b)) * (1 / ((y - y1) * (y - y2) * (y - y3))) := by
  sorry

theorem theorem_854333_problem (a b : ℝ) (n : ℕ) :
  (a - b) ^ n = ∑ k in Finset.range (n + 1), (-1 : ℝ) ^ k * (Nat.choose n k) * a ^ (n - k) * b ^ k := by
  sorry



theorem theorem_854187_problem (n : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2))
  (e : Fin n → Fin n → ZMod 2)
  (he : ∀ i, e i = Pi.single i 1) :
  (∀ u v : Fin n → ZMod 2, Matrix.dotProduct u (Matrix.mulVec M v) = - Matrix.dotProduct v (Matrix.mulVec M u)) ↔
  (∀ i j : Fin n, Matrix.dotProduct (e i) (Matrix.mulVec M (e j)) = - Matrix.dotProduct (e j) (Matrix.mulVec M (e i))) := by
  sorry

theorem theorem_854110_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (A : E → ℝ) (x₀ h : E)
  (hA : ContDiff ℝ ⊤ A)
  (t s₁ s₂ s₃ : ℝ) :
  let B : ℝ → E := fun t ↦ x₀ + t • h
  let f : ℝ → ℝ := fun t ↦ A (B t)
  iteratedFDeriv ℝ 3 f t ![s₁, s₂, s₃] =
  iteratedFDeriv ℝ 3 A (B t) ![s₁ • h, s₂ • h, s₃ • h] := by
  sorry



theorem theorem_854474_problem (x : ℝ) (hx : x ≠ 0) :
  HasDerivAt (fun x => -1 / x - (3 * Real.arctan x) / 2 - x / (2 * (1 + x^2)))
    (1 / (x^2 * (x^2 + 1)^2)) x := by
  sorry

theorem theorem_854422_problem (x₁ x₂ x₃ : ℂ)
  (e₁ e₂ e₃ p₃ : ℂ)
  (h_e1 : e₁ = x₁ + x₂ + x₃)
  (h_e2 : e₂ = x₁ * x₂ + x₂ * x₃ + x₃ * x₁)
  (h_e3 : e₃ = x₁ * x₂ * x₃)
  (h_p3 : p₃ = x₁^3 + x₂^3 + x₃^3) :
  (1 / 3 : ℂ) * (x₁ + x₂ + x₃)^3 - 2 * x₁ * x₂ * x₃ - (1 / 3 : ℂ) * (x₁^3 + x₂^3 + x₃^3) =
  (1 / 3 : ℂ) * e₁^3 - 2 * e₃ - (1 / 3 : ℂ) * p₃ := by
  sorry









theorem theorem_854190_problem (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (B : Matrix (Fin n) (Fin n) ℝ)
  (hB : IsUnit B.det) :
  (Matrix.fromBlocks 0 A A.transpose B).det =
    (-1 : ℝ) ^ m * (A * B⁻¹ * A.transpose).det * B.det := by
  sorry





theorem theorem_855094_problem 
  (Statement : Type)
  (provable : Statement → Prop)
  (is_true : Statement → Prop)
  (h_sound : ∀ s : Statement, provable s → is_true s)
  (phi : Statement)
  (h_prov : provable phi) :
  is_true phi := by
  sorry









theorem theorem_855306_problem (p : ℕ) [Fact p.Prime]
  (a b : (ZMod p)ˣ)
  (h k : ℕ)
  (hk_def : orderOf b = k)
  (hh_def : orderOf (a * b) = h) :
  a ^ (h * k) = 1 := by
  sorry



theorem theorem_855123_problem 
  (phi psi : ℝ → ℝ) 
  (t1 t2 a1 a2 : ℝ) 
  (h_diff : t1 ≠ t2)
  (h_phi : phi 0 = 1) 
  (h_psi : psi 0 = 0) : 
  (∃! B : ℝ, (a1 * phi (t1 - t1) + B * psi (t1 - t1) = a1) ∧ 
             (a1 * phi (t2 - t1) + B * psi (t2 - t1) = a2)) ↔ 
  psi (t2 - t1) ≠ 0 := by
  sorry









theorem theorem_855118_problem
  -- Predicates representing the balance conditions at each order derived from F
  (is_dominant_balance : ℝ → Prop)
  (is_second_balance : ℝ → ℝ → Prop)
  (is_third_balance : ℝ → ℝ → ℝ → Prop)
  -- Hypothesis: The dominant term condition determines a unique α
  (h_dom : ∃! α, is_dominant_balance α)
  -- Hypothesis: Given α, the next order terms determine a unique β > α
  (h_second : ∀ α, is_dominant_balance α → ∃! β, α < β ∧ is_second_balance α β)
  -- Hypothesis: Given α and β, the higher order terms determine a unique γ > β
  (h_third : ∀ α β, is_dominant_balance α → is_second_balance α β → 
    ∃! γ, β < γ ∧ is_third_balance α β γ) :
  -- Conclusion: There exists a unique set (tuple) of values
  ∃! p : ℝ × ℝ × ℝ, 
    is_dominant_balance p.1 ∧ 
    is_second_balance p.1 p.2.1 ∧ 
    is_third_balance p.1 p.2.1 p.2.2 ∧ 
    p.1 < p.2.1 ∧ p.2.1 < p.2.2 := by
  sorry



theorem theorem_855622_problem
  {D : Type*} [CommMonoid D]
  (f_dim : D)
  (var_dims : List D)
  (calc_integral_dim : D → List D → D)
  (h_base : ∀ d, calc_integral_dim d [] = d)
  (h_step : ∀ d x xs, calc_integral_dim d (x :: xs) = calc_integral_dim (d * x) xs) :
  calc_integral_dim f_dim var_dims = f_dim * var_dims.prod := by
  sorry





theorem theorem_854189_problem :
  ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) = π / 4 := by
  sorry

theorem theorem_855675_problem (m n : ℕ)
  (C' : Matrix (Fin m) (Fin n) ℝ)
  (D : Matrix (Fin m) (Fin m) ℝ)
  (hD_diag : ∀ i j, i ≠ j → D i j = 0)
  (hD_entries : ∀ i, D i i = 0 ∨ D i i = 1)
  (C : Matrix (Fin m) (Fin n) ℝ)
  (hC : C = D * C') :
  ∀ i, (D i i = 1 → C i = C' i) ∧ (D i i = 0 → C i = 0) := by
  sorry





theorem theorem_856109_problem (f : ℝ → ℝ)
  (h_eq : ∀ x, f (2 * x) = 2 * (f x)^2 - 1)
  (h_bound : ∃ X > 0, ∀ x, x ≥ X → |f x| < 1/2) :
  False := by
  sorry



theorem theorem_856202_problem (r A : ℝ → ℝ) (V : ℝ)
  (hr : ∀ z, r z = 1 / (z + 1))
  (hA : ∀ z, A z = Real.pi * (r z) ^ 2)
  (hV : V = ∫ z in (0 : ℝ)..1, A z) :
  V = Real.pi / 2 := by
  sorry

theorem theorem_856452_problem (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
  Set.Infinite { S : Finset ℕ | (∀ x ∈ S, 0 < x) ∧ (∑ x in S, (1 : ℚ) / x) = (a : ℚ) / b } := by
  sorry



theorem theorem_855759_problem
  (f : ℝ → ℝ) (m₁ m₂ b₁ b₂ x₁ x₂ : ℝ) (P Q : ℝ × ℝ)
  (h_parabola : ∃ a b c : ℝ, a ≠ 0 ∧ ∀ x, f x = a * x^2 + b * x + c)
  (h_distinct : m₁ ≠ m₂)
  (h_deriv₁ : deriv f x₁ = m₁)
  (h_deriv₂ : deriv f x₂ = m₂)
  (hP : P.2 = m₁ * (P.1 - x₁) + f x₁ ∧ P.2 = m₂ * (P.1 - x₂) + f x₂)
  (hQ : Q.2 = m₁ * Q.1 + b₁ ∧ Q.2 = m₂ * Q.1 + b₂) :
  let Δx := Q.1 - P.1
  let Δy := Q.2 - P.2
  let g := fun x ↦ f (x - Δx) + Δy
  (∃ t₁, deriv g t₁ = m₁ ∧ g t₁ = m₁ * t₁ + b₁) ∧
  (∃ t₂, deriv g t₂ = m₂ ∧ g t₂ = m₂ * t₂ + b₂) := by
  sorry





theorem theorem_856966_problem (f : ℂ → ℂ)
  (h : ∀ z, z ≠ 0 → f z = z + 1 / z) :
  DifferentiableOn ℂ f {z | z ≠ 0} := by
  sorry

theorem theorem_856960_problem 
  {α : Type*} [Fintype α] [DecidableEq α] 
  (Q : Finset (Finset α)) : 
  sInf {n : ℕ | ∃ x : α → ℕ, (∀ v, x v ≤ 1) ∧ (∀ q ∈ Q, 1 ≤ ∑ v in q, x v) ∧ ∑ v, x v = n} = 
  sInf {n : ℕ | ∃ S : Finset α, (∀ q ∈ Q, (q ∩ S).Nonempty) ∧ S.card = n} := by
  sorry





theorem theorem_857083_problem 
  {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [CommRing R]
  (Tp Tz S Rx Ry : Matrix n n R)
  (hTp : Invertible Tp)
  (hTz : Invertible Tz) :
  let step1 := Tp⁻¹
  let step2 := Tz⁻¹
  let step3 := S
  let step4 := Ry * Rx
  let step5 := Tz
  -- The resulting matrix M is the composition of steps 1 through 5.
  -- Applying transformations sequentially (A then B) corresponds to matrix multiplication (B * A).
  let M := step5 * step4 * step3 * step2 * step1
  M = Tz * (Ry * Rx) * S * Tz⁻¹ * Tp⁻¹ := by
  sorry











theorem theorem_857246_problem (k : ℝ) (hk : k > 0)
  (a : ℕ → ℝ) (h_def : ∀ n, a n = k ^ (Nat.fib n)) :
  ∀ n, a (n + 2) = a (n + 1) * a n := by
  sorry

theorem theorem_857360_problem
  (Sentence : Type)
  (FormulaOneFreeVar : Type)
  (code : Sentence → ℕ)
  (models : Sentence → Prop)
  (satisfies : FormulaOneFreeVar → ℕ → Prop)
  (is_second_order_definable : Set ℕ → Prop)
  (h_def : ∀ S : Set ℕ, is_second_order_definable S ↔
    ∃ φ : FormulaOneFreeVar, ∀ n : ℕ, n ∈ S ↔ satisfies φ n) :
  ¬ is_second_order_definable {n | ∃ φ : Sentence, code φ = n ∧ models φ} := by
  sorry

theorem theorem_857451_problem
  {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
  (A : Matrix m n ℝ) (B : Matrix n p ℝ)
  (h : B.rank = (A * B).rank) :
  LinearMap.ker (Matrix.toLin' B) = LinearMap.ker (Matrix.toLin' (A * B)) := by
  sorry







theorem theorem_857543_problem 
  (xA yA zA xB yB zB xC yC zC xP yP zP : ℝ)
  (dA dB dC : ℝ)
  (h_dA_pos : 0 < dA)
  (h_dB_pos : 0 < dB)
  (h_dC_pos : 0 < dC)
  (h_distA : dA = Real.sqrt ((xP - xA)^2 + (yP - yA)^2 + (zP - zA)^2))
  (h_distB : dB = Real.sqrt ((xP - xB)^2 + (yP - yB)^2 + (zP - zB)^2))
  (h_distC : dC = Real.sqrt ((xP - xC)^2 + (yP - yC)^2 + (zP - zC)^2)) :
  ((xP - xA)^2 + (yP - yA)^2 + (zP - zA)^2 = dA^2) ∧ 
  ((xP - xB)^2 + (yP - yB)^2 + (zP - zB)^2 = dB^2) ∧ 
  ((xP - xC)^2 + (yP - yC)^2 + (zP - zC)^2 = dC^2) := by
  sorry

theorem theorem_857319_problem
  {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  (S : ℕ → Set X) (hS : ∀ n, IsOpen (S n)) :
  interior (⋂ n, closure (S n)) = interior (closure (⋂ n, S n)) := by
  sorry

theorem theorem_857532_problem (a₁ b₁ a₂ b₂ : ℝ)
  (ha : a₁ ≤ b₁) (hb : a₂ ≤ b₂)
  (f : ℝ × ℝ → ℝ × ℝ)
  (hf : ContinuousOn f (Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂))
  (h1 : ∀ y ∈ Set.Icc a₂ b₂, (f (a₁, y)).1 ≤ 0)
  (h2 : ∀ y ∈ Set.Icc a₂ b₂, 0 ≤ (f (b₁, y)).1)
  (h3 : ∀ x ∈ Set.Icc a₁ b₁, (f (x, a₂)).2 ≤ 0)
  (h4 : ∀ x ∈ Set.Icc a₁ b₁, 0 ≤ (f (x, b₂)).2) :
  ∃ x ∈ Set.Icc a₁ b₁, ∃ y ∈ Set.Icc a₂ b₂, f (x, y) = 0 := by
  sorry

theorem theorem_857675_problem
  (R : Type*) [Ring R]
  (A : Type*) [AddCommGroup A] [Module R A]
  (ι : Type*) [DecidableEq ι]
  (S : ι → Submodule R A)
  (h_internal : DirectSum.IsInternal S)
  (h_cyclic : ∀ i, ∃ x, S i = Submodule.span R {x})
  (j : ι)
  (B : Submodule R A)
  (hB : B = S j) :
  ∃ C : Submodule R A, IsCompl B C := by
  sorry



theorem theorem_857408_problem
  (X : Type*)
  [MeasurableSpace X]
  (h_pow : ∀ s : Set X, MeasurableSet s)
  (h_uncountable : ¬ Set.Countable (Set.univ : Set X))
  (P : MeasureTheory.Measure X)
  [MeasureTheory.IsProbabilityMeasure P]
  (h_pos : ∀ x : X, P {x} > 0) :
  False := by
  sorry











theorem theorem_857668_problem
  (φ : ℝ → ℝ)
  (x y : ℝ)
  (h_conv : ConvexOn ℝ Set.univ φ)
  (h_lt : y < φ x) :
  ∃ a b : ℝ, (a * x + b = y) ∧ (∀ t : ℝ, a * t + b < φ t) := by
  sorry



theorem theorem_857954_problem (y u : ℝ → ℝ) (t : ℝ)
  (hy : DifferentiableAt ℝ y t) (hu : DifferentiableAt ℝ u t)
  (ht : t ≠ 0) (hs : Real.sinh (u t) ≠ 0)
  (h1 : deriv y t = t * Real.sinh (u t))
  (h2 : y t = Real.sqrt ((2 : ℝ) / 3) * t * Real.cosh (u t)) :
  deriv u t = Real.sqrt ((3 : ℝ) / 2) - (Real.cosh (u t)) / (t * Real.sinh (u t)) := by
  sorry

theorem theorem_857939_problem
  (U : ℝ → ℝ → ℝ)
  (h_diff : Differentiable ℝ (fun p : ℝ × ℝ ↦ U p.1 p.2))
  (h_pde : ∀ x y : ℝ, x * (deriv (fun t ↦ U t y) x) - y * (deriv (fun t ↦ U x t) y) = x^2 * y + x * U x y) :
  ∃ F : ℝ → ℝ, Differentiable ℝ F ∧ ∀ x y : ℝ, U x y = Real.exp x * F (x * y) - x * y := by
  sorry



theorem theorem_858032_problem
  (a : ℕ → ℝ)
  (S : ℝ)
  (S_N : ℕ → ℝ)
  (hS_def : ∀ N, S_N N = ∑ n in Finset.Icc 1 N, a n)
  (h_conv : Filter.Tendsto S_N Filter.atTop (nhds S))
  (T : ℕ → ℝ)
  (hT_def : ∀ N, T N = ∑ k in Finset.Icc 1 N, (1 - (k : ℝ) / (N : ℝ)) * a k) :
  Filter.Tendsto T Filter.atTop (nhds S) := by
  sorry

theorem theorem_858464_problem (n : ℕ) (x : ℝ) :
  iteratedDeriv n f x =
  ((-1 : ℝ) ^ n * (n.factorial : ℝ) / ((x ^ 2 + 1) ^ (n + 1))) *
  (∑ k in Finset.range (n / 2 + 1),
    (-1 : ℝ) ^ k * ((n + 1).choose (2 * k + 1) : ℝ) * x ^ (n - 2 * k)) := by
  sorry

theorem theorem_858785_problem (K L : Type*) [Field K] [AddCommGroup L] [Module K L]
  (m : L →ₗ[K] L →ₗ[K] L) (δ : L →ₗ[K] L)
  (is_derivation : (L →ₗ[K] L →ₗ[K] L) → (L →ₗ[K] L) → Prop)
  (h_def : ∀ (m' : L →ₗ[K] L →ₗ[K] L) (d : L →ₗ[K] L),
    is_derivation m' d ↔ ∀ a b, d (m' a b) = m' (d a) b + m' a (d b)) :
  is_derivation m δ ↔ ∀ a b, δ (m a b) = m (δ a) b + m a (δ b) := by
  sorry





theorem theorem_858813_problem {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (A B : ExteriorAlgebra R M) (k l : ℕ)
  (hA : ∃ L : List M, L.length = k ∧ A = (L.map (ExteriorAlgebra.ι R)).prod)
  (hB : ∃ L : List M, L.length = l ∧ B = (L.map (ExteriorAlgebra.ι R)).prod) :
  ∃ L : List M, L.length = k + l ∧ A * B = (L.map (ExteriorAlgebra.ι R)).prod := by
  sorry





theorem theorem_859120_problem
  {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  (f : X → Y) (hf : Function.Bijective f)
  (h_lip_f : ∃ K, LipschitzWith K f)
  (h_lip_inv : ∃ K, LipschitzWith K (Function.surjInv hf.surjective)) :
  Nonempty (X ≃ₜ Y) := by
  sorry

theorem theorem_858490_problem 
  (C : ℕ → ℝ → ℝ) 
  (n : ℝ → ℕ) 
  (a : ℝ) (ha : a > 0)
  -- Condition 1: The cost C_k satisfies the lower bound derived from 
  -- the failure probability P_k ≤ a/√T and signal decay μ_k = 2⁻ᵏ.
  (h_cost : ∃ c > 0, ∀ k, ∀ᶠ T in atTop, C k T ≥ c * (4 : ℝ)^k * Real.log T)
  -- Condition 2: Any valid strategy must perform at least logarithmically many guesses
  -- to avoid catastrophic loss (resolving the uncertainty).
  (h_strat : ∀ᶠ T in atTop, (n T : ℝ) ≥ Real.log T / Real.log 2) :
  -- Conclusion: The total expected payment is not bounded by O(√T).
  ¬ (fun T => ∑ k in Finset.Icc 1 (n T), C k T) =O[atTop] (fun T => Real.sqrt T) := by
  sorry

theorem theorem_859272_problem (z : ℂ) (δ : ℝ)
  (h1 : 0 < δ) (h2 : δ < 1)
  (h3 : Complex.abs (z - Complex.I) < δ) :
  Complex.abs (z + Complex.I) < 3 := by
  sorry





