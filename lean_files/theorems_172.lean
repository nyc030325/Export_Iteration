import Mathlib
import Mathlib.Tactic



theorem theorem_940750_problem (n : ℕ) (a d r : ℝ) (h : r ≠ 1) :
  ∑ k in Finset.range n, (a + (k : ℝ) * d) * r ^ k =
  a / (1 - r) + (d * r) / ((1 - r) ^ 2) - (d * r ^ n) / ((1 - r) ^ 2) -
  ((a + ((n : ℝ) - 1) * d) * r ^ n) / (1 - r) := by
  sorry

theorem theorem_940926_problem
  (X : Type*)
  (t1 t2 : TopologicalSpace X)
  (h : ∀ (A : Type*) [Preorder A] [IsDirected A (· ≤ ·)] [Nonempty A] (x : A → X) (s : X),
    Filter.Tendsto x Filter.atTop (@nhds X t1 s) ↔
    Filter.Tendsto x Filter.atTop (@nhds X t2 s)) :
  t1 = t2 := by
  sorry

theorem theorem_940611_problem
  (n : ℕ)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (u : Fin (n + 1) → V)
  (f : Fin n → V)
  (h_indep : LinearIndependent ℝ u) :
  ∃ α : Fin (n + 1) → ℝ,
    α ≠ 0 ∧
    let g := ∑ i, α i • u i
    g ≠ 0 ∧ ∀ j : Fin n, ⟪g, f j⟫_ℝ = 0 := by
  sorry

theorem theorem_937017_problem
  (Ω : Type*) [MeasurableSpace Ω]
  (X : Set.Icc (0 : ℝ) 1 → Ω → ℝ)
  (hX : ∀ t, Measurable (X t)) :
  Measurable (fun ω => ⨆ t, X t ω) := by
  sorry









theorem theorem_941105_problem 
  -- Abstract types for Processes and Differentials
  {Process : Type*} [CommRing Process] [Algebra ℝ Process]
  {Differential : Type*} [AddCommGroup Differential] [Module ℝ Differential]
  -- The differential operator d
  (d : Process → Differential)
  -- The deterministic time differential dt
  (dt : Differential)
  -- Operation representing Process * Differential (e.g., B * dB)
  (proc_mul_diff : Process → Differential → Differential)
  -- Problem variables
  (n : ℕ)
  (B : Fin n → Process)
  -- Predicates for conditions (Independence and Brownian Motion)
  (IsStandardBrownianMotion : Process → Prop)
  (IsIndependent : (Fin n → Process) → Prop)
  -- Hypotheses from the problem statement
  (h_bm : ∀ i, IsStandardBrownianMotion (B i))
  (h_indep : IsIndependent B)
  -- Definition of X
  (X : Process)
  (hX : X = ∑ i, (B i)^2) :
  -- Conclusion: The stochastic differential equation
  d X = (∑ i, proc_mul_diff (2 * B i) (d (B i))) + (n : ℝ) • dt := by
  sorry









theorem theorem_941577_problem
  (u v : ℝ → ℝ)
  (f : ℝ × ℝ → ℝ)
  (x : ℝ)
  (hu : Differentiable ℝ u)
  (hv : Differentiable ℝ v)
  (hf : Differentiable ℝ f) :
  deriv (fun t => f (u t, v t)) x =
  deriv (fun a => f (a, v x)) (u x) * deriv u x +
  deriv (fun b => f (u x, b)) (v x) * deriv v x := by
  sorry

theorem theorem_941793_problem (a b n : ℝ) (h : a + b > 0) :
  deriv (fun x ↦ (a + b) ^ x) n = (a + b) ^ n * Real.log (a + b) := by
  sorry

theorem theorem_942069_problem
  (J : ℕ) (hJ : 0 < J)
  (θ : Fin J → ℝ)
  -- f represents the PDF of a Normal distribution f(x; μ, 1) taking mean μ and value x
  (normal_pdf : ℝ → ℝ → ℝ)
  -- Condition: w_j = 1/J
  (w : Fin J → ℝ)
  (hw : ∀ j, w j = 1 / (J : ℝ))
  -- Condition: g(x) is defined as the mixture sum
  (g : ℝ → ℝ)
  (hg : ∀ x, g x = ∑ j, w j * normal_pdf (θ j) x)
  -- Condition: Algorithm Step 1 (Uniform selection of index)
  (prob_select : Fin J → ℝ)
  (h_prob : ∀ j, prob_select j = 1 / (J : ℝ))
  -- Condition: Algorithm Step 2 (Conditional generation from Normal)
  (pdf_cond : Fin J → ℝ → ℝ)
  (h_cond : ∀ j x, pdf_cond j x = normal_pdf (θ j) x)
  -- Condition: The resulting variable has a PDF derived from the steps (Law of Total Probability)
  (alg_pdf : ℝ → ℝ)
  (h_alg : ∀ x, alg_pdf x = ∑ j, prob_select j * pdf_cond j x) :
  -- Question: Prove the resulting PDF is g(x)
  alg_pdf = g := by
  sorry

theorem theorem_941065_problem (a b c k₁ k₂ θ : ℂ)
  (h_a : a = Complex.exp (Complex.I * k₁))
  (h_b : b = Complex.exp (Complex.I * k₂))
  (h_c : c = Complex.exp (Complex.I * θ))
  (h_a_ne : a ≠ 1)
  (h_b_ne : b ≠ 1)
  (h_c_ne : c ≠ 1)
  (h_denom : a * b + 1 - 2 * b ≠ 0)
  (h_cond : c = -(a * b + 1 - 2 * a) / (a * b + 1 - 2 * b)) :
  2 * Complex.cot (θ / 2) = Complex.cot (k₁ / 2) - Complex.cot (k₂ / 2) := by
  sorry





theorem theorem_940936_problem (n : ℕ) (p : Fin n → ℝ)
  (h_bounds : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
  (h_equal : ∀ (x y : Fin n → Bool),
    (∏ i, if x i then p i else (1 - p i)) = (∏ i, if y i then p i else (1 - p i))) :
  ∀ i, p i = 1 / 2 := by
  sorry

theorem theorem_941303_problem (a : ℝ) (h1 : a ≠ 1) (h2 : a ≠ -1) :
  ∀ x : ℝ, HasDerivAt (fun x =>
    (1 / 2) * (
      (1 / (a - 1) ^ 2) * (Real.sin ((a - 1) * x) - (a - 1) * x * Real.cos ((a - 1) * x)) +
      (1 / (a + 1) ^ 2) * (Real.sin ((a + 1) * x) - (a + 1) * x * Real.cos ((a + 1) * x))
    )
  ) (x * Real.sin (a * x) * Real.cos x) x := by
  sorry





theorem theorem_941839_problem (x : ℕ → ℝ) (L M N : ℝ)
  (h1 : Filter.Tendsto (fun n ↦ x (3 * n)) Filter.atTop (nhds L))
  (h2 : Filter.Tendsto (fun n ↦ x (3 * n + 1)) Filter.atTop (nhds M))
  (h3 : Filter.Tendsto (fun n ↦ x (3 * n + 2)) Filter.atTop (nhds N))
  (h_eq : L = M ∧ M = N) :
  Filter.Tendsto x Filter.atTop (nhds L) := by
  sorry



theorem theorem_941104_problem (r θ ab_length : ℝ)
  (h_r : r = Real.sqrt 3 / 2)
  (h_θ : θ = 2 * Real.pi - 5 * Real.arccos (1 / 3))
  (h_ab : ab_length = 2 * r * Real.sin (θ / 2)) :
  ab_length = 1 / 9 := by
  sorry

theorem theorem_942157_problem
  {n : ℕ} {R : Type*} [CommRing R]
  (K : Matrix (Fin n) (Fin n) R)
  (η : R)
  (ones : Fin n → R)
  (h_ones : ones = fun _ ↦ 1) :
  η * Matrix.dotProduct ones (Matrix.mulVec K ones) =
  Matrix.trace (K * (η • Matrix.vecMulVec ones ones)) := by
  sorry





theorem theorem_942576_problem :
  ∃ (X Y : Type*) (tX : TopologicalSpace X) (tY : TopologicalSpace Y) (f : X → Y),
    CompactSpace X ∧ PathConnectedSpace X ∧
    CompactSpace Y ∧ T2Space Y ∧
    ¬ Continuous f := by
  sorry



theorem theorem_942276_problem
  {X : Type*} [TopologicalSpace X]
  (T : TopologicalSpace ℝ)
  (f : X → ℝ)
  (h : ∃ c : ℝ, ∀ x : X, f x = c) :
  @Continuous X ℝ _ T f := by
  sorry

theorem theorem_942265_problem :
  ∃ (V : Type) (E : V → V → Prop) (v₀ : V) (t₁ t₂ : List V),
    t₁.head? = some v₀ ∧ t₂.head? = some v₀ ∧
    List.Chain' E t₁ ∧ List.Chain' E t₂ ∧
    (t₁.zip t₁.tail).Nodup ∧ (t₂.zip t₂.tail).Nodup ∧
    (∀ v, t₁.getLast? = some v → ∀ u, E v u → (v, u) ∈ t₁.zip t₁.tail) ∧
    (∀ v, t₂.getLast? = some v → ∀ u, E v u → (v, u) ∈ t₂.zip t₂.tail) ∧
    t₁.getLast? ≠ t₂.getLast? := by
  sorry

theorem theorem_942366_problem
  {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
  (A : ι → Finset α) :
  ((Finset.univ \ Finset.biUnion Finset.univ A).card : ℤ) =
  ∑ J in Finset.univ.powerset, (-1 : ℤ) ^ J.card * ((Finset.inf J A).card : ℤ) := by
  sorry







theorem theorem_942763_problem (k E : Type*) [Field k] [Field E] [Algebra k E]
  (h : Algebra.FiniteType k E) :
  Module.Finite k E := by
  sorry

theorem theorem_941823_problem (a : ℕ → ℝ)
  (h_summable : Summable a)
  (h_eq : ∀ n, a n = ∑' k, if n < k then (a k)^2 else 0) :
  ∀ n, a n = 0 := by
  sorry

theorem theorem_942949_problem
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix m n ℝ) :
  LinearMap.range (Matrix.toLin' A) = LinearMap.range (Matrix.toLin' (A * A.transpose)) := by
  sorry

theorem theorem_942656_problem (n : ℕ) (d : ℕ → ℝ) (h : n ≥ 1) :
  ∑ k in Finset.Icc 1 n, ∑ j in Finset.Icc 1 k, d j =
  ∑ k in Finset.range n, ((n : ℝ) - (k : ℝ)) * d (k + 1) := by
  sorry









theorem theorem_942677_problem
  (f g : ℕ → ℝ)
  (hf : ∀ n, f n = (2 : ℝ) ^ ((n : ℝ) ^ 2 + n))
  (hg : ∀ n, g n = (2 : ℝ) ^ ((12 + Real.logb 2 n) * n)) :
  Filter.Tendsto (fun n ↦ f n / g n) Filter.atTop Filter.atTop := by
  sorry

theorem theorem_943493_problem (S : Set (ℝ × ℝ))
  (hS : S = {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ p.1 + p.2 ≤ 1}) :
  MeasurableSet S := by
  sorry

theorem theorem_942464_problem
  (f : ℝ → ℝ → ℝ → ℝ)
  (h : ℝ → ℝ → ℝ)
  (u v w : ℝ → ℝ)
  (hf : ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ ↦ f p.1 p.2.1 p.2.2))
  (hh : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ h p.1 p.2))
  (hu : ContDiff ℝ 1 u)
  (hv : ContDiff ℝ 1 v)
  (hw : ContDiff ℝ 1 w)
  (h_eq : ∀ x y z, f x y z = h y (x + z) + u x + v y + w (x + z) + v (y + z)) :
  ∃ θ₁ θ₂ θ₃ θ₄ : ℝ → ℝ,
    ContDiff ℝ 1 θ₁ ∧
    ContDiff ℝ 1 θ₂ ∧
    ContDiff ℝ 1 θ₃ ∧
    ContDiff ℝ 1 θ₄ ∧
    ∀ x y z, f x y z = θ₁ x + θ₂ y + θ₃ z + θ₄ (x + y + z) := by
  sorry

theorem theorem_943076_problem
  (exp : ℝ → ℝ)
  (h_exp : ∀ x : ℝ, Filter.Tendsto (fun (n : ℕ) ↦ (1 + x / (n : ℝ)) ^ n) Filter.atTop (nhds (exp x)))
  (x y : ℝ) :
  exp (x + y) = exp x * exp y := by
  sorry







theorem theorem_943242_problem (a b : ℝ) (f : ℝ → ℝ)
  (h1 : a < b)
  (h2 : ContinuousOn f (Set.Icc a b))
  (h3 : DifferentiableOn ℝ f (Set.Ioo a b)) :
  ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a) := by
  sorry









theorem theorem_943480_problem :
  ∫ (z : ℂ), Real.exp (- Complex.normSq z) ∂volume = Real.pi := by
  sorry





theorem theorem_943613_problem (n : ℕ) (hn : n ≠ 0) :
  IsCompact {x : Fin n → ℝ | (∀ i, |x i| ≤ 1) ∧ (∃ i, |x i| = 1)} := by
  sorry





theorem theorem_943619_problem :
  ∃ (X : Type) (t : TopologicalSpace X) (S : Set X),
    @closure X t (@interior X t S) ≠ @closure X t S := by
  sorry

theorem theorem_943656_problem
  (K F : Type*) [Field K] [Field F] [Algebra K F]
  (eta : F)
  (h : FiniteDimensional.finrank K (IntermediateField.adjoin K {eta}) = 5) :
  IntermediateField.adjoin K {eta^2} = IntermediateField.adjoin K {eta} := by
  sorry

theorem theorem_943836_problem (α β s : ℝ)
  (hα : 0 < α) (hβ : 0 < β) (hs : -β < s) :
  ∫ x in Set.Ioi 0, Real.exp (-s * x) * (β ^ α / Real.Gamma α * x ^ (α - 1) * Real.exp (-β * x)) =
  β ^ α / (s + β) ^ α := by
  sorry

theorem theorem_944069_problem
  {X Y : Type*}
  [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y]
  (f : X ≃ₜ Y)
  (A : Set X)
  (hA : MeasurableSet A) :
  MeasurableSet (f '' A) := by
  sorry





theorem theorem_943862_problem (r s t m n p : Fin 3) :
  let delta := fun (i j : Fin 3) => if i = j then (1 : ℤ) else 0
  let eps := fun (a b c : Fin 3) => Matrix.det (Matrix.of (fun i j => delta (![a, b, c] j) i))
  let M := Matrix.of (fun i j => delta (![m, n, p] j) (![r, s, t] i))
  M.det = eps r s t * eps m n p := by
  sorry







theorem theorem_944532_problem
  (F L : Type*) [Field F] [Field L] [Algebra F L]
  (a x : L)
  (h_alg : IsAlgebraic F a)
  (h_trans : ¬ IsAlgebraic F x) :
  IsEmpty (IntermediateField.adjoin F {a} ≃ₐ[F] IntermediateField.adjoin F {x}) := by
  sorry





theorem theorem_945003_problem
  (D : Set ℂ)
  (hD_open : IsOpen D)
  (hD_conn : IsConnected D)
  (f : ℂ → ℂ)
  (hf_holo : DifferentiableOn ℂ f D)
  (U : Set ℂ)
  (hU_subset : U ⊆ D)
  (hU_open : IsOpen U)
  (hU_nonempty : U.Nonempty)
  (h_zero_on_U : ∀ z ∈ U, f z = 0) :
  ∀ z ∈ D, f z = 0 := by
  sorry







theorem theorem_944852_problem
  (X : Type*) [TopologicalSpace X]
  (E : Set (Set X))
  (hE : ∀ U ∈ E, IsOpen U)
  (x : E → X)
  (h_cond : ∀ U ∈ E, (closure (Set.range x))ᶜ ∩ U = ∅) :
  Dense (Set.range x) := by
  sorry













theorem theorem_944880_problem
  (f : ℕ → ℝ)
  (F : ℝ → ℝ)
  (c : ℝ)
  (T : ℝ)
  (t₀ : ℝ → ℝ)
  (S : ℝ → ℝ)
  (v : ℝ)
  (hF : ∀ n : ℕ, F n = (∑ k in Finset.range (n + 1), f k) + c)
  (hS : ∀ u, S u = F (T - t₀ u + 1) - F 1)
  (hF_diff : Differentiable ℝ F)
  (ht₀_diff : DifferentiableAt ℝ t₀ v) :
  deriv S v = deriv (fun u ↦ F (T - t₀ u + 1) - F 1) v := by
  sorry









theorem theorem_945549_problem (n : ℕ) 
  (probable_prime_test : ℕ → Prop)
  (deterministic_prime_test : ℕ → Prop)
  (h_n_gt_1 : n > 1)
  (h_step1 : ∀ p : ℕ, Nat.Prime p → (p : ℝ) < Real.sqrt n → ¬ p ∣ n)
  (h_step2 : probable_prime_test n)
  (h_step3 : deterministic_prime_test n)
  (h_det_algo : ∀ k, deterministic_prime_test k → Nat.Prime k) : 
  Nat.Prime n := by
  sorry

theorem theorem_944948_problem
  (n : ℕ)
  (F : (Fin n → ℝ) → ℝ → ℝ)
  (G : ℝ → ℝ)
  (h_even : ∀ x y, F x y = F x (-y))
  (h_indep : ∀ x₁ x₂, ∀ᵐ y, F x₁ y = F x₂ y)
  (hG : ∀ a x, G a = ∫ y in (0 : ℝ)..a, F x y * y) :
  ∀ y₁ y₂ x, ∫ y in -y₂..y₁, F x y * y = G y₁ - G y₂ := by
  sorry

theorem theorem_945845_problem (x y z : ℤ)
  (h : x^2 + y^2 = 3 * z^2) :
  x = 0 ∧ y = 0 ∧ z = 0 := by
  sorry



theorem theorem_945858_problem (R S : Type*) [Ring R] [Ring S] [Nontrivial R]
  (f : R →ₙ+* S) (h : f 1 ≠ 1) :
  ∃ u : R, u ≠ 0 ∧ IsUnit u ∧ ¬ IsUnit (f u) := by
  sorry



theorem theorem_946081_problem (p n : ℕ) (r : ℤ) (t : ℕ)
  (hp : p.Prime)
  (hn : n > 0)
  (hr : ¬ (p : ℤ) ∣ r)
  (ht : t = Nat.lcm n (p - 1) / n) :
  (∃ x : ℤ, x ^ n ≡ r [ZMOD p]) ↔ r ^ t ≡ 1 [ZMOD p] := by
  sorry

