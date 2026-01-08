import Mathlib
import Mathlib.Tactic







theorem theorem_131100_problem (R : Type*) [CommRing R] (S : Type*) :
  LinearIndependent R (fun s : S => (MvPolynomial.X s : MvPolynomial S R)) := by
  sorry



theorem theorem_131199_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {k : ℕ}
  (v : Fin k → V)
  (lam : Fin k → F)
  (h_indep : LinearIndependent F v)
  (phi : Polynomial F)
  (h_roots : ∀ i, phi.eval (lam i) = 0) :
  ∑ i : Fin k, (phi.eval (lam i)) • (v i) = 0 := by
  sorry

theorem theorem_131242_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (x : X) (ε : ℝ)
  (hx : ‖x‖ < 1) (hε : 0 < ε) :
  let m := Nat.floor (1 / ε) + 1
  ∃ x_seq : Fin (m + 1) → X,
    x_seq 0 = 0 ∧
    x_seq (Fin.last m) = x ∧
    (∀ i : Fin (m + 1), ‖x_seq i‖ < 1) ∧
    (∀ i : Fin m, ‖x_seq i.succ - x_seq i.castSucc‖ < ε) := by
  sorry





theorem theorem_131384_problem
  (m n : ℕ)
  (A B : Matrix (Fin m) (Fin n) ℝ)
  (h1 : A * B.transpose = B * A.transpose)
  (h2 : ∃ (i1 : Fin m) (j1 : Fin n) (i2 : Fin m) (j2 : Fin n), A i1 j1 * B i2 j2 ≠ 0) :
  ∃ c : ℝ, A = c • B := by
  sorry



theorem theorem_131489_problem {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (x y : V) :
  |‖x‖ - ‖y‖| ≤ ‖x - y‖ := by
  sorry





theorem theorem_131721_problem (f : ℝ → ℝ → ℝ)
  (h_smooth : ContDiff ℝ ⊤ (Function.uncurry f))
  (h_partial : ∀ x y, deriv (fun u ↦ f u y) x = 0) :
  ∃ g : ℝ → ℝ, ContDiff ℝ ⊤ g ∧ ∀ x y, f x y = g y := by
  sorry











theorem theorem_132497_problem (n r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (h_nonneg : ∀ i j, 0 ≤ A i j)
  (h_stoch : ∀ i, ∑ j, A i j = 1)
  (h_classes : ∃ (classes : Fin r → Set (Fin n)),
    (∀ k₁ k₂, k₁ ≠ k₂ → classes k₁ ≠ classes k₂) ∧
    ∀ k,
      (∃ x, classes k = {y | Relation.ReflTransGen (fun a b => A a b ≠ 0) x y ∧
                             Relation.ReflTransGen (fun a b => A a b ≠ 0) y x}) ∧
      (∀ x ∈ classes k, ∀ y, Relation.ReflTransGen (fun a b => A a b ≠ 0) x y → y ∈ classes k)) :
  r ≤ A.charpoly.rootMultiplicity 1 := by
  sorry



theorem theorem_132234_problem (m n : ℕ)
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (p : Fin (m + 1) → V)
  (hp : AffineIndependent ℝ p)
  (b : V)
  (hb : b = (m + 1 : ℝ)⁻¹ • ∑ j, p j)
  (i : Fin (m + 1)) :
  AffineIndependent ℝ (Function.update p i b) := by
  sorry

theorem theorem_131832_problem
  (S : Set (ℝ × ℝ))
  (hS : MeasurableSet S)
  (f g : ℝ × ℝ → ℝ)
  (hf : Measurable f)
  (hg : Measurable g)
  (A B C : ℝ)
  (hA : A = ∫ x in S, (f x)^2)
  (hB : B = ∫ x in S, f x * g x)
  (hC : C = ∫ x in S, (g x)^2) :
  |B| ≤ Real.sqrt A * Real.sqrt C := by
  sorry



theorem theorem_132143_problem (n : ℕ) (A Q : Matrix (Fin n) (Fin n) ℝ)
  (hQ : Q * Q.transpose = 1 ∧ Q.transpose * Q = 1) :
  Matrix.trace ((A - Q).transpose * (A - Q)) = 
  Matrix.trace ((Q.transpose * A - 1).transpose * (Q.transpose * A - 1)) := by
  sorry

theorem theorem_132349_problem
  (M : Matrix (Fin 3) (Fin 3) ℝ)
  (hM : M = !![0, 1, 0; 0, 0, 1; 1, 0, 0])
  (t : ℝ)
  (A : Matrix (Fin 3) (Fin 3) ℝ)
  (hA : A = t • M + (1 - t) • M ^ 2)
  (S : Matrix (Fin 3) (Fin 3) ℝ)
  (J : Matrix (Fin 3) (Fin 3) ℝ)
  (hS : IsUnit S.det) -- S is invertible
  (hJ : J.IsDiag)     -- J is a diagonal matrix
  (h_decomp : M = S * J * S⁻¹)
  (n : ℕ)
  (hn : n > 0) :
  A ^ n = S * (t • J + (1 - t) • J ^ 2) ^ n * S⁻¹ := by
  sorry







theorem theorem_132588_problem (n : ℕ) (Q : Polynomial ℂ) (P : ℂ → ℂ)
  (hQ : Q.degree = n)
  (h_bound : ∀ w : ℂ, Complex.abs w = 1 → Complex.abs (Q.eval w) ≤ 1)
  (h_P : ∀ z : ℂ, 1 ≤ Complex.abs z → P z = (1 / z ^ n) * Q.eval (1 / z)) :
  ∀ z : ℂ, 1 ≤ Complex.abs z → Complex.abs (P z) ≤ Complex.abs z ^ n := by
  sorry

theorem theorem_132702_problem
  (n m : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (α₁ : ℝ)
  (J : Matrix (Fin m) (Fin n) ℝ)
  (E : Matrix (Fin n) (Fin 1) ℝ)
  (M : Matrix (Fin m) (Fin m) ℝ)
  (X : Matrix (Fin m) (Fin 1) ℝ)
  (h_JE : J.transpose * J * E = E)
  (h_M : M = J * (A - α₁ • (1 : Matrix (Fin n) (Fin n) ℝ)) * J.transpose)
  (h_X : X = J * E)
  (h_AE : (A - α₁ • (1 : Matrix (Fin n) (Fin n) ℝ)) * E = 0) :
  M * X = 0 := by
  sorry







theorem theorem_132939_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  (T : V →ₗ[K] W)
  (n : ℕ)
  (h : Module.rank K (LinearMap.range T) = n) :
  Module.rank K (LinearMap.range (LinearMap.dualMap T)) = n := by
  sorry

theorem theorem_132530_problem (f1 f2 g1 g2 h1 h2 d1 d2 : ℝ) :
  ∃ A B C : ℝ, ∀ E L : ℝ,
    ((f1 * h2 - f2 * h1) * E^2 - 2 * (g1 * h2 - g2 * h1) * E * L - (d1 * h2 - d2 * h1) = 0) →
    ((f1 * g2 - f2 * g1) * E^2 - (h1 * g2 - h2 * g1) * L^2 - (d1 * g2 - d2 * g1) = 0) →
    A * E^4 + B * E^2 + C = 0 := by
  sorry

theorem theorem_132643_problem :
  map_A '' {X : Matrix (Fin 3) (Fin 3) ℝ | X.IsSymm ∧ X.PosSemidef} = problem_S := by
  sorry

theorem theorem_132686_problem
  (f_n : ℕ → ℝ → ℝ)
  (f : ℝ → ℝ)
  (h_cont_n : ∀ n, ContinuousOn (f_n n) (Set.Ioo (-1) 1))
  (h_pointwise : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, HasSum (fun n ↦ f_n n x) (f x))
  (h_uniform : ∀ a, 0 < a → a < 1 →
    TendstoUniformlyOn (fun N x ↦ ∑ n in Finset.range N, f_n n x) f atTop (Set.Icc (-a) a)) :
  ContinuousOn f (Set.Ioo (-1) 1) := by
  sorry









theorem theorem_132732_problem
  {n p R : Type*}
  [Fintype n] [Fintype p]
  [DecidableEq n] [DecidableEq p]
  [Field R]
  (V : Matrix n n R)
  (A : Matrix n p R)
  [Invertible V]
  [Invertible (A.transpose * (⅟V) * A)]
  (B : Matrix p n R)
  (hB : B = (⅟(A.transpose * (⅟V) * A)) * A.transpose * (⅟V)) :
  B * V * B.transpose = ⅟(A.transpose * (⅟V) * A) := by
  sorry

theorem theorem_132931_problem
  {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  (f : E → F) (g : F → G) (p : E)
  (df_p : E →L[ℝ] F) (dg_q : F →L[ℝ] G)
  (hf : HasFDerivAt f df_p p)
  (hg : HasFDerivAt g dg_q (f p)) :
  HasFDerivAt (g ∘ f) (dg_q.comp df_p) p := by
  sorry



theorem theorem_133087_problem (n d : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d))
  (μ : EuclideanSpace ℝ (Fin d))
  (hμ : μ = (n : ℝ)⁻¹ • ∑ j, x j) :
  ∑ i, ∑ j, ‖x i - x j‖^2 = 2 * (n : ℝ) * ∑ i, ‖x i - μ‖^2 := by
  sorry

























theorem theorem_133931_problem (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
  (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.IsSymm)
  (N : Matrix (Fin 2) (Fin 2) ℝ) (hN : N = Matrix.diagonal ![a, b])
  (h_gen : M 0 1 ≠ 0) :
  (M * N).IsSymm ↔ a = b := by
  sorry









theorem theorem_133957_problem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
  Summable (fun k : ℕ => A ^ k) ↔ spectralRadius ℂ A < 1 := by
  sorry



theorem theorem_133734_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ) (x_k : E) (α_k : ℝ)
  (h_diff : Differentiable ℝ f)
  (h_min : IsLocalMin (fun α ↦ f (x_k - α • gradient f x_k)) α_k) :
  inner (gradient f x_k) (gradient f (x_k - α_k • gradient f x_k)) = (0 : ℝ) := by
  sorry



theorem theorem_133892_problem
  {R : Type*} [CommRing R]
  (A : Matrix (Fin 3) (Fin 3) R)
  (B : Matrix (Fin 3) (Fin 2) R)
  (u : ℕ → Matrix (Fin 2) (Fin 1) R)
  (x : ℕ → Matrix (Fin 3) (Fin 1) R)
  (h_init : x 0 = 0)
  (h_rec : ∀ n, x (n + 1) = A * x n + B * u n) :
  ∀ n, n ≥ 1 → x n = ∑ k in Finset.range n, A ^ (n - k - 1) * B * u k := by
  sorry





theorem theorem_134454_problem (n : ℕ) (a b : Fin n → ℂ) :
  let inner_prod := ∑ i, star (a i) * b i
  Complex.abs inner_prod ^ 2 = Complex.abs (∑ i, star (a i) * b i) ^ 2 := by
  sorry

theorem theorem_134608_problem
  {K X : Type*}
  [Field K] [TopologicalSpace K]
  [AddCommGroup X] [Module K X] [TopologicalSpace X]
  (h_seq : ∀ (x : ℕ → X) (x₀ : X) (α : ℕ → K) (α₀ : K),
    Filter.Tendsto x Filter.atTop (nhds x₀) →
    Filter.Tendsto α Filter.atTop (nhds α₀) →
    Filter.Tendsto (fun n => α n • x n) Filter.atTop (nhds (α₀ • x₀))) :
  Continuous (fun (p : K × X) => p.1 • p.2) := by
  sorry



theorem theorem_134477_problem
  (A H : Matrix (Fin 3) (Fin 3) ℝ)
  (l : ℝ → ℝ)
  (h_eig : ∀ c, Matrix.det (A + c • H - (l c) • 1) = 0)
  (h_diff : DifferentiableAt ℝ l 0)
  (h_denom : Matrix.trace (Matrix.adjugate (A - (l 0) • 1)) ≠ 0) :
  deriv l 0 = Matrix.trace (H * Matrix.adjugate (A - (l 0) • 1)) /
              Matrix.trace (Matrix.adjugate (A - (l 0) • 1)) := by
  sorry





theorem theorem_135021_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  (k : ℕ)
  (T : Module.End K V)
  (c : Fin k → K)
  (h_comm : ∀ i j : Fin k, (T - c i • (1 : Module.End K V)) * (T - c j • 1) = 
                           (T - c j • 1) * (T - c i • 1)) :
  ∀ σ : Equiv.Perm (Fin k),
    (List.ofFn (fun i => T - c i • (1 : Module.End K V))).prod = 
    (List.ofFn (fun i => T - c (σ i) • (1 : Module.End K V))).prod := by
  sorry

theorem theorem_135106_problem
  (n : ℕ)
  (C : ℕ → ℝ)
  (grad_J : ℕ → ℝ)
  (k : ℕ)
  (hk_lt : k < n)
  (hC_nonneg : ∀ i, 0 ≤ C i)
  (hgrad_nonneg : ∀ i, 0 ≤ grad_J i)
  -- The problem assumes a neural network structure where gradients propagate via the chain rule.
  -- Given the activation derivative bound C_i, this implies the gradient at step i is bounded
  -- by C_{i+1} times the gradient at step i+1 (simplifying weight interactions as per the problem context).
  (h_chain_step : ∀ i, k ≤ i → i < n → grad_J i ≤ C (i + 1) * grad_J (i + 1)) :
  grad_J k ≤ (∏ i in Finset.Ioc k n, C i) * (Finset.image grad_J (Finset.Ioc k n)).max' (by simp; omega) := by
  sorry



theorem theorem_134760_problem
  {K : Type*} [Field K]
  {L : Type*} [AddCommGroup L] [Module K L]
  (bracket : L →ₗ[K] L →ₗ[K] L)
  (h_anti : ∀ x y, bracket x y = - bracket y x) :
  (∃ (V : Type*) (_ : AddCommGroup V) (_ : Module K V) (φ : L →ₗ[K] Module.End K V),
    Function.Injective φ ∧
    ∀ x y, φ (bracket x y) = φ x * φ y - φ y * φ x) ↔
  (∀ x y z, bracket x (bracket y z) + bracket y (bracket z x) + bracket z (bracket x y) = 0) := by
  sorry

theorem theorem_135184_problem
  (F : Type*) [Field F] [Fintype F]
  (n : ℕ) (hn : n > 0)
  (q : ℕ) (hq : q = Fintype.card F)
  (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) F))
  (hM : ∀ (i j : Fin n), M i j = (MvPolynomial.X i)^(q^(j : ℕ)))
  (S : Finset (Fin n → F))
  (hS : ∀ (v : Fin n → F), v ≠ 0 → ∃! s, s ∈ S ∧ ∃ (k : F), k ≠ 0 ∧ v = k • s) :
  ∃ (c : F), c ≠ 0 ∧
    M.det = (MvPolynomial.C c) * ∏ s in S, (∑ i : Fin n, (MvPolynomial.C (s i)) * (MvPolynomial.X i)) := by
  sorry













theorem theorem_135811_problem
  {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  (M : X →ₗ[ℝ] Y)
  (S : Y →L[ℝ] Z)
  (T : X →L[ℝ] Z)
  (h : ∀ x, S (M x) = T x) :
  IsClosed (M.graph : Set (X × Y)) := by
  sorry

theorem theorem_135248_problem
  {R : Type*} [CommRing R]
  (n : ℕ)
  (a b c : Fin n → R)
  (d : Fin n → Fin n → R)
  (hd : ∀ x y, d x y = if x = y then 1 else 0)
  (i : Fin n) :
  ∑ j : Fin n, ∑ l : Fin n, ∑ m : Fin n, (d i l * d j m - d i m * d j l) * a j * b l * c m =
  ∑ j : Fin n, (a j * b i * c j - a j * b j * c i) := by
  sorry

theorem theorem_135734_problem
  (x : Fin 9 → Fin 2 → ℝ)
  (w : Fin 9 → ℝ)
  (hw : ∀ i, 0 ≤ w i)
  (n : ℝ)
  (hn : n = ∑ i, w i)
  (m : ℝ)
  (hm : m = ∑ i, (w i) ^ 2)
  (x_bar : Fin 2 → ℝ)
  (hx_bar : x_bar = (1 / n) • ∑ i, w i • x i)
  (h_cond : m < n ^ 2) :
  let w_hat := fun i ↦ w i / n
  let Cov_std := (1 / (1 - ∑ i, (w_hat i) ^ 2)) • ∑ i, w_hat i • Matrix.vecMulVec (x i - x_bar) (x i - x_bar)
  Cov_std = (n / (n ^ 2 - m)) • ∑ i, w i • Matrix.vecMulVec (x i - x_bar) (x i - x_bar) := by
  sorry

theorem theorem_135894_problem (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (h : x ≠ 0) :
  gradient (fun v => ‖v‖) x = ‖x‖⁻¹ • x := by
  sorry



theorem theorem_136072_problem (K : Type) [Field K] :
  ∃ (n : ℕ) (A B : Matrix (Fin n) (Fin n) K),
    IsUnit (A + B) ∧ ¬ IsUnit A ∧ ¬ IsUnit B := by
  sorry

theorem theorem_135353_problem
  (n : ℕ)
  (φ : EuclideanSpace ℝ (Fin n) → ℝ)
  (E : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (B : ℝ)
  (hB : B > 0)
  (h_diff : Differentiable ℝ φ)
  (hE : ∀ x, E x = - gradient φ x)
  (h_bound : ∀ x, ‖E x‖ ≤ B) :
  ∀ δ > 0, ∃ ε > 0, ∀ x y : EuclideanSpace ℝ (Fin n), ‖y - x‖ < δ → |φ y - φ x| < ε := by
  sorry



theorem theorem_136011_problem (a b : ℕ) (h : a ≤ b) :
  ∑ k in Finset.Icc a b, Nat.fib k = Nat.fib (b + 2) - Nat.fib (a + 1) := by
  sorry







