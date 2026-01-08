import Mathlib
import Mathlib.Tactic



theorem theorem_299813_problem (a b : ℝ) (f : ℂ → ℂ) (γ : ℝ → ℂ)
  (hf : Continuous f)
  (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
  IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume a b := by
  sorry

theorem theorem_299946_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (u : E → ℝ) (x : E)
  (h_diff : DifferentiableAt ℝ u x)
  (hx : x ≠ 0) :
  inner (gradient u x) x = ‖x‖ * fderiv ℝ u x (‖x‖⁻¹ • x) := by
  sorry

theorem theorem_300132_problem (a b c d e f : ℝ) :
  (∃ p₁ q₁ r₁ p₂ q₂ r₂ : ℝ, ∀ x y : ℝ,
    a * x^2 + b * x * y + c * y^2 + d * x + e * y + f =
    (p₁ * x + q₁ * y + r₁) * (p₂ * x + q₂ * y + r₂)) ↔
  (1 : ℝ) / 8 * Matrix.det !![2 * a, b, d; b, 2 * c, e; d, e, 2 * f] = 0 := by
  sorry

theorem theorem_299791_problem (k : ℕ) (hk : k > 0)
  (p : Fin (k + 1) → EuclideanSpace ℝ (Fin k))
  (c : EuclideanSpace ℝ (Fin k)) :
  (∀ i : Fin k, inner (p i.castSucc - p i.succ) c =
    (1 / 2 : ℝ) * inner (p i.castSucc - p i.succ) (p i.castSucc + p i.succ)) ↔
  (∀ i j : Fin (k + 1), dist c (p i) = dist c (p j)) := by
  sorry









theorem theorem_300082_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (P₁ P₂ I : V)
  (v₁ v₂ : V)
  (R : V) (hR : R = v₁ + v₂)
  (S : Set V)
  (E_star : V) (hE_star : E_star ∈ S)
  -- Condition: E_star is the correct elbow, meaning it minimizes the angle between R and u_E
  (h_optimal : ∀ E ∈ S, InnerProductGeometry.angle R (E_star - I) ≤ InnerProductGeometry.angle R (E - I)) :
  -- Conclusion: E_star satisfies the argmin expression (minimizes the arccos formula)
  ∀ E ∈ S, Real.arccos (inner R (E_star - I) / (norm R * norm (E_star - I))) ≤
           Real.arccos (inner R (E - I) / (norm R * norm (E - I))) := by
  sorry



theorem theorem_300591_problem
  {n : ℕ} {F : Type*} [Field F]
  (A : Matrix (Fin n) (Fin n) F)
  (hA : IsNilpotent A) :
  Matrix.trace A = 0 := by
  sorry

theorem theorem_300090_problem
  {R : Type*} [CommRing R]
  {r : ℕ}
  (A : Matrix (Fin r) (Fin r) R)
  (I : Ideal R)
  (hI : I = Ideal.span (Set.range (fun (x : Fin r × Fin r) => A x.1 x.2))) :
  Matrix.det ((1 : Matrix (Fin r) (Fin r) R) - A) - 1 ∈ I := by
  sorry





theorem theorem_300548_problem
  (L : Type*) [AddCommGroup L] [Module ℝ L]
  (J : L →ₗ[ℝ] L) (hJ : J ^ 2 = -LinearMap.id)
  (T : L →ₗ[ℝ] L) :
  (∀ (a b : ℝ) (v : L), T (a • v + J (b • v)) = a • T v + J (b • T v)) ↔
  (T ∘ₗ J = J ∘ₗ T) := by
  sorry



theorem theorem_300679_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  (S T : X →L[𝕜] X)
  (hS : IsUnit S)
  (h_ineq : ‖T - S‖ < ‖(↑hS.unit⁻¹ : X →L[𝕜] X)‖⁻¹) :
  IsUnit T := by
  sorry

theorem theorem_300686_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (x y : E) (hx : x ≠ 0) (hy : ‖y‖ = 1) :
  ‖x‖^2 * ‖y - (‖x‖^2)⁻¹ • x‖^2 = ‖x‖^2 - 2 * inner y x + 1 := by
  sorry



theorem theorem_300837_problem :
  Fintype.card { v : Fin 5 → ZMod 3 // (Finset.univ.filter (λ i => v i ≠ 0)).card = 2 } = 40 := by
  sorry













theorem theorem_300870_problem
  (a b c x y : Fin 3 → ℝ)
  (A B : Matrix (Fin 3) (Fin 3) ℝ)
  (hA : A = Matrix.of (fun i j => if j = 0 then a i else if j = 1 then b i else c i))
  (hB : B = Matrix.of (fun i j => if i = 0 then x j else if i = 1 then y j else 1))
  (h_orth : ∀ i j, i ≠ j → a j * x i + b j * y i + c j = 0)
  (d : Fin 3 → ℝ)
  (hd_def : ∀ i, d i = a i * x i + b i * y i + c i)
  (hd_nonzero : ∀ i, d i ≠ 0)
  (C_1 C_2 C_3 : ℝ)
  (hC1 : C_1 = a 1 * b 2 - a 2 * b 1)
  (hC2 : C_2 = a 2 * b 0 - a 0 * b 2)
  (hC3 : C_3 = a 0 * b 1 - a 1 * b 0) :
  B.det = A.det ^ 2 / (C_1 * C_2 * C_3) := by
  sorry





theorem theorem_301466_problem (n d : ℕ) (K : Type*) [Field K]
  (M : Matrix (Fin n) (Fin n) (Polynomial K))
  (h : ∀ i j, (M i j).degree ≤ d) :
  M.det.degree ≤ n * d := by
  sorry

theorem theorem_301387_problem
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
  (A B : Matrix m n ℝ)
  (β : ℝ) (hβ : 0 < β) :
  Matrix.PosSemidef ((A - B) * (A - B).transpose - ((β / (1 + β)) • (A * A.transpose) - β • (B * B.transpose))) := by
  sorry





theorem theorem_301391_problem
  (n m : ℕ)
  (rows cols : Fin m → Fin n)
  (D : Set (Matrix (Fin n) (Fin n) ℝ))
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : A ∈ D)
  (h_det : (A.submatrix rows cols).det ≠ 0) :
  let φ : ↥D → ℝ := fun M ↦ (M.val.submatrix rows cols).det
  let S := φ ⁻¹' {x | x ≠ 0}
  IsOpen S ∧ (⟨A, hA⟩ : ↥D) ∈ S := by
  sorry



theorem theorem_301276_problem
  {K : Type*} [Field K]
  {n m : ℕ}
  (A : Matrix (Fin n) (Fin m) K) :
  ∃! B : Matrix (Fin m) (Fin n) K,
    ∀ (x : Fin n → K) (y : Fin m → K),
      Matrix.dotProduct x (Matrix.mulVec A y) = Matrix.dotProduct (Matrix.mulVec B x) y := by
  sorry





theorem theorem_301573_problem
  {F Z : Type*} [Field F] [AddCommGroup Z] [Module F Z]
  [FiniteDimensional F Z]
  (h_dim : FiniteDimensional.finrank F Z = 4)
  (ω₁ ω₂ : Z →ₗ[F] Z →ₗ[F] F)
  (hω₁ : ∀ v, ω₁ v v = 0)
  (hω₂ : ∀ v, ω₂ v v = 0) :
  ∃ L : Submodule F Z,
    FiniteDimensional.finrank F L = 2 ∧
    (∀ u v : L, ω₁ u v = 0) ∧
    (∀ u v : L, ω₂ u v = 0) := by
  sorry

theorem theorem_301383_problem (u v : ℝ)
  (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) :
  (1 - u) * (1 - v) + u * (1 - v) + u * v + (1 - u) * v = 1 := by
  sorry

theorem theorem_301720_problem
  (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
  (q : ℕ) (hq : Fintype.card K = q) :
  Fintype.card { A : Matrix (Fin m) (Fin n) K // A.rank = m } =
  ∏ j in Finset.range m, (q ^ n - q ^ j) := by
  sorry





theorem theorem_301783_problem
  (z : ℂ) (hz : 1 < Complex.abs z)
  (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 (Complex.abs z)))
  (P : Polynomial ℂ) :
  circleIntegral (fun ζ => f ζ / (ζ - z)) 0 1 =
  circleIntegral (fun ζ => (f ζ - Polynomial.eval ζ P) / (ζ - z)) 0 1 := by
  sorry











theorem theorem_302235_problem :
  ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    (∀ (k : ℕ) (f : Fin k → Fin n), Function.Injective f → (A.submatrix f f).det > 0) ∧
    ¬ (∀ (z : ℂ), (Polynomial.map (algebraMap ℝ ℂ) A.charpoly).eval z = 0 → z.im = 0 ∧ 0 < z.re) := by
  sorry



theorem theorem_302519_problem
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix m n ℝ)
  (S : Matrix m m ℝ)
  (hS : S.PosSemidef) :
  (A.transpose * S * A).PosSemidef := by
  sorry





theorem theorem_302334_problem (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (B : Matrix (Fin n) (Fin 1) ℝ)
  (C : Matrix (Fin 1) (Fin n) ℝ)
  (s : ℝ)
  (h : IsUnit (s • (1 : Matrix (Fin n) (Fin n) ℝ) - A)) :
  (s • (1 : Matrix (Fin n) (Fin n) ℝ) - A + B * C).det =
    (s • (1 : Matrix (Fin n) (Fin n) ℝ) - A).det *
      (1 + (C * (s • (1 : Matrix (Fin n) (Fin n) ℝ) - A)⁻¹ * B) 0 0) := by
  sorry



theorem theorem_302670_problem
  {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (T : X →L[ℝ] Y)
  (x₀ x : X)
  (r : ℝ)
  (hr : 0 < r) :
  2 * r * ‖T x‖ ≤ ‖T (x₀ + r • x) - T (x₀ - r • x)‖ := by
  sorry

theorem theorem_302793_problem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (a b c : V)
  (h_distinct : a ≠ b ∧ b ≠ c ∧ a ≠ c)
  (h_ncol : ¬ Collinear K ({a, b, c} : Set V)) :
  (affineSpan K ({a, b, c} : Set V) : Set V) =
  {r | ∃ x y : K, r = a + x • (b - a) + y • (c - a)} := by
  sorry





theorem theorem_302813_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [Field K]
  (A : Matrix n n K)
  (hA : A ^ 2 = A)
  (f : Polynomial K)
  (s t : K) :
  Polynomial.aeval (s • (1 : Matrix n n K) + t • A) f =
    (f.eval s) • ((1 : Matrix n n K) - A) + (f.eval (s + t)) • A := by
  sorry

theorem theorem_302965_problem
  (k m : ℕ)
  (M : Matrix (Fin m) (Fin k) ℤ)
  (c : Fin m → ℤ)
  -- Condition 1: Local solvability modulo every prime q
  (h_local : ∀ (q : ℕ), q.Prime → ∃ (x : Fin k → ℤ), ∀ (i : Fin m),
    ((Matrix.mulVec M x) i + c i) % (q : ℤ) = 0)
  -- Condition 2: The set of real solutions is unbounded
  (h_real : ¬ Bornology.IsBounded { x : Fin k → ℝ | ∀ (i : Fin m),
    (Matrix.mulVec (M.map (Int.cast : ℤ → ℝ)) x) i + (c i : ℝ) = 0 })
  -- Hypothesis: The Generalized Hardy-Littlewood Conjecture
  -- We assume the conjecture implies that if a system is locally solvable and real unbounded,
  -- then it has infinitely many prime solutions.
  (h_ghlc : ∀ (k' m' : ℕ) (M' : Matrix (Fin m') (Fin k') ℤ) (c' : Fin m' → ℤ),
    (∀ (q : ℕ), q.Prime → ∃ (x : Fin k' → ℤ), ∀ (i : Fin m'), ((Matrix.mulVec M' x) i + c' i) % (q : ℤ) = 0) →
    (¬ Bornology.IsBounded { x : Fin k' → ℝ | ∀ (i : Fin m'), (Matrix.mulVec (M'.map (Int.cast : ℤ → ℝ)) x) i + (c' i : ℝ) = 0 }) →
    Set.Infinite { x : Fin k' → ℕ | (∀ i, (x i).Prime) ∧ (∀ j, (Matrix.mulVec M' (fun i ↦ (x i : ℤ))) j + c' j = 0) }) :
  -- Conclusion: There exist infinitely many solutions where all x_i are prime
  Set.Infinite { x : Fin k → ℕ | (∀ i, (x i).Prime) ∧ (∀ j, (Matrix.mulVec M (fun i ↦ (x i : ℤ))) j + c j = 0) } := by
  sorry









theorem theorem_303386_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (α : ι → V)
  (s : ι)
  (h_le : ∀ i, B (α i) (α s) ≤ 0)
  (k : ι)
  (c : ι → ℝ)
  (h_decomp : α k = (∑ t in Finset.univ.erase s, c t • α t) + c s • α s) :
  B (α k) (α s) = (∑ t in Finset.univ.erase s, c t * B (α t) (α s)) + c s * B (α s) (α s) ∧
  B (α k) (α s) ≤ 0 := by
  sorry





theorem theorem_303357_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  (e : ℕ → X)
  (f : X →L[𝕜] Y)
  (x : X)
  (α : ℕ → 𝕜)
  (h : HasSum (fun i => α i • e i) x) :
  HasSum (fun i => α i • f (e i)) (f x) := by
  sorry

theorem theorem_303359_problem (φ : ℝ → (Fin 3 → ℝ)) (hφ : ContDiff ℝ ⊤ φ) :
  ∃ (n : ℕ) (F : (Fin (n + 1) → (Fin 3 → ℝ)) → (Fin 3 → ℝ)),
    ∀ t, F (fun i => iteratedDeriv i φ t) = 0 := by
  sorry



theorem theorem_303443_problem
  {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  (f : F → G) (u : E → F) (x : E)
  (hf : ContDiff ℝ ⊤ f)
  (hu : ContDiff ℝ ⊤ u) :
  fderiv ℝ (f ∘ u) x = (fderiv ℝ f (u x)).comp (fderiv ℝ u x) := by
  sorry





theorem theorem_303826_problem
  (n : ℕ)
  (c : ℝ)
  (hc : c > 0)
  (norm : (Fin n → ℝ) → ℝ)
  (h_nonneg : ∀ x : Fin n → ℝ, 0 ≤ norm x)
  (h_def : ∀ x : Fin n → ℝ, norm x = 0 ↔ x = 0)
  (h_homog : ∀ (a : ℝ) (x : Fin n → ℝ), norm (a • x) = |a| * norm x)
  (h_tri : ∀ x y : Fin n → ℝ, norm (x + y) ≤ norm x + norm y) :
  ∀ x : Fin n → ℝ, 0 ≤ x → norm 0 ≤ norm x := by
  sorry



theorem theorem_304135_problem
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (C : Set E) (f : E → F) (k : ℝ)
  (hC : Convex ℝ C)
  (hf : DifferentiableOn ℝ f C)
  (hk : k > 0)
  (h_bound : ∀ x ∈ C, ‖fderiv ℝ f x‖ ≤ k) :
  ∀ a ∈ C, ∀ b ∈ C, ‖f a - f b‖ ≤ k * ‖a - b‖ := by
  sorry



theorem theorem_303928_problem (a b p : EuclideanSpace ℝ (Fin 2))
  (h : inner (a - p) (b - p) = (0 : ℝ)) :
  ‖a - p‖^2 + ‖b - p‖^2 = ‖a - b‖^2 := by
  sorry



theorem theorem_303919_problem (S q : ℝ)
  (h_constr : -q ≤ S ∧ S ≤ q)
  (h_opt : ∀ q', (-q' ≤ S ∧ S ≤ q') → q ≤ q') :
  q = |S| := by
  sorry









theorem theorem_304424_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (g : LinearMap.BilinForm ℝ V)
  (hg_symm : g.IsSymm)
  (hg_nondeg : g.Nondegenerate)
  (ϕ : V →ₗ[ℝ] V)
  {n : Type*} [Fintype n] [DecidableEq n]
  (b : Basis n ℝ V) :
  ∃! ψ : V →ₗ[ℝ] V,
    (∀ v w, g v (ϕ w) = g (ψ v) w) ∧
    (let M_ϕ := LinearMap.toMatrix b b ϕ
     let M_g := BilinForm.toMatrix b g
     let M_g_inv := M_g⁻¹
     let M_ψ := LinearMap.toMatrix b b ψ
     ∀ (a c : n), M_ψ a c = ∑ d : n, ∑ e : n, M_ϕ e d * M_g_inv a d * M_g e c) := by
  sorry







theorem theorem_304555_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  (ρ : V →L[𝕜] 𝕜) :
  ∃! x : V, ∀ y : V, ρ y = inner x y := by
  sorry

theorem theorem_304288_problem
  (n : ℕ)
  (S : Matrix (Fin n) (Fin n) ℝ)
  (μ α : Fin n → ℝ)
  (hS_symm : S.IsSymm)
  (hS_pos : S.PosDef)
  (hμ : μ ≠ 0)
  (h_eqn : (Matrix.dotProduct α (S.mulVec α)) • μ = (Matrix.dotProduct α μ) • (S.mulVec α)) :
  ∃ k : ℝ, α = k • (S⁻¹.mulVec μ) := by
  sorry

theorem theorem_304297_problem (n : ℕ) (x y : EuclideanSpace ℝ (Fin n))
  (hx : x ≠ 0) (hy : y ≠ 0) :
  ‖(‖x‖ ^ 3)⁻¹ • x - (‖y‖ ^ 3)⁻¹ • y‖ ≤
  ‖x - y‖ / ‖x‖ ^ 3 + (‖x - y‖ * (‖x‖ ^ 2 + ‖x‖ * ‖y‖ + ‖y‖ ^ 2)) / (‖x‖ ^ 3 * ‖y‖ ^ 3) := by
  sorry





theorem theorem_305129_problem (n : ℕ) (a : Fin n → ℝ) (x : Fin n → ℝ) (lam : ℝ)
  (hx : ∀ i, 0 < x i)
  (h : ∀ i, -a i / (x i)^2 = lam * ∏ j in Finset.univ.erase i, x j) :
  ∀ i k, a i / x i = a k / x k := by
  sorry



theorem theorem_304749_problem
  (a b : Fin 4 → ℝ)
  (B C : Matrix (Fin 5) (Fin 5) ℝ)
  (hB : B = !![b 0, 0, 0, 0, 0;
               0, b 1, 0, 0, 0;
               0, 0, b 2, 0, 0;
               0, 0, 0, b 3, 0;
               0, 0, 0, 0, 1])
  (hC : C = !![b 0, b 1, 0, 0, 0;
               0, b 1, b 2, 0, 0;
               0, 0, b 2, b 3, 0;
               0, 0, 0, b 3, 1;
               a 0, -(a 1), a 2, -(a 3), 0])
  (hb : ∀ i, b i ≠ 0)
  (hsum : ∑ i, a i / b i ≠ 0)
  (hCdet : C.det ≠ 0) :
  1 / (∑ i, a i / b i) = B.det / C.det := by
  sorry



