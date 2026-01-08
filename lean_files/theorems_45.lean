import Mathlib
import Mathlib.Tactic





theorem theorem_241141_problem (θ₁ θ₂ : ℝ)
  (h_conv : θ₁ < 0 ∧ 4 * θ₁ ^ 2 > θ₂ ^ 2)
  (A : ℝ)
  (h_pdf : ∫ p : ℝ × ℝ, Real.exp (θ₁ * (p.1 ^ 2 + p.2 ^ 2) + θ₂ * p.1 * p.2 - A) = 1) :
  ∃ c : ℝ, A = -1/2 * Real.log (1/4 * (θ₁ ^ 2 - 1/4 * θ₂ ^ 2)) + c := by
  sorry











theorem theorem_242481_problem
  {N : ℕ}
  (a : Matrix (Fin N) (Fin N) ℝ)
  (x : Fin N → ℝ)
  (K : Fin N → ℝ)
  (y : Matrix (Fin N) (Fin N) ℝ)
  (hy : ∀ i j, y i j = a i j / K i)
  (i : Fin N) :
  (1 / K i) * Matrix.dotProduct (a i) x = ∑ j, y i j * x j := by
  sorry







theorem theorem_242966_problem (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
  (h : Matrix.rank M + 1 = n) :
  Matrix.adjugate M ≠ 0 := by
  sorry



theorem theorem_243081_problem (F K : Type*) [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] (k : K) :
  let u_k : K →ₗ[F] K := Algebra.lmul F K k
  let P := LinearMap.charpoly u_k
  Polynomial.aeval k P = 0 := by
  sorry



theorem theorem_242912_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (A B : Matrix n n ℝ)
  (hA : A.PosDef)
  (hB : B.PosSemidef) :
  Matrix.trace (A + B)⁻¹ ≤ Matrix.trace A⁻¹ := by
  sorry

theorem theorem_242803_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (a b : E) (h : b ≠ 0) :
  ∀ t₁ t₂ : ℝ, dist (a + t₁ • (‖b‖⁻¹ • b)) (a + t₂ • (‖b‖⁻¹ • b)) = dist t₁ t₂ := by
  sorry

theorem theorem_242657_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (E F : V →ₗ[K] V)
  (hE : E ^ 2 = E)
  (hF : F ^ 2 = F)
  (h1 : LinearMap.ker F ⊓ LinearMap.range E = ⊥)
  (h2 : LinearMap.ker E ⊓ LinearMap.range F = ⊥) :
  Module.rank K (LinearMap.range E) = Module.rank K (LinearMap.range F) := by
  sorry







theorem theorem_242786_problem
  {K V W X Y : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]
  (A : V →ₗ[K] W) (B : X →ₗ[K] Y)
  (m n : ℕ)
  (w : Basis (Fin m) K W)
  (y : Basis (Fin n) K Y)
  (v₁ : V) (x₁ : X)
  (a : Fin m → K) (ha : A v₁ = ∑ i, a i • w i)
  (b : Fin n → K) (hb : B x₁ = ∑ j, b j • y j) :
  TensorProduct.map A B (v₁ ⊗ₜ[K] x₁) =
  ∑ i : Fin m, ∑ j : Fin n, (a i * b j) • (w i ⊗ₜ[K] y j) := by
  sorry



theorem theorem_243511_problem (n : ℕ) (k : Type*) [CommRing k] (A : Matrix (Fin n) (Fin n) k) :
  Polynomial.aeval A (Matrix.charpoly A) = 0 := by
  sorry





theorem theorem_243455_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (u : ℝ → E)
  (h_diff : Differentiable ℝ u)
  (h_norm : ∀ t, inner (u t) (u t) = (1 : ℝ)) :
  ∀ t, inner (u t) (deriv u t) = (0 : ℝ) := by
  sorry





theorem theorem_243525_problem
  (n m : ℕ)
  (D : Set (Fin n → ℝ))
  (hD : IsCompact D)
  (hD_ne : D.Nonempty)
  (f : (Fin m → ℝ) × D → ℝ)
  (hf : Continuous f)
  (ψ : (Fin m → ℝ) → ℝ)
  (hψ : ∀ x, ψ x = ⨆ y : D, f (x, y)) :
  Continuous ψ := by
  sorry

theorem theorem_243479_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  (m n : ℕ)
  (A : V →ₗ[K] W)
  (h_dim_domain : FiniteDimensional.finrank K V = n)
  (h_dim_codomain : FiniteDimensional.finrank K W = m) :
  FiniteDimensional.finrank K (LinearMap.range A) + FiniteDimensional.finrank K (LinearMap.ker A) = n := by
  sorry

theorem theorem_243581_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [Field K]
  (α₁ α₂ β₁ β₂ : n → K)
  (h₁ : Matrix.dotProduct α₁ β₁ ≠ 0)
  (h₂ : Matrix.dotProduct α₂ β₂ ≠ 0) :
  ((Matrix.dotProduct α₂ β₁) / (Matrix.dotProduct α₁ β₁)) •
    ((1 / (Matrix.dotProduct α₂ β₂)) • Matrix.vecMulVec α₁ β₂) =
  ((1 / (Matrix.dotProduct α₁ β₁)) • Matrix.vecMulVec α₁ β₁) *
    ((1 / (Matrix.dotProduct α₂ β₂)) • Matrix.vecMulVec α₂ β₂) := by
  sorry





theorem theorem_244098_problem
  {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  (V_alpha : ι → Set V)
  (h_chain : ∀ i j, V_alpha i ⊆ V_alpha j ∨ V_alpha j ⊆ V_alpha i)
  (h_indep : ∀ i, LinearIndependent K (Subtype.val : V_alpha i → V)) :
  LinearIndependent K (Subtype.val : (⋃ i, V_alpha i) → V) := by
  sorry

theorem theorem_243849_problem (n : ℕ) :
  Subgroup.closure { A : Matrix.GeneralLinearGroup (Fin n) ℤ |
    (∃ i j : Fin n, i ≠ j ∧ A.1 = 1 + Matrix.stdBasisMatrix i j 1) ∨
    (∃ i : Fin n, A.1 = Matrix.diagonal (fun k => if i = k then -1 else 1)) } = ⊤ := by
  sorry



theorem theorem_243133_problem
  (u v : ℝ → ℝ → ℝ)
  (x y : ℝ) :
  let G := fun (t : ℝ) ↦ (
    x * Real.cos t - u x y * Real.sin t,
    y * Real.cos t - v x y * Real.sin t,
    u x y * Real.cos t + x * Real.sin t
  )
  Continuous G ∧
  G 0 = (x, y, u x y) ∧
  G (Real.pi / 2) = (-u x y, -v x y, x) := by
  sorry



theorem theorem_242550_problem
  (k : Type*) [Field k] (hchar : ringChar k ≠ 2)
  (Q : Fin 3 → MvPolynomial (Fin 2) k)
  (hI : Ideal.span (Set.range Q) = Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 1, MvPolynomial.X 1 ^ 2})
  (h_squares : ∀ i, ∃ L : MvPolynomial (Fin 2) k, MvPolynomial.IsHomogeneous L 1 ∧ Q i = L ^ 2) :
  ∀ (lo : LinearOrder (Fin 2 →₀ ℕ))
  (h_add : ∀ a b c : Fin 2 →₀ ℕ, lo.le a b → lo.le (a + c) (b + c))
  (h_bot : ∀ a : Fin 2 →₀ ℕ, lo.le 0 a),
  letI := lo
  let lm := fun (p : MvPolynomial (Fin 2) k) => p.support.max
  ¬ Set.Pairwise Set.univ (fun i j => lm (Q i) ≠ lm (Q j)) := by
  sorry



theorem theorem_243957_problem (h k θ : ℝ)
  (T R T_inv : ℝ × ℝ → ℝ × ℝ)
  (hT : ∀ x y, T (x, y) = (x - h, y - k))
  (hR : ∀ x y, R (x, y) = (x * Real.cos θ - y * Real.sin θ, x * Real.sin θ + y * Real.cos θ))
  (hT_inv : ∀ x y, T_inv (x, y) = (x + h, y + k)) :
  ∀ x y, T_inv (R (T (x, y))) = 
    ((x - h) * Real.cos θ - (y - k) * Real.sin θ + h, 
     (x - h) * Real.sin θ + (y - k) * Real.cos θ + k) := by
  sorry











theorem theorem_244038_problem (a b c d : ℝ) :
  a + b * Real.sqrt 3 + c * Real.sqrt 5 + d * Real.sqrt 3 * Real.sqrt 5 =
  (a + c * Real.sqrt 5) + (b + d * Real.sqrt 5) * Real.sqrt 3 := by
  sorry

theorem theorem_244858_problem
  (c1 c2 c3 d1 d2 d3 : ℝ)
  (h : c1 * d2 - c2 * d1 = 0) :
  ∃ g : ℝ → ℝ, ∀ x t : ℝ,
    d1 * x + d2 * t + d3 ≠ 0 →
    (c1 * x + c2 * t + c3) / (d1 * x + d2 * t + d3) = g (d1 * x + d2 * t) := by
  sorry

theorem theorem_244722_problem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (S : V →ₗ[K] V) (f u v : V)
  (hf : f ≠ 0)
  (hSu : S u = f)
  (hSv : S v = f) :
  u - v ∈ LinearMap.ker S := by
  sorry









theorem theorem_244733_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (e : HilbertBasis ℕ ℂ H)
  (S : H →L[ℂ] H)
  (hS : ∀ n, S (e n) = e (n + 1)) :
  spectrum ℂ (S + star S) = (Set.Icc (-2 : ℝ) 2).image (algebraMap ℝ ℂ) := by
  sorry











theorem theorem_244703_problem
  (n : ℕ) (hn : n > 0)
  (x : Fin n → ℝ)
  (p q : ℝ)
  (hp : 1 ≤ p) (hq : 1 ≤ q)
  (hpq : p ≠ q) :
  (∑ i, |x i| ^ p) ^ (1 / p) = (∑ i, |x i| ^ q) ^ (1 / q) ↔
  ∃ c : ℝ, ∃ i : Fin n, x = Pi.single i c := by
  sorry

theorem theorem_245480_problem
  {X : Type*} [MetricSpace X]
  (f_n : ℕ → X → ℝ) (f : X → ℝ)
  (x_n : ℕ → X) (x : X)
  (h_fn_cont : ∀ n, Continuous (f_n n))
  (h_f_cont : Continuous f)
  (h_unif : TendstoUniformly f_n f Filter.atTop)
  (h_xn_conv : Filter.Tendsto x_n Filter.atTop (nhds x)) :
  Filter.Tendsto (fun n ↦ f_n n (x_n n)) Filter.atTop (nhds (f x)) := by
  sorry

theorem theorem_244361_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (U : Set E) (hU : IsOpen U)
  (f : E → E) (a : E) (ha : a ∈ U)
  (h_diff : DifferentiableOn ℝ f U)
  (h_cont : ContinuousAt (fderiv ℝ f) a) :
  let r := fun z ↦ f z - f a - (fderiv ℝ f a) (z - a)
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Metric.ball a δ, ∀ y ∈ Metric.ball a δ,
    ‖r x - r y‖ ≤ ε * ‖x - y‖ := by
  sorry





theorem theorem_245383_problem
  (b c : ℝ)
  (x₁ x₂ : ℝ → ℝ)
  (h_diff₁ : ContDiff ℝ 2 x₁)
  (h_diff₂ : ContDiff ℝ 2 x₂)
  (h_sol₁ : ∀ t, deriv (deriv x₁) t + b * deriv x₁ t + c * x₁ t = 0)
  (h_sol₂ : ∀ t, deriv (deriv x₂) t + b * deriv x₂ t + c * x₂ t = 0)
  (t₀ : ℝ)
  (hW : x₁ t₀ * deriv x₂ t₀ - deriv x₁ t₀ * x₂ t₀ = 0) :
  ∃ (k₁ k₂ : ℝ), (k₁ ≠ 0 ∨ k₂ ≠ 0) ∧ ∀ t, k₁ * x₁ t + k₂ * x₂ t = 0 := by
  sorry



theorem theorem_245350_problem (n : ℕ) (hn : 2 ≤ n) :
  ¬ ∀ (P1 Q1 P2 Q2 : Matrix (Fin n) (Fin n) ℝ),
    P1.IsSymm → Q1.IsSymm → P2.IsSymm → Q2.IsSymm →
    ∀ (x : ℝ), 0 ≤ x ∧ x ≤ 1 →
    min (P1 * Q1).trace (P2 * Q2).trace ≤ 
      (((1 - x) • P1 + x • P2) * ((1 - x) • Q1 + x • Q2)).trace := by
  sorry



theorem theorem_246005_problem
  {K V U W : Type*}
  [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W]
  (f : V →ₗ[K] W)
  (g : U →ₗ[K] W)
  (hg : Function.Bijective g)
  (T : V → U)
  (h : ∀ x, f x = g (T x)) :
  IsLinearMap K T := by
  sorry



theorem theorem_245736_problem
  (n : ℕ)
  (R : Type*) [CommRing R]
  (A : Matrix (Fin n) (Fin n) R) :
  Polynomial.aeval A (Matrix.charpoly A) = 0 := by
  sorry



theorem theorem_246203_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  {W : Type*} [AddCommGroup W] [Module K W]
  {n : ℕ}
  (T : V →ₗ[K] W)
  (h_inj : Function.Injective T)
  (x : Fin n → V)
  (h_indep : LinearIndependent K x) :
  LinearIndependent K (T ∘ x) := by
  sorry



theorem theorem_246200_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (A : V →ₗ[F] V)
  (k : ℕ)
  (hAk : A ^ k = 0)
  (hAm : ∀ m : ℕ, m < k → A ^ m ≠ 0)
  (v : V)
  (hv : (A ^ (k - 1)) v ≠ 0) :
  LinearIndependent F (fun (i : Fin k) => (A ^ (i : ℕ)) v) := by
  sorry



theorem theorem_245699_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  {W : Type*} [AddCommGroup W] [Module F W]
  {n m : ℕ}
  (B : Basis (Fin n) F V)
  (B' : Basis (Fin m) F W)
  (T : V →ₗ[F] W) :
  ∀ j : Fin n, T (B j) = ∑ i : Fin m, (LinearMap.toMatrix B B' T i j) • (B' i) := by
  sorry



theorem theorem_246501_problem
  (M : C(Set.Icc (0 : ℝ) 1, ℝ) →L[ℝ] C(Set.Icc (0 : ℝ) 1, ℝ))
  (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
  (S : Submodule ℝ C(Set.Icc (0 : ℝ) 1, ℝ))
  (hS : ∀ f, f ∈ S ↔ ∀ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ≤ ε → f x = 0)
  (h_invariant : ∀ f ∈ S, M f ∈ S)
  (h_invertible : Function.Bijective (fun (f : S) ↦ (⟨M f, h_invariant f f.2⟩ : S))) :
  ¬ IsCompactOperator M := by
  sorry

theorem theorem_245613_problem
  (n : ℕ)
  (K : Type*) [Field K]
  (x : Fin n → K)
  (hx : ∀ i, x i ≠ 0)
  (B : Matrix (Fin n) (Fin n) K)
  (hB : ∀ i j, B i j = (x i) ^ (j.val + 1))
  (A : Matrix (Fin n) (Fin n) K)
  (hA : A = B + Matrix.vecMulVec (fun _ => 1) (fun _ => 1)) :
  A.det = B.det * (2 - ∏ i, (x i - 1) / (x i)) := by
  sorry



theorem theorem_246634_problem (ρ ρ' κ : Matrix (Fin 2) (Fin 2) ℝ)
  (hρ : ρ = !![-1, 0; 0, 1])
  (hρ' : ρ' = !![3/5, -4/5; -4/5, -3/5])
  (hκ : κ = !![1, -2; 2, 1]) :
  ρ' * κ = κ * ρ := by
  sorry





theorem theorem_247113_problem {R : Type*} [CommRing R] (m n : ℕ)
  (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
  Matrix.det (Matrix.fromBlocks A 0 0 B) = Matrix.det A * Matrix.det B := by
  sorry









theorem theorem_246944_problem
  {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (hN : 0 < N)
  (ρ : ℝ) (hρ : ρ ≠ 0)
  (x y : ℕ → Fin N → E)
  (z : ℕ → E)
  (h_init : ∑ i, y 0 i = 0)
  (h_z : ∀ k, z (k + 1) = (1 / N : ℝ) • ∑ i, (x (k + 1) i + (1 / ρ) • y k i))
  (h_y : ∀ k i, y (k + 1) i = y k i + ρ • (x (k + 1) i - z (k + 1))) :
  ∀ k, ∑ i, y k i = 0 := by
  sorry







theorem theorem_246738_problem
  (n : ℕ) (h_n : 0 < n)
  (U : Matrix (Fin n) (Fin n) ℝ)
  (r : Fin n → ℝ)
  (h_Unn : U ⟨n - 1, Nat.sub_lt h_n Nat.zero_lt_one⟩ ⟨n - 1, Nat.sub_lt h_n Nat.zero_lt_one⟩ = 0)
  (h_rn : r ⟨n - 1, Nat.sub_lt h_n Nat.zero_lt_one⟩ = 0)
  (adj : Fin n → ℝ)
  (h_adj : ∀ i : Fin n, adj i = if h : i.val + 1 < n then r ⟨i.val + 1, h⟩ - r i else 0) :
  ¬ ∃ y : Fin n → ℝ, U.mulVec ((Matrix.diagonal y).mulVec adj) = r := by
  sorry

theorem theorem_247300_problem (n k : ℕ) (f : ℝ × (Fin n → ℝ) → ℝ)
  (hf : ContDiff ℝ ⊤ f) (hsupp : HasCompactSupport f) :
  (∑ j in Finset.range (k + 1), ∫ t, ‖iteratedDeriv j (fun u ↦ ∫ y, f (u, y)) t‖) ≤
  ∑ j in Finset.range (k + 1), ∫ p : ℝ × (Fin n → ℝ), ‖iteratedDeriv j (fun u ↦ f (u, p.2)) p.1‖ := by
  sorry







