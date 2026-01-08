import Mathlib
import Mathlib.Tactic

theorem theorem_726262_problem (x y k : ℕ)
  (hx : x > 0) (hy : y > 0) (hk : k > 0)
  (h : x^2 * y + x + y = k * x * y^2 + k * y + 11 * k) :
  x = 11 * k^2 ∧ y = 11 * k := by
  sorry



theorem theorem_727506_problem (x : Matrix (Fin 4) (Fin 4) ℝ)
  (h_line : ∃ p q : Fin 4 → ℝ, x = fun i j ↦ p i * q j - p j * q i) :
  x 0 1 * x 2 3 - x 0 2 * x 1 3 + x 0 3 * x 1 2 = 0 := by
  sorry



theorem theorem_727842_problem
  (k L A B : Type*)
  [Field k] [Field L] [Field A] [Field B]
  [Algebra k L] [Algebra L A] [Algebra A B]
  [Algebra k A] [IsScalarTower k L A]
  [Algebra k B] [IsScalarTower k A B]
  (V_L : Type*) [AddCommGroup V_L] [Module L V_L]
  [FiniteDimensional k L] [FiniteDimensional k A] [FiniteDimensional k B] [FiniteDimensional L V_L]
  (h1 : FiniteDimensional.finrank k A * FiniteDimensional.finrank k L = (FiniteDimensional.finrank L V_L) ^ 2 * FiniteDimensional.finrank k L)
  (h2 : FiniteDimensional.finrank k B * FiniteDimensional.finrank k A = (FiniteDimensional.finrank L V_L) ^ 2 * (FiniteDimensional.finrank k L) ^ 2) :
  FiniteDimensional.finrank k B = (FiniteDimensional.finrank k L) ^ 2 := by
  sorry



theorem theorem_727926_problem {Domain Range : Type*} [LE Range]
  (F_X : Domain → Range) (beta : Range) :
  ∀ x : Domain, x ∈ {y : Domain | F_X y ≥ beta} ↔ F_X x ≥ beta := by
  sorry

theorem theorem_727728_problem
  (n : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (v x : Fin n → ℝ)
  (f : (Fin n → ℝ) → ℝ)
  (hf : ∀ y, f y = Matrix.dotProduct y (A.mulVec y)) :
  deriv (fun t : ℝ => f (x + t • v)) 0 = Matrix.dotProduct ((A.transpose + A).mulVec v) x := by
  sorry

theorem theorem_727882_problem
  (n k : ℕ)
  (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k))
  (h : EuclideanSpace ℝ (Fin k) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hg : DifferentiableAt ℝ g x)
  (hh : DifferentiableAt ℝ h (g x)) :
  fderiv ℝ (h ∘ g) x = (innerSL ℝ (gradient h (g x))).comp (fderiv ℝ g x) := by
  sorry



theorem theorem_728364_problem (f : ℝ → ℝ) (a r : ℝ)
  (hf : DifferentiableAt ℝ f r)
  (h_pos : f r > 0)
  (ha : a > 0)
  (h_denom : 1 + Real.log (a / f r) ≠ 0) :
  HasDerivAt (fun x => - Real.log (|1 + Real.log (a / f x)|)) 
    ((deriv f r / f r) * (1 / (1 + Real.log (a / f r)))) r := by
  sorry

theorem theorem_727274_problem
  (F : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ)) -- Fourier transform denoted as Linear Map
  (F_inv : (ℝ → ℂ) → (ℝ → ℂ)) -- Inverse Fourier transform
  (h_inv : ∀ f, F (F_inv f) = f) -- Relationship between F and F_inv
  (h : ℝ → ℂ) -- The function h(y) in the Fourier domain
  (β : ℂ) -- The eigenvalue
  -- Sufficiently smooth assumption for the spatial function
  (h_smooth : ContDiff ℝ ⊤ (F_inv h))
  -- Definition of the operator M'
  (M' : (ℝ → ℂ) → (ℝ → ℂ))
  (hM' : ∀ f z, M' f z = z * deriv f z)
  -- The eigenvalue equation condition in the spatial domain
  (h_eigen : M' (F_inv h) = fun z => β * (F_inv h) z) :
  -- Conclusion: The eigenvalue is invariant (h satisfies the transformed equation)
  F (M' (F_inv h)) = fun y => β * h y := by
  sorry



theorem theorem_728522_problem {X Y : Type*} (f : X → Y) (A B : Set Y)
  (h : A ∩ B = ∅) :
  f ⁻¹' A ∩ f ⁻¹' B = ∅ := by
  sorry

theorem theorem_728552_problem (y : ℝ → ℝ) :
  (Differentiable ℝ y ∧ Differentiable ℝ (deriv y) ∧
   ∀ x : ℝ, (x^2 - 1) * deriv (deriv y) x - 2 * x * deriv y x + 2 * y x = 1) ↔
  (∃ A B : ℝ, ∀ x : ℝ, y x = A * (x^2 + 1) + B * x + 1 / 2) := by
  sorry

theorem theorem_728318_problem (v : ℝ) (f g : ℝ → ℝ)
  (hv : 0 < v) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
  let ψ : ℝ → ℝ → ℝ := fun x t ↦ f (x + v * t) + g (x - v * t)
  ∀ x t : ℝ, deriv (fun x ↦ deriv (fun x ↦ ψ x t) x) x =
             (1 / v ^ 2) * deriv (fun t ↦ deriv (fun t ↦ ψ x t) t) t := by
  sorry











theorem theorem_729139_problem :
  Nonempty (Matrix.orthogonalGroup (Fin 0) ℝ ≃* PUnit) ∧
  Nonempty (Matrix.specialOrthogonalGroup (Fin 0) ℝ ≃* PUnit) ∧
  Nonempty (Matrix.unitaryGroup (Fin 0) ℂ ≃* PUnit) ∧
  Nonempty (Matrix.specialUnitaryGroup (Fin 0) ℂ ≃* PUnit) := by
  sorry





theorem theorem_728640_problem
  (a : ℕ → ℝ)
  (L ε : ℝ)
  (hL : L > 0)
  (hε : ε > 0)
  (h_seq : ∀ n, a (n + 1) < (L + ε) * a n)
  (k : ℕ) (hk : k > 0)
  (n : ℕ) :
  a (n + k) < (L + ε) ^ k * a n := by
  sorry



theorem theorem_728400_problem
  (R : Type*) [CommRing R] [IsNoetherianRing R]
  (I : ℕ → Ideal R)
  (h_coprime : Pairwise (fun i j => I i + I j = ⊤))
  (h_conv : ∀ (s : ℕ → R),
    (∀ k, ∃ N, ∀ n ≥ N, ∀ m ≥ N, s n - s m ∈ ⨅ i ∈ Finset.range k, I i) →
    ∃ r, ∀ k, ∃ N, ∀ n ≥ N, s n - r ∈ ⨅ i ∈ Finset.range k, I i) :
  ∀ (a : Π i, R ⧸ I i), ∃ r : R, ∀ i, Ideal.Quotient.mk (I i) r = a i := by
  sorry

theorem theorem_729218_problem
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (T : V → W) (f : W → ℝ) (y : V)
  (dT : V →L[ℝ] W) (df : W →L[ℝ] ℝ)
  (hT : ∀ h : V, HasDerivAt (fun t : ℝ => T (y + t • h)) (dT h) 0)
  (hf : ∀ k : W, HasDerivAt (fun t : ℝ => f (T y + t • k)) (df k) 0) :
  ∀ h : V, HasDerivAt (fun t : ℝ => f (T (y + t • h))) (df (dT h)) 0 := by
  sorry



theorem theorem_728858_problem {R : Type*} [CommRing R] (I J : Ideal R)
  (h : Function.Surjective (RingHom.prod (Ideal.Quotient.mk I) (Ideal.Quotient.mk J))) :
  I + J = ⊤ := by
  sorry





theorem theorem_729358_problem (r θ : ℝ) :
  let φ : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
  LinearMap.det (fderiv ℝ φ (r, θ)).toLinearMap = r := by
  sorry







theorem theorem_729703_problem
  (n : ℕ)
  (f : ℝ → (Fin n → ℝ) → ℝ)
  (h1 : ∀ t x, deriv (fun s => f s x) t = 0)
  (h2 : ∀ t x i, deriv (fun u => f t (Function.update x i u)) (x i) = 2 * x i)
  (h3 : ∀ t x i, deriv (fun v => deriv (fun u => f t (Function.update x i u)) v) (x i) = 2) :
  (∀ t x, deriv (fun s => f s x) t + (1 / 2) * ∑ i : Fin n, deriv (fun v => deriv (fun u => f t (Function.update x i u)) v) (x i) = n) ∧
  (∀ t x i, deriv (fun u => f t (Function.update x i u)) (x i) = 2 * x i) := by
  sorry

theorem theorem_729629_problem
  {X : Type*} [TopologicalSpace X]
  (D : Set X)
  (hD_compact : IsCompact D)
  (hD_nonempty : D.Nonempty)
  (f : D → ℝ)
  (hf_usc : UpperSemicontinuous f) :
  ∃ x : D, f x = sSup (Set.range f) := by
  sorry



theorem theorem_729723_problem (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
  (fun (n : ℕ) => (∫ x in (0 : ℝ)..1,
    ((1 - p + p * x) ^ n - x ^ ((n : ℝ) * p) - (1 - p) ^ n * (1 - x) ^ n) / (x * (1 - x))) -
    (1 - p) / (2 * p * n))
  =O[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  sorry





theorem theorem_730371_problem (N p : ℕ)
  (Y : Matrix (Fin N) (Fin 1) ℝ)
  (X : Matrix (Fin N) (Fin p) ℝ)
  (hN : 0 < N)
  (h_rank : Invertible (X.transpose * X)) :
  let P_X_perp : Matrix (Fin N) (Fin N) ℝ := 1 - X * (X.transpose * X)⁻¹ * X.transpose
  let β_hat := (X.transpose * X)⁻¹ * X.transpose * Y
  let r := Y - X * β_hat
  (1 / (N : ℝ)) • (r.transpose * r) = (1 / (N : ℝ)) • (Y.transpose * P_X_perp * Y) := by
  sorry

theorem theorem_730416_problem
  -- Let is_solution U f be the predicate that U(x, t) is a solution to the PDE
  -- on the spatial domain x ∈ [-1, 1] and time t ≥ 0 with initial condition U(x, 0) = f(x)
  -- and appropriately defined boundary conditions.
  (is_solution : (ℝ → ℝ → ℝ) → (ℝ → ℝ) → Prop)
  -- Let f(x) be the specific initial condition
  (f : ℝ → ℝ)
  -- f(x) is a continuous function on [-1, 1]
  (hf : ContinuousOn f (Set.Icc (-1) 1))
  -- The PDE is assumed to be well-posed.
  -- Well-posedness implies that for any continuous initial data g,
  -- a solution exists and is unique.
  (h_well_posed : ∀ g : ℝ → ℝ, ContinuousOn g (Set.Icc (-1) 1) →
    ∃! U : ℝ → ℝ → ℝ, is_solution U g) :
  -- Prove that the solution U(x, t) exists and is unique for the given f
  ∃! U : ℝ → ℝ → ℝ, is_solution U f := by
  sorry







theorem theorem_730118_problem
  (Qi V Cu K Xnu ci0 : ℝ)
  (ci : ℝ → ℝ)
  (hQi : Qi ≠ 0)
  (hV : V ≠ 0)
  (h_diff : Differentiable ℝ ci)
  (h_ode : ∀ t, deriv ci t + ci t * (Qi / V) = (Cu * K * Xnu) / V)
  (h_init : ci 0 = ci0) :
  ∀ t, ci t = (Cu * K * Xnu) / Qi + (ci0 - (Cu * K * Xnu) / Qi) * Real.exp (-(Qi * t) / V) := by
  sorry

theorem theorem_730718_problem (a b : ℝ) (f : ℝ → ℝ)
  (h_lt : a < b)
  (h_cont : ContinuousOn f (Set.Icc a b))
  (h_diff : DifferentiableOn ℝ f (Set.Ioo a b)) :
  ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a) := by
  sorry













theorem theorem_730899_problem
  {X ι : Type*} [Fintype ι] [Nonempty ι]
  (ds : ι → X → X → ℝ)
  (h_metric : ∀ i, (∀ x y, 0 ≤ ds i x y) ∧
                   (∀ x y, ds i x y = 0 ↔ x = y) ∧
                   (∀ x y, ds i x y = ds i y x) ∧
                   (∀ x y z, ds i x z ≤ ds i x y + ds i y z)) :
  let d := λ x y ↦ Finset.univ.sup' Finset.univ_nonempty (λ i ↦ ds i x y)
  (∀ x y, 0 ≤ d x y) ∧
  (∀ x y, d x y = 0 ↔ x = y) ∧
  (∀ x y, d x y = d y x) ∧
  (∀ x y z, d x z ≤ d x y + d y z) := by
  sorry

























theorem theorem_731870_problem
  (K : Type*) [Field K]
  (G : Type*) [Group G] [Fintype G]
  (M : Type*) [AddCommGroup M] [Module (MonoidAlgebra K G) M]
  (h_char : ¬ ringChar K ∣ Fintype.card G)
  (M₁ : Submodule (MonoidAlgebra K G) M) :
  ∃ M₂ : Submodule (MonoidAlgebra K G) M, IsCompl M₁ M₂ := by
  sorry



theorem theorem_731609_problem
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (i : Fin m)
  (S : Set (Fin m))
  (hS : i ∉ S) :
  (A i ∈ Submodule.span ℝ (A '' S)) ↔
  (FiniteDimensional.finrank ℝ (Submodule.span ℝ (A '' (insert i S))) =
   FiniteDimensional.finrank ℝ (Submodule.span ℝ (A '' S))) := by
  sorry

theorem theorem_731869_problem
  (h_pillai : ∀ a b k : ℤ, 1 < a → 1 < b → k ≠ 0 →
    Set.Finite { p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ a ^ p.1 - b ^ p.2 = k }) :
  Set.Finite { p : ℤ × ℤ | p.1 > 1 ∧ p.2 > 1 ∧ p.1 * p.2 ≠ 0 ∧
    2 * (5 : ℤ) ^ p.1.toNat - (7 : ℤ) ^ p.2.toNat = 1 } := by
  sorry











theorem theorem_731953_problem (f : ℝ × ℝ → ℝ)
  (h : ∀ p : ℝ × ℝ, f p = if p = 0 then 0 else (p.1 * p.2 * (p.1 ^ 2 - p.2 ^ 2)) / (p.1 ^ 2 + p.2 ^ 2) ^ 2) :
  ¬ DifferentiableAt ℝ f 0 := by
  sorry



theorem theorem_731700_problem :
  Set.Countable {b : ℂ | ¬ IsAlgebraic ℚ b ∧ IsAlgebraic ℚ (b ^ b)} := by
  sorry

theorem theorem_732230_problem (x : ℝ) :
  let expected_gain_A := (0.5 * (0.5 * x) + 0.5 * (2 * x)) - (0.5 * (0.5 * x) + 0.5 * (2 * x))
  let expected_gain_B := (0.5 * (0.5 * x) + 0.5 * (2 * x)) - (0.5 * (0.5 * x) + 0.5 * (2 * x))
  expected_gain_A = 0 ∧ expected_gain_B = 0 := by
  sorry

theorem theorem_732746_problem (θ : ℝ) :
  Real.cos (6 * θ) = 32 * (Real.cos θ)^6 - 48 * (Real.cos θ)^4 + 18 * (Real.cos θ)^2 - 1 := by
  sorry



theorem theorem_732758_problem (a b x0 : ℝ) (x : ℝ → ℝ)
  (ha : 0 ≤ a) (hb : 0 ≤ b)
  (hx_diff : Differentiable ℝ x)
  (hx_ode : ∀ t, 0 ≤ t → deriv x t = a - b * Real.sin (x t))
  (hx_init : x 0 = x0) :
  ∀ t, 0 ≤ t → |x t| ≤ |x0| + (a + b) * t := by
  sorry



theorem theorem_732003_problem (x : ℝ) (h : x = 2 * Real.pi / (2 ^ 100 + 1 : ℝ)) :
  ¬ LinearIndependent ℝ (fun i : Fin 100 => Real.cos (2 ^ (i : ℕ) * x)) := by
  sorry



theorem theorem_732709_problem
  {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  (f : X → Y) (a : X)
  (h_cont : ContinuousAt f a)
  (h_not_bd : a ∉ frontier (Set.univ : Set X))
  (x : ℕ → X)
  (h_conv : Filter.Tendsto x Filter.atTop (nhds a)) :
  Filter.Tendsto (fun n ↦ f (x n)) Filter.atTop (nhds (f a)) := by
  sorry









theorem theorem_732698_problem (x k a : ℝ)
  (hx : x ≠ 0)
  (hk : k ≠ 0)
  (hx1 : x ≠ 1)
  (ha : a ≠ 1)
  (h : a / (1 - a) * x^2 + a * x = 1 / (2 * k)) :
  a = (1 - 2 * k * x^2) / (2 * k * x - 2 * k * x^2) := by
  sorry

theorem theorem_732861_problem
  (h f g Fx Fy : ℝ → ℝ)
  (P : Set ℝ → ℝ)
  (h_bijective : Function.Bijective h)
  (h_diff : Differentiable ℝ h)
  (h_inv_diff : Differentiable ℝ (Function.invFun h))
  (h_mono : StrictMono h ∨ StrictAnti h)
  (P_compl : ∀ s, P sᶜ = 1 - P s)
  (P_continuity : ∀ a, P {t | t < a} = P {t | t ≤ a})
  (Fx_def : ∀ x, Fx x = P {t | t ≤ x})
  (Fy_def : ∀ y, Fy y = P {t | h t ≤ y})
  (f_is_pdf : ∀ x, HasDerivAt Fx (f x) x)
  (g_is_pdf : ∀ y, HasDerivAt Fy (g y) y) :
  ∀ y, g y = f (Function.invFun h y) * |deriv (Function.invFun h) y| := by
  sorry



theorem theorem_732895_problem (a : ℕ → ℝ) (S : ℝ)
  (h_conv : Filter.Tendsto (fun n ↦ ∑ i in Finset.range n, a i) Filter.atTop (nhds S))
  (b : ℕ → ℝ)
  (hb : ∀ n, b n = if Even n then a (n + 1) else a (n - 1)) :
  Filter.Tendsto (fun n ↦ ∑ i in Finset.range n, b i) Filter.atTop (nhds S) := by
  sorry

theorem theorem_733328_problem (a b c d : ℝ) :
  a^4 + b^4 + c^4 + d^4 + 4 * a * b * c * d =
  (a + b + c + d) * (a^3 + b^3 + c^3 + d^3 + a * b * c + a * b * d + a * c * d + b * c * d) -
  (a^2 + b^2 + c^2 + d^2) * (a * b + a * c + a * d + b * c + b * d + c * d) := by
  sorry





theorem theorem_733179_problem (b k : ℕ) (f : ℕ → ℝ)
  (hb : b ≥ 2) (hk : k ≥ 1) :
  ∑ m in Finset.range (b ^ k), ∏ i in Finset.range k, f ((m / b ^ i) % b) =
  (∑ j in Finset.range b, f j) ^ k := by
  sorry

