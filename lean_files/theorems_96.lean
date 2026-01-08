import Mathlib
import Mathlib.Tactic

theorem theorem_516387_problem
  (I : Type*)
  (X : I → Type*)
  (p : Π i, X i)
  (S : (Π i, X i) → Set I)
  (hS : ∀ x, S x = {i | x i ≠ p i})
  (Y : Set (Π i, X i))
  (hY : Y = {x | (S x).Finite})
  (Y_F : Set I → Set (Π i, X i))
  (hY_F : ∀ F, Y_F F = {x | S x ⊆ F}) :
  (⋃ F ∈ {F : Set I | F.Finite}, Y_F F) = Y := by
  sorry

theorem theorem_516292_problem {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (y : X) (f : X → ℝ) (h : ∀ x, f x = ‖x - y‖) :
  Continuous f := by
  sorry

theorem theorem_515835_problem :
  ((5 : ℝ) ^ (1 / 10 : ℝ) * (2 * Real.cos (8 * Real.pi / 25) + 2 * Real.cos (4 * Real.pi / 25) + 1)) /
  (2 * Real.cos (6 * Real.pi / 25) + 2 * Real.cos (Real.pi / 5)) =
  (Real.Gamma (2 / 25) * Real.Gamma (7 / 25) * Real.Gamma (12 / 25)) /
  (Real.Gamma (2 / 5) * Real.Gamma (3 / 25) * Real.Gamma (8 / 25)) := by
  sorry

theorem theorem_516867_problem
  {X : Type*} [TopologicalSpace X]
  {ι : Type*} (S : Finset ι)
  (U : ι → Set X)
  (h_open : ∀ i ∈ S, IsOpen (U i))
  (A : Set X)
  (h_A : A = (⋃ i ∈ S, U i)ᶜ) :
  IsClosed A := by
  sorry





theorem theorem_516611_problem (b c : ℝ) :
  Real.cos b * Real.cos c + Real.sin b * Real.sin c = Real.cos (b - c) := by
  sorry

theorem theorem_516903_problem
  (V : Type*) [Fintype V] [DecidableEq V]
  (G : V → V → Prop) [DecidableRel G]
  (h_tournament : ∀ u v : V, u ≠ v → (G u v ↔ ¬ G v u))
  (n : ℕ) (hn : Fintype.card V = n)
  (σ : Fin n ≃ V)
  (h_median : ∀ σ' : Fin n ≃ V,
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G (σ' p.1) (σ' p.2))).card ≤
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G (σ p.1) (σ p.2))).card) :
  ∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → G (σ i) (σ j) := by
  sorry

theorem theorem_516832_problem
  {Dom RangeF RangeG : Type*}
  (f : Dom → RangeF)
  (g : Dom → RangeG) :
  (∃ t1 t2 : Dom, t1 ≠ t2 ∧ (f t1, g t1) = (f t2, g t2)) ↔
  (∃ t1 t2 : Dom, t1 ≠ t2 ∧ f t1 = f t2 ∧ g t1 = g t2) := by
  sorry







theorem theorem_516527_problem (x : ℝ) (h : x ∈ Set.Icc (-2) 2) :
  ∫ t in (0)..x, Real.sqrt (4 - t^2) = 
  x / 2 * Real.sqrt (4 - x^2) + 2 * Real.arcsin (x / 2) := by
  sorry



theorem theorem_515467_problem (R₁ R₂ ϕ₁ ϕ₂ : ℝ)
  (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) :
  {θ : ℝ | θ ∈ Set.Ico 0 (2 * Real.pi) ∧
    Real.sin (3 * (θ - ϕ₂)) * R₂^3 + Real.sin (θ - ϕ₂) * R₂^3 +
    Real.sin (3 * (θ - ϕ₁)) * R₁^3 + Real.sin (θ - ϕ₁) * R₁^3 = 0}.Finite := by
  sorry



theorem theorem_516992_problem
  (m n : ℕ)
  (F : Type*) [Field F] [Infinite F]
  (A : Fin n → Matrix (Fin m) (Fin m) F)
  (h : (⨅ i, LinearMap.ker (Matrix.toLin' (A i))) = ⊥) :
  ∃ c : Fin n → F, LinearMap.ker (Matrix.toLin' (∑ i, c i • A i)) = ⊥ := by
  sorry

theorem theorem_516056_problem
  (M : Matrix (Fin 2) (Fin 2) ℝ)
  (v₀ : Fin 2 → ℝ)
  (h_det : M.det = 1)
  (h_elliptic : |M.trace| < 2)
  (Ω : Matrix (Fin 2) (Fin 2) ℝ)
  (hΩ : Ω = !![0, -1; 1, 0])
  (Q_s : Matrix (Fin 2) (Fin 2) ℝ)
  (hQs : Q_s = (1/2 : ℝ) • (Ω * M - M.transpose * Ω)) :
  ∀ v : Fin 2 → ℝ,
    Matrix.dotProduct v (Matrix.mulVec Q_s v) - Matrix.dotProduct v₀ (Matrix.mulVec Q_s v₀) = 0 →
    Matrix.dotProduct (Matrix.mulVec M v) (Matrix.mulVec Q_s (Matrix.mulVec M v)) - Matrix.dotProduct v₀ (Matrix.mulVec Q_s v₀) = 0 := by
  sorry

theorem theorem_517118_problem 
  {α D : Type*} 
  (E : D → (α → ℝ) → ℝ) 
  (A B : D → α → ℝ) 
  (w : ℝ) 
  (hw : 0 < w ∧ w < 1)
  (hA : ∀ (F Q : D), F ≠ Q → E F (A Q) > E F (A F))
  (hB : ∀ (F Q : D), F ≠ Q → E F (B Q) > E F (B F))
  (h_lin : ∀ (F Q : D), E F (fun x => w * A Q x + (1 - w) * B Q x) = 
                        w * E F (A Q) + (1 - w) * E F (B Q)) :
  ∀ (F Q : D), F ≠ Q → 
    E F (fun x => w * A Q x + (1 - w) * B Q x) > 
    E F (fun x => w * A F x + (1 - w) * B F x) := by
  sorry

theorem theorem_517027_problem (U V : Set ℂ) (hU : IsOpen U) (hV : IsOpen V) (f : ℂ → ℂ)
  (h_holo : DifferentiableOn ℂ f U)
  (h_bij : Set.BijOn f U V)
  (h_inv : ContinuousOn (Function.invFunOn f U) V) :
  ∀ z ∈ U, deriv f z ≠ 0 := by
  sorry

theorem theorem_517486_problem (x : ℕ → ℝ) (hx : CauchySeq x) :
  CauchySeq (fun n ↦ |x n|) := by
  sorry

theorem theorem_517106_problem (n : ℕ) (f : ℂ → ℂ)
  (h_holo : Differentiable ℂ f)
  (h_deriv : ∀ z, (deriv^[n + 1] f) z = 0) :
  ∃ p : Polynomial ℂ, p.degree ≤ n ∧ ∀ z, f z = p.eval z := by
  sorry





theorem theorem_516451_problem (G : Type*) [Group G] [Fintype G]
  (hG : Fintype.card G = 36) :
  (∃ P : Sylow 2 G, Subgroup.Normal (P : Subgroup G)) ∨
  (∃ P : Sylow 3 G, Subgroup.Normal (P : Subgroup G)) := by
  sorry





theorem theorem_516957_problem
  (t : ℝ)
  (ht : 0 ≤ t)
  (ζ : ℝ → ℝ)
  (h_int : IntervalIntegrable (fun s ↦ (ζ s)^2) volume 0 t)
  (ξ : ℝ)
  (hξ : ξ = ∫ s in (0)..t, (ζ s)^2)
  (W_xi : ℝ)
  (int_W_dW : ℝ)
  (int_zeta_dW2 : ℝ)
  (h_notation : int_zeta_dW2 = ∫ s in (0)..t, (ζ s)^2)
  (h_ito : W_xi^2 = 2 * int_W_dW + ξ) :
  int_zeta_dW2 = W_xi^2 - 2 * int_W_dW := by
  sorry

theorem theorem_517156_problem
  (Knot : Type*)
  (V : Knot → ℝ)
  (IsHyperbolic : Knot → Prop)
  (K : Knot)
  (h : V K > 2) :
  IsHyperbolic K := by
  sorry

theorem theorem_517149_problem (x y z : ℝ) :
  |x - z| ≤ |x + y| + |z + y| := by
  sorry







theorem theorem_517643_problem
  (x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ x y z : ℝ)
  (a b c : ℝ)
  (hP_A : (x - x₁)^2 + (y - y₁)^2 + (z - z₁)^2 = a^2)
  (hP_B : (x - x₂)^2 + (y - y₂)^2 + (z - z₂)^2 = b^2)
  (hP_C : (x - x₃)^2 + (y - y₃)^2 + (z - z₃)^2 = c^2)
  (h_unique : ∃! p : ℝ × ℝ × ℝ,
    (p.1 - x₁)^2 + (p.2.1 - y₁)^2 + (p.2.2 - z₁)^2 = a^2 ∧
    (p.1 - x₂)^2 + (p.2.1 - y₂)^2 + (p.2.2 - z₂)^2 = b^2 ∧
    (p.1 - x₃)^2 + (p.2.1 - y₃)^2 + (p.2.2 - z₃)^2 = c^2) :
  ∀ p : ℝ × ℝ × ℝ,
    ((p.1 - x₁)^2 + (p.2.1 - y₁)^2 + (p.2.2 - z₁)^2 = a^2 ∧
     (p.1 - x₂)^2 + (p.2.1 - y₂)^2 + (p.2.2 - z₂)^2 = b^2 ∧
     (p.1 - x₃)^2 + (p.2.1 - y₃)^2 + (p.2.2 - z₃)^2 = c^2) ↔
    p = (x, y, z) := by
  sorry

theorem theorem_517734_problem (x y : ℕ) (hx : x > 0) (hy : y > 0)
  (h : x * Nat.totient x = y * Nat.totient y) : x = y := by
  sorry

theorem theorem_518137_problem (n : ℕ) :
  ∑ k in Finset.range (n + 1), (Nat.choose n k)^2 = Nat.choose (2 * n) n := by
  sorry

theorem theorem_517525_problem
  (X : Set ℝ)
  (f : ℝ → ℝ)
  (p L : ℝ)
  (hX_discrete : ∀ x ∈ X, ∃ ε > 0, Metric.ball x ε ∩ X = {x})
  (hp_not_mem : p ∉ X)
  (hp_isolated : ∃ δ > 0, Metric.ball p δ ∩ X = ∅)
  (hL : L ∈ f '' X) :
  Filter.Tendsto f (nhdsWithin p X) (nhds L) := by
  sorry





theorem theorem_517690_problem (f : ℝ → ℝ)
  (h : ∀ x, f x = (x * Real.exp x - 2 + 2 * Real.cos x - x) / ((Real.sin x)^2 * Real.tan (2 * x))) :
  Filter.Tendsto f (nhds 0) (nhds (1 / 4)) := by
  sorry





theorem theorem_518270_problem (B₁ C₁ F₁ B₂ C₂ F₂ : ℝ)
  (rotation_difference axis_length_ratio_difference size_difference total_difference : ℝ)
  (h1 : rotation_difference = |B₁ - B₂|)
  (h2 : axis_length_ratio_difference = |C₁ - C₂|)
  (h3 : size_difference = |F₁ - F₂|)
  (h4 : total_difference = rotation_difference + axis_length_ratio_difference + size_difference) :
  total_difference = |B₁ - B₂| + |C₁ - C₂| + |F₁ - F₂| := by
  sorry











theorem theorem_518470_problem (n : ℤ) (h : 0 < n) :
  ∃ a0 a1 a2 a3 : ℤ, n = a0^2 + a1^2 + a2^2 + a3^2 := by
  sorry









theorem theorem_518644_problem (R : Type*) [Ring R] (M : Type*) [AddCommGroup M] [Module R M] :
  Nonempty (((M →₀ R) ⧸ LinearMap.ker (Finsupp.total M M R (id : M → M))) ≃ₗ[R] M) := by
  sorry













theorem theorem_518915_problem (n_theta n_phi : ℕ)
  (polar_crossings non_polar_crossings : ℕ)
  (h_polar : polar_crossings = n_theta * (n_theta + 1))
  (h_non_polar : non_polar_crossings = n_theta * n_phi) :
  polar_crossings + non_polar_crossings = n_theta * (n_phi + n_theta + 1) := by
  sorry







theorem theorem_519539_problem (u : ℝ) (h1 : 0 < u) (h2 : u < 1) :
  HasDerivAt (fun x => Real.log ((1 + x) / (1 - x))) ((2 * u) / (u - u ^ 3)) u := by
  sorry

theorem theorem_518582_problem (B C : ℕ → ℚ)
  (hB0 : B 0 = 1)
  (hB1 : B 1 = 1/2)
  (hB_rec : ∀ n, 2 ≤ n → B n = 1 - ∑ k in Finset.range n, (Nat.choose n k : ℚ) * B k / (n - k + 1 : ℚ))
  (hC0 : C 0 = 1)
  (hC1 : C 1 = 1/2)
  (hC_rec : ∀ n, 2 ≤ n → C n = 1 - ∑ k in Finset.range n, (Nat.choose n k : ℚ) * C k / (n - k + 1 : ℚ)) :
  B = C := by
  sorry







theorem theorem_520228_problem (G g bt p₁ p₂ : ℝ)
  (hbt : bt > 0) (hg : g ≠ 0)
  (hp1 : p₁ > 0) (hp2 : p₂ > 0) :
  ∫ x in p₁..p₂, (G^2 / g) * (x / bt) * deriv (fun y => bt / y) x =
  (G^2 / g) * Real.log (p₁ / p₂) := by
  sorry







theorem theorem_520038_problem (f : ℕ → ℕ) (hf : ¬ Computable f) :
  ¬ ∃ p : ℕ → Nat.Partrec.Code, Computable p ∧ 
    ∀ n x, (p n).eval x = Part.some (f n) := by
  sorry



theorem theorem_520139_problem
  (n : ℕ)
  (R : Type*) [CommRing R]
  (X Y Z : Matrix (Fin n) (Fin n) R) :
  Matrix.trace (X * Y * Z) = Matrix.trace (Y * Z * X) ∧
  Matrix.trace (Y * Z * X) = Matrix.trace (Z * X * Y) := by
  sorry

theorem theorem_520200_problem (X : Set ℝ) (d : ℝ → ℝ → ℝ)
  (hX : X = {x | ∃ n : ℕ, n > 0 ∧ x = 1 / (n : ℝ)})
  (h_d_ne : ∀ x y, x ∈ X → y ∈ X → x ≠ 1 → y ≠ 1 → d x y = |x - y|)
  (h_d_1n : ∀ n : ℕ, n > 1 → d 1 (1 / (n : ℝ)) = 1 / (n : ℝ))
  (h_d_11 : d 1 1 = 0)
  (h_symm : ∀ x y, x ∈ X → y ∈ X → d x y = d y x) :
  ∀ ε > 0, ∃ N : ℕ, N > 0 ∧ ∀ n : ℕ, n ≥ N → d (1 / (n : ℝ)) 1 < ε := by
  sorry

theorem theorem_520471_problem (a b n k : ℤ)
  (hk : 1 ≤ k)
  (hn : 1 ≤ n)
  (h : Int.ModEq (k * n) a b) :
  Int.ModEq (k ^ 2 * n) (a ^ k.natAbs) (b ^ k.natAbs) := by
  sorry





theorem theorem_520910_problem (T : ℝ → ℝ)
  (h_base : ∀ n, 0 < n → n ≤ 1 → T n = 1)
  (h_rec : ∀ n, 1 < n → T n = T (n / 7) + T (11 * n / 14) + n) :
  (fun n ↦ T n) =Θ[atTop] (fun n ↦ n) := by
  sorry

theorem theorem_520591_problem (x y L k : ℝ)
  (hk : k > 0)
  (hx : ∀ z : ℤ, x / L ≠ z)
  (hy : ∀ z : ℤ, y / L ≠ z)
  (hxy : ∀ z : ℤ, x ≠ y + z * L) :
  ¬ Summable (fun n : ℕ => Real.sin (n * Real.pi * x / L) * Real.sin (n * Real.pi * y / L) * Real.sqrt (k^2 + (n : ℝ)^2 * Real.pi^2 / L^2)) := by
  sorry





theorem theorem_521299_problem (n : ℕ) (x : Fin n → ℝ) :
  @MeasurableSet (Fin n → ℝ) (borel (Fin n → ℝ)) {x} := by
  sorry



theorem theorem_521265_problem
  (L : ℝ)
  (n : ℕ)
  (x : Fin n → ℝ)
  (w : Fin n → ℝ)
  (f : ℝ → ℝ → ℝ → ℝ)
  (hL : L > 0)
  (hf : Continuous (fun p : ℝ × ℝ × ℝ ↦ f p.1 p.2.1 p.2.2))
  (h_quad_1d : ∀ (g : ℝ → ℝ), Continuous g →
    ∫ t in (-L/2)..(L/2), g t = ∑ i, w i * g (x i)) :
  ∫ z in (-L/2)..(L/2), ∫ y in (-L/2)..(L/2), ∫ x_val in (-L/2)..(L/2), f x_val y z =
  ∑ k, ∑ j, ∑ i, w k * w j * w i * f (x i) (x j) (x k) := by
  sorry

theorem theorem_521821_problem (K L : Type*) [Field K] [Field L] [Algebra K L]
  (β : L) (f : Polynomial K) (hf : f = minpoly K β) :
  IsSeparable K β ↔ f.Separable := by
  sorry

theorem theorem_521060_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (S : Set V)
  (h_indep : LinearIndependent F (Subtype.val : S → V))
  (h_span : Submodule.span F S = ⊤) :
  ∃ b : Basis S F V, ∀ s : S, b s = s := by
  sorry







theorem theorem_520958_problem :
  ¬ ∀ (F : ℝ → Set ℝ),
    IsClosed {p : ℝ × ℝ | p.1 ∈ Set.Icc 0 1 ∧ p.2 ∈ F p.1} →
    ∃ (ι : Type) (f : ι → ℝ → ℝ),
      (∀ i, ContinuousOn (f i) (Set.Icc 0 1)) ∧
      (∀ x ∈ Set.Icc 0 1, F x = {y | ∃ i, f i x = y}) := by
  sorry





theorem theorem_522382_problem
  (Theory : Type)
  (MathObject : Type)
  (definable : Theory → MathObject → Prop)
  (equivalent_objects : MathObject → MathObject → Prop)
  (ZFC ETCS_plus : Theory)
  -- Condition: ETCS+ is augmented to ensure expressiveness equivalent to ZFC.
  -- This implies a bidirectional correspondence between definable structures.
  (h_expressiveness_equiv : 
    (∀ x, definable ZFC x → ∃ y, definable ETCS_plus y ∧ equivalent_objects x y) ∧ 
    (∀ y, definable ETCS_plus y → ∃ x, definable ZFC x ∧ equivalent_objects x y)) :
  -- Conclusion: For any mathematical structure or property definable within ZFC, 
  -- there exists an equivalent structure or property definable within ETCS+.
  ∀ x, definable ZFC x → ∃ y, definable ETCS_plus y ∧ equivalent_objects x y := by
  sorry



theorem theorem_522188_problem (a : ℤ) (n p m : ℕ) (c : ℕ → ℕ)
  (hn : n > 0)
  (hp : Nat.Prime p)
  (h_decomp : n = ∑ k in Finset.range (m + 1), c k * 2 ^ k)
  (hc : ∀ k ≤ m, c k = 0 ∨ c k = 1) :
  (a ^ n) % p = (∏ k in Finset.range (m + 1), ((a ^ (2 ^ k)) % p) ^ (c k)) % p := by
  sorry



theorem theorem_522471_problem (a b c d : ℤ)
  (h_distinct : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
  (h1 : ∃ k : ℕ, a + b = 2^k)
  (h2 : ∃ k : ℕ, a + c = 2^k)
  (h3 : ∃ k : ℕ, a + d = 2^k)
  (h4 : ∃ k : ℕ, b + c = 2^k)
  (h5 : ∃ k : ℕ, b + d = 2^k) :
  False := by
  sorry

