import Mathlib
import Mathlib.Tactic

theorem theorem_787814_problem (m n : ℤ) (θ : ℝ)
  (hθ : θ = (m : ℝ) * Real.pi / (n : ℝ))
  (h_rat : ∃ q : ℚ, Real.sin θ = (q : ℝ)) :
  Real.sin θ ∈ ({0, 1/2, -1/2, 1, -1} : Set ℝ) := by
  sorry



theorem theorem_788939_problem (n : ℕ) (hn : n > 0) :
  ∃ (G : Type) (_ : Group G) (_ : Fintype G), Fintype.card G = n := by
  sorry



theorem theorem_788262_problem
  (F K L : Type*) [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra F L] [Algebra K L] [IsScalarTower F K L]
  [IsGalois F L]
  (H : Subgroup (L ≃ₐ[F] L))
  (hH : ∀ σ : L ≃ₐ[F] L, σ ∈ H ↔ ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
  (R : Set (L ≃ₐ[F] L))
  (hR : ∀ τ : L ≃ₐ[F] L, ∃! p : H × R, τ = (p.1 : L ≃ₐ[F] L) * (p.2 : L ≃ₐ[F] L)) :
  (Set.univ : Set (K →ₐ[F] L)) =
    { φ | ∃ σ ∈ R, φ = (σ.symm : L ≃ₐ[F] L).toAlgHom.comp (IsScalarTower.toAlgHom F K L) } := by
  sorry



theorem theorem_788786_problem
  (f : ℝ → ℝ) (B : ℝ → ℝ) (t : ℝ)
  -- S and I are the Stratonovich and Itô integral operators respectively,
  -- mapping a function (the integrand) to a real value (the integral over [0, t] along B).
  (S : (ℝ → ℝ) → ℝ)
  (I : (ℝ → ℝ) → ℝ)
  (hf : ContDiff ℝ 2 f)
  -- Condition: The Stratonovich integral satisfies the Chain Rule.
  -- For any C¹ function F, F(B_t) - F(B_0) = ∫ F'(B_s) ∘ dB_s.
  (h_strat_chain : ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → F (B t) = F (B 0) + S (deriv F))
  -- Condition: The Itô integral satisfies Itô's Formula.
  -- For any C² function F, F(B_t) - F(B_0) = ∫ F'(B_s) dB_s + (1/2)∫ F''(B_s) ds.
  (h_ito_formula : ∀ F : ℝ → ℝ, ContDiff ℝ 2 F →
    F (B t) = F (B 0) + I (deriv F) + (1 / 2) * ∫ s in (0)..t, deriv (deriv F) (B s)) :
  -- Conclusion: The conversion formula holds for f.
  S f = I f + (1 / 2) * ∫ s in (0)..t, deriv f (B s) := by
  sorry



theorem theorem_788625_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  [NormedAddCommGroup (Matrix n n ℝ)]
  [NormedSpace ℝ (Matrix n n ℝ)]
  (h_submul : ∀ A B : Matrix n n ℝ, ‖A * B‖ ≤ ‖A‖ * ‖B‖)
  (M : Matrix n n ℝ)
  (hM : ‖M‖ < 1) :
  IsUnit (1 + M) := by
  sorry



theorem theorem_788555_problem
  (p q r : ℤ)
  (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
  (h_sq : IsSquare (p^2 + r^2))
  (a b c k : ℤ)
  (ha : a = p * (q^2 + r^2))
  (hb : b = q * (p^2 + r^2))
  (hc : c = (p + q) * (p * q - r^2))
  (hk : k^2 = (p^2 + r^2) * (p * q - r^2)^2) :
  b * c * (b + c - a) = k^2 * (a + b + c) := by
  sorry

theorem theorem_788774_problem 
  (m E hbar : ℝ) 
  (I : Set ℝ) 
  (V : ℝ → ℝ) 
  (psi : ℝ → ℂ)
  (h_hbar : hbar ≠ 0)
  (hV : ContinuousOn V I)
  (h_sol : ∀ x ∈ I, DifferentiableAt ℝ (deriv psi) x ∧ 
    deriv (deriv psi) x + ((2 * m) / hbar ^ 2 : ℂ) * ((E - V x) : ℂ) * psi x = 0) :
  ContinuousOn psi I := by
  sorry





theorem theorem_788766_problem (x : ℝ) (N : ℕ) (h : Real.sin (x / 2) ≠ 0) :
  ∑ n in Finset.Icc 1 N, Real.cos (n * x) =
    Real.sin (((N : ℝ) + 1 / 2) * x) / (2 * Real.sin (x / 2)) - 1 / 2 := by
  sorry





theorem theorem_788577_problem (F : Type*) [Field F]
  (a b : LaurentSeries F)
  (ha : a.order = -2)
  (hb : b.order = -3) :
  ∃! (C : Fin 6 → F),
    (b^2 - C 0 • a^3 - C 1 • (a * b) - C 2 • a^2 - C 3 • b - C 4 • a - C 5 • 1).order > 0 := by
  sorry





theorem theorem_789199_problem 
  (r : ℕ → ℝ) 
  (S : ℕ → ℝ)
  (hS : ∀ (n k : ℕ), k < n + 1 → S (n * (n + 1) / 2 + k) = r k) :
  ∀ (idxs : List ℕ), idxs.Sorted (·<·) → 
    ∃ (jdxs : List ℕ), jdxs.Sorted (·<·) ∧ jdxs.map S = idxs.map r := by
  sorry

theorem theorem_789446_problem (n q : ℕ) (hn : n ≥ q)
  (V W : Type*) [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  (f : V →ₗ[ℝ] W)
  (h_dim_V : FiniteDimensional.finrank ℝ V = n^2)
  (h_dim_W : FiniteDimensional.finrank ℝ W = (n - q)^2)
  (h_rank : FiniteDimensional.finrank ℝ (LinearMap.range f) = (n - q)^2) :
  FiniteDimensional.finrank ℝ (LinearMap.ker f) = q * (2 * n - q) := by
  sorry

theorem theorem_789048_problem (A : AddSubgroup (Fin 3 → ℤ))
  (hA : Nonempty (A ≃+ (Fin 2 → ℤ))) :
  ∃ a b : ℕ, a > 0 ∧ b > 0 ∧
    Nonempty (((Fin 3 → ℤ) ⧸ A) ≃+ (ℤ × ZMod a × ZMod b)) := by
  sorry



theorem theorem_789823_problem (F₁ F₂ F₃ : ℝ) :
  (∃ A B : ℝ, F₁ / Real.cos A = F₂ / Real.cos B ∧ F₂ / Real.cos B = F₃ / Real.sin (A + B)) →
  ¬ ∃! (p : ℝ × ℝ), 
    F₁ / Real.cos p.1 = F₂ / Real.cos p.2 ∧ 
    F₂ / Real.cos p.2 = F₃ / Real.sin (p.1 + p.2) := by
  sorry

theorem theorem_790129_problem (G : Type*) (X : Type*) [Group G] [MulAction G X]
  (x y : X) (a : G) (h : y = a • x) :
  MulAction.stabilizer G y = (MulAction.stabilizer G x).map (MulAut.conj a) := by
  sorry

theorem theorem_789353_problem (a b : ℝ) (h_ab : a < b)
  (δ : ℝ → ℝ) (hδ : ∀ x ∈ Set.Icc a b, 0 < δ x) :
  ∃ n : ℕ, ∃ x : ℕ → ℝ,
    x 0 = a ∧
    x n = b ∧
    (∀ i, i < n → x i < x (i + 1)) ∧
    (∀ i, i < n → ∃ t ∈ Set.Icc (x i) (x (i + 1)),
      Set.Icc (x i) (x (i + 1)) ⊆ Set.Ioo (t - δ t) (t + δ t)) := by
  sorry





theorem theorem_789949_problem (b h c : ℝ) (n : ℤ)
  (hb : b ≠ 0)
  (h_eq : h = (2 * (n : ℝ) * Real.pi + Real.arctan (c / b)) / b)
  (h_range : -Real.pi / 2 < b * h - 2 * (n : ℝ) * Real.pi ∧ 
             b * h - 2 * (n : ℝ) * Real.pi < Real.pi / 2) :
  c = b * Real.tan (b * h - 2 * (n : ℝ) * Real.pi) := by
  sorry





theorem theorem_790430_problem
  (W : ℝ → ℝ)
  (hW : ∀ x : ℝ, W x * Real.exp (W x) = x)
  (a : ℝ)
  (ha : 0 < a) :
  ∀ y : ℝ, y * Real.exp y = a ↔ y = W a := by
  sorry

theorem theorem_789838_problem
  {n : ℕ} {R : Type*} [Field R] [DecidableEq R]
  (A C : Matrix (Fin n) (Fin n) R)
  (hA : IsUnit A.det)
  (hC_diag : ∀ i j, i ≠ j → C i j = 0)
  (hC_nz : ∀ i, C i i ≠ 0) :
  (A * C)⁻¹ = C⁻¹ * A⁻¹ := by
  sorry



theorem theorem_790343_problem (n : ℕ) (h : n ≥ 2) :
  ∫ x in (0 : ℝ)..Real.pi, (Real.sin x) ^ n =
  ((n : ℝ) - 1) / (n : ℝ) * ∫ x in (0 : ℝ)..Real.pi, (Real.sin x) ^ (n - 2) := by
  sorry













theorem theorem_790497_problem
  (y : ℝ → ℝ → ℝ)
  (f : ℝ → ℝ)
  (x₁ x₂ α : ℝ)
  (h_ord : x₁ < x₂)
  (hy : ContDiff ℝ 2 (Function.uncurry y))
  (hf : ContDiff ℝ 1 f) :
  ∫ x in x₁..x₂, deriv f (deriv (fun u ↦ y u α) x) * deriv (fun a ↦ deriv (fun u ↦ y u a) x) α =
  ∫ x in x₁..x₂, deriv f (deriv (fun u ↦ y u α) x) * deriv (fun u ↦ deriv (fun a ↦ y u a) α) x := by
  sorry

theorem theorem_790333_problem
  (F : ℝ × ℝ → ℝ × ℝ)
  (D : Set (ℝ × ℝ))
  (hD_open : IsOpen D)
  (hD_conn : IsConnected D)
  (hD_sc : SimplyConnectedSpace D)
  (hF_cont : Continuous F)
  (h_no_crit : ∀ x ∈ D, F x ≠ 0)
  (h_traj : ∀ x₀ ∈ D, ∃ γ : ℝ → ℝ × ℝ,
    γ 0 = x₀ ∧
    (∀ t, HasDerivAt γ (F (γ t)) t) ∧
    (∀ t ≥ 0, γ t ∈ D)) :
  ∃ γ : ℝ → ℝ × ℝ,
    (∀ t, HasDerivAt γ (F (γ t)) t) ∧
    (∀ t, γ t ∈ D) ∧
    (∃ T > 0, ∀ t, γ (t + T) = γ t) ∧
    (∃ t, γ t ≠ γ 0) := by
  sorry

theorem theorem_790584_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (u : ℕ → X) (y : X)
  (h_conv : Filter.Tendsto u Filter.atTop (nhds y)) :
  ∃ M > 0, ∀ n, ‖u n‖ ≤ M := by
  sorry





theorem theorem_790003_problem (f : {x : ℝ // Irrational x} → ℝ)
  (h_def : ∀ (x : {x : ℝ // Irrational x}) (n : ℕ),
    (n : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) < (n : ℝ) + 1 → f x = (n : ℝ)) :
  Continuous f := by
  sorry

theorem theorem_791123_problem {A B : Type*} [Group A] [Group B]
  (N : Subgroup A) (M : Subgroup B)
  (hN : N.Normal) (hM : M.Normal) :
  (Subgroup.prod N M).Normal := by
  sorry











theorem theorem_790142_problem (X : Type*) [TopologicalSpace X]
  (G : ℕ → Set X)
  (h_open : ∀ n, IsOpen (G n))
  (h_dense : ∀ n, Dense (G n)) :
  Dense (⋂ n, G n) := by
  sorry









theorem theorem_790796_problem (A_xx A_yy A_xy C : ℝ) (Φ : ℝ)
  (h_denom : A_xx ≠ A_yy)
  (h_principal :
    let M : Matrix (Fin 2) (Fin 2) ℝ := !![A_xx, A_xy; A_xy, A_yy]
    let R : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos Φ, -Real.sin Φ; Real.sin Φ, Real.cos Φ]
    (R.transpose * M * R) 0 1 = 0) :
  Real.tan (2 * Φ) = (2 * A_xy) / (A_xx - A_yy) := by
  sorry





theorem theorem_790944_problem
  -- Definitions of the geometric objects and vector field
  (S : Set (EuclideanSpace ℝ (Fin 3)))
  (C : Set (EuclideanSpace ℝ (Fin 3)))
  (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
  -- Abstracted operators for Curl, Line Integral, and Surface Integral
  (curl : (EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)))
  (line_integral : Set (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) → ℝ)
  (surface_integral : Set (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) → ℝ)
  -- Predicates for geometric properties
  (is_smooth_oriented_surface : Set (EuclideanSpace ℝ (Fin 3)) → Prop)
  (is_boundary : Set (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)) → Prop)
  (consistent_orientation : Set (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)) → Prop)
  -- Conditions provided in the problem
  (hS : is_smooth_oriented_surface S)
  (hC : is_boundary S C)
  (hF : ContDiff ℝ 1 F) -- F is continuously differentiable
  (h_orient : consistent_orientation S C) :
  -- The conclusion: Stokes' Theorem
  line_integral C F = surface_integral S (curl F) := by
  sorry

theorem theorem_790872_problem
  (n m : ℕ)
  (f : (Fin n → ℝ) → (Fin m → ℝ))
  (x : Fin n → ℝ)
  (hf : DifferentiableAt ℝ f x) :
  let J := LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m)) (fderiv ℝ f x).toLinearMap
  ∀ i : Fin m, ∀ j : Fin n,
    J i j = deriv (fun t : ℝ => f (x + t • Pi.basisFun ℝ (Fin n) j) i) 0 := by
  sorry





theorem theorem_790506_problem 
  (p f1 f2 f21 f22 : ℝ)
  (gx gy g21 : ℝ)
  (h_f2_nonzero : f2 ≠ 0)
  (h_gx : f1 + f2 * gx = 0)
  (h_gy : f2 * gy = 1)
  (h_g21 : g21 = - (1 / f2 ^ 2) * (f21 + f22 * gx)) :
  p * f2 * g21 = p * f2 * (f1 * f22 - f21 * f2) / f2 ^ 3 := by
  sorry

theorem theorem_791681_problem (n : ℕ) (h : n > 0) :
  (Finset.filter (fun x : ℕ × ℕ => x.1 + x.2 = n ∧ x.1 ≥ x.2 ∧ x.2 ≥ 1)
    (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))).card = n / 2 := by
  sorry











theorem theorem_791358_problem (m : ℕ)
  (f : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1)))
  (hf : ContDiff ℝ ⊤ f)
  (x : EuclideanSpace ℝ (Fin (m + 1)))
  (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
  f x ∈ tangentConeAt ℝ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) x ↔
  inner (f x) x = (0 : ℝ) := by
  sorry



theorem theorem_791461_problem (f : ℝ × ℝ → ℝ) (x y dx dy : ℝ)
  (hf : ContDiff ℝ 2 f) :
  iteratedFDeriv ℝ 2 f (x, y) ![(dx, dy), (dx, dy)] =
  (iteratedFDeriv ℝ 2 f (x, y) ![(1, 0), (1, 0)]) * dx ^ 2 +
  2 * (iteratedFDeriv ℝ 2 f (x, y) ![(1, 0), (0, 1)]) * dx * dy +
  (iteratedFDeriv ℝ 2 f (x, y) ![(0, 1), (0, 1)]) * dy ^ 2 := by
  sorry





theorem theorem_791956_problem (F : ℝ → ℝ)
  (hF : ∀ s > 0, F s = ∫ x in Set.Ioi 0, (Real.sin x / x) * Real.exp (-s * x)) :
  Filter.Tendsto F Filter.atTop (nhds 0) := by
  sorry





theorem theorem_791441_problem (a b x : ℝ) (Y : ℝ → ℝ)
  (ha : 0 < a) (hb : 0 < b)
  (h_pos : ∀ n, 0 < Y n)
  (h_diff : Differentiable ℝ Y)
  (h_eq : ∀ n, Y n = (a + b * (Y n) ^ x) ^ n)
  (n : ℝ) :
  deriv Y n = (Y n * (a + b * (Y n) ^ x) * Real.log (a + b * (Y n) ^ x)) / 
    (a + (b - b * n * x) * (Y n) ^ x) := by
  sorry

theorem theorem_792348_problem (α : Type*) (V : Set (Set α)) (hV : V.Finite)
  (W : Set (Set α))
  (hW : W = {s | ∃ t : Finset (Set α), s = ⋃₀ (t : Set (Set α)) ∧ 
    ∀ x ∈ t, ∃ u : Finset (Set α), x = ⋂₀ (u : Set (Set α)) ∧ 
      ∀ y ∈ u, y ∈ V ∨ yᶜ ∈ V }) :
  W.Finite := by
  sorry

theorem theorem_792240_problem (r : ℝ) (P : ℕ → ℝ)
  (h1 : P 1 = r)
  (h2 : ∀ n, P (n + 1) = P n * P 1) :
  ∀ n, n ≥ 1 → P n = r ^ n := by
  sorry



theorem theorem_792248_problem {R : Type*} [CommRing R] (I : Ideal R) (h : I.IsMaximal) :
  IsField (R ⧸ I) := by
  sorry

theorem theorem_792518_problem (n : ℕ) :
  ∑ x in (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1))).filter 
    (fun x => 1 ≤ x.1 ∧ x.1 < x.2 + x.1 ∧ x.2 + x.1 ≤ n), (1 : ℝ) / x.2 = 
  ∑ k in Finset.Ico 1 n, ∑ j in Finset.Ico 1 (n - k + 1), (1 : ℝ) / k := by
  sorry

theorem theorem_792103_problem
  (f : ℝ → ℝ → ℝ)
  (a b : ℝ)
  (hf : ContDiff ℝ 1 (Function.uncurry f))
  (y : ℝ) :
  deriv (fun u => ∫ x in a..b, f x u) y = ∫ x in a..b, deriv (fun v => f x v) y := by
  sorry

theorem theorem_792064_problem 
  (f : ℝ → ℝ) 
  (r M₁ : ℝ) 
  (hr : 0 < r ∧ r < 1) 
  (hM : M₁^2 > 16 * ((1 - r) / (1 + r))) : 
  ¬ ∃ Ω, Ω > 0 ∧ f Ω = 0 := by
  sorry



theorem theorem_792149_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (T_n : ℕ → E →L[ℝ] E) (T : E →L[ℝ] E)
  (h_pt : ∀ x, Filter.Tendsto (fun n ↦ T_n n x) Filter.atTop (nhds (T x)))
  (h_bound : ∃ M > 0, ∀ n, ‖T_n n‖ ≤ M)
  (K : Set E) (hK : IsCompact K)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ N, ∀ n > N, ∀ x ∈ K, ‖T_n n x - T x‖ < ε := by
  sorry

theorem theorem_792244_problem (x y : ℤ)
  (h : ∀ p : ℕ, Nat.Prime p → x.emod p ≤ y.emod p) :
  x = y := by
  sorry

theorem theorem_793186_problem (n : ℕ) (F : Finset (Finset (Fin n)))
  (h : ∀ A ∈ F, ∀ B ∈ F, A ⊆ B → A = B) :
  ∑ A in F, (1 : ℝ) / (Nat.choose n A.card) ≤ 1 := by
  sorry

theorem theorem_791979_problem
  (D : Set (ℝ × ℝ))
  (f : ℝ × ℝ → ℝ)
  (hf : ConvexOn ℝ D f)
  (g : ℝ → ℝ)
  (hg : ∀ y, g y = sSup {z | ∃ x, (x, y) ∈ D ∧ z = f (x, y)})
  (h_well_defined : ∀ y, (∃ x, (x, y) ∈ D) → BddAbove {z | ∃ x, (x, y) ∈ D ∧ z = f (x, y)}) :
  ConvexOn ℝ {y | ∃ x, (x, y) ∈ D} g := by
  sorry

theorem theorem_792335_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (E t : ℝ)
  (p x : V)
  -- Condition: g_Mink denotes the Minkowski metric with components diag(-1, 1, 1, 1).
  -- We define the inner product induced by this metric on the product space ℝ × V (spacetime).
  (minkowski_dot : ℝ × V → ℝ × V → ℝ)
  (h_metric : ∀ (u v : ℝ × V), minkowski_dot u v = - (u.1 * v.1) + inner u.2 v.2) :
  -- Question: Prove that the exponent sign (Et - p⋅x) is consistent with the metric 
  -- (corresponds to the negative of the Minkowski inner product).
  E * t - inner p x = - minkowski_dot (E, p) (t, x) := by
  sorry





theorem theorem_792801_problem 
  {α : Type*} 
  (rel : α → α → Prop) 
  (IsNormalForm : α → Prop)
  (h_confluence : ∀ x y z, rel x y → rel x z → ∃ w, rel y w ∧ rel z w)
  (h_nf_def : ∀ n, IsNormalForm n ↔ ∀ q, rel n q → n = q)
  (M N₁ N₂ : α)
  (h_red1 : rel M N₁)
  (h_red2 : rel M N₂)
  (h_nf1 : IsNormalForm N₁)
  (h_nf2 : IsNormalForm N₂) :
  N₁ = N₂ := by
  sorry



theorem theorem_792895_problem
  (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  (N₁ N₂ : Module.End K V)
  (h₁ : ∃ r₁ : ℕ, r₁ > 0 ∧ N₁ ^ r₁ = 0)
  (h₂ : ∃ r₂ : ℕ, r₂ > 0 ∧ N₂ ^ r₂ = 0)
  (h_comm : N₁ * N₂ = N₂ * N₁) :
  ∃ r : ℕ, r > 0 ∧ (N₁ + N₂) ^ r = 0 := by
  sorry

