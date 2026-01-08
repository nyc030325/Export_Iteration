import Mathlib
import Mathlib.Tactic

theorem theorem_906515_problem {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
  (A B : Matrix n n K) :
  A * B = B * A ↔ Commute A B := by
  sorry









theorem theorem_906461_problem (h a b sl s : ℝ) (h_pos : 0 < h) :
  (∀ x ∈ Set.Icc sl s, (a * h + b^2) / h - h * (x - b / h)^2 ≥ 0) →
  ∀ x ∈ Set.Icc sl s,
  ∀ y : ℝ,
  (h * (x - b / h)^2 + y^2 = (a * h + b^2) / h ∧ 0 ≤ y) ↔
  y = Real.sqrt ((a * h + b^2) / h - h * (x - b / h)^2) := by
  sorry

theorem theorem_906521_problem (n : ℕ) (r : ℝ) (V S : ℝ → ℝ)
  (hV : ∀ x, V x = V 1 * x ^ n)
  (hS : HasDerivAt V (S r) r) :
  S r = (n : ℝ) * r ^ (n - 1) * V 1 := by
  sorry







theorem theorem_907332_problem (n : ℕ) (a : ℝ) 
  (hn : 0 < n) (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) :
  Real.logb a (n.factorial : ℝ) = ∑ k in Finset.Icc 1 n, Real.logb a (k : ℝ) := by
  sorry

theorem theorem_906857_problem (G S : Type*) [Group G] [MulAction G S]
  (H2 : Subgroup G) (R : Set S)
  (h_res : ∀ g ∈ H2, ∀ x ∈ R, g • x ∈ R) :
  {g : G | ∀ r ∈ R, g • r = r} = {g : G | g ∈ H2 ∧ ∀ r ∈ R, g • r = r} := by
  sorry





theorem theorem_906939_problem (K : Type*) [Field K] (A B : K) :
  (∀ X Y Z : K, (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) →
    ¬ (Y^2 * Z = X^3 + A * X * Z^2 + B * Z^3 ∧
       -3 * X^2 - A * Z^2 = 0 ∧
       2 * Y * Z = 0 ∧
       Y^2 - 2 * A * X * Z - 3 * B * Z^2 = 0)) ↔
  4 * A^3 - 27 * B^2 ≠ 0 := by
  sorry









theorem theorem_907181_problem :
  HasSum (fun k : ℕ => (-1 : ℝ) ^ k * (1 / ((k + 1 : ℝ) * Real.log 2))) 1 := by
  sorry







theorem theorem_907982_problem {V : Type*} (G H : SimpleGraph V) :
  (G ⊔ H).chromaticNumber ≤ G.chromaticNumber * H.chromaticNumber := by
  sorry





theorem theorem_907395_problem
  (T : ℝ)
  (f : ℝ → ℝ)
  (F : ℝ → ℝ)
  (hT : T > 0)
  (hf : DifferentiableOn ℝ f (Set.Icc 0 T))
  (hF : ∀ x ∈ Set.Icc 0 T, F x = sSup (f '' Set.Icc 0 x))
  (t : ℝ)
  (ht : t ∈ Set.Ioo 0 T)
  (hF_diff : DifferentiableAt ℝ F t)
  (hF_pos : deriv F t > 0) :
  deriv F t = deriv f t := by
  sorry





theorem theorem_907730_problem :
  -- Let H be the Upper Half Plane (standard model for Hyperbolic plane)
  let H := UpperHalfPlane
  -- Let E3 be the standard Euclidean 3-space
  let E3 := EuclideanSpace ℝ (Fin 3)
  -- The claim: There does not exist a function f from H to E3 such that...
  ¬ ∃ f : H → E3,
    -- f is smooth (C^∞). 
    -- We treat H as a real manifold (charts to ℂ ~ ℝ²).
    -- We treat E3 as a real manifold.
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ E3) ⊤ f ∧
    -- f is an isometry (preserves the metric: d_H(x, y) = d_E(f x, f y)).
    -- Note: The MetricSpace instance on UpperHalfPlane is the hyperbolic Poincaré metric.
    Isometry f := by
  sorry

theorem theorem_908400_problem
  (IsTrue : List ℕ → Prop)
  (S : Set (List ℕ))
  (hS_true : ∀ s ∈ S, IsTrue s)
  (hS_finite : S.Finite) :
  ∃ f : ℕ → Option (List ℕ), Computable f ∧ (∀ s, s ∈ S ↔ ∃ n, f n = some s) := by
  sorry

theorem theorem_907870_problem
  {K : Type*} [Field K] {n : ℕ}
  (A : Matrix (Fin n) (Fin n) K)
  (hA : ∀ i j : Fin n, j < i → A i j = 0) :
  ∀ k : ℕ, k ≤ n →
  let V_k := Submodule.span K (Set.image (Pi.basisFun K (Fin n)) {i : Fin n | ↑i < k})
  Submodule.map (Matrix.toLin' A) V_k ≤ V_k := by
  sorry



theorem theorem_908175_problem (a : ℕ → ℝ)
  (h1 : a 1 = 1)
  (h_rec : ∀ m : ℕ, 2 ≤ m → a m = m + (m + 1) * a (m - 1)) :
  ∀ m : ℕ, 1 ≤ m → a m = Real.Gamma (m + 2) - 1 := by
  sorry









theorem theorem_908656_problem
  {S : Type*} [TopologicalSpace S]
  {W : Type*}
  (T₀ : Set S)
  (Tw : W → Set S)
  (h₀ : IsConnected T₀)
  (hw : ∀ w, IsConnected (Tw w))
  (h_inter : ∀ w, (T₀ ∩ Tw w).Nonempty) :
  IsConnected (T₀ ∪ ⋃ w, Tw w) := by
  sorry











theorem theorem_908643_problem
  (k : Type*) [Field k] [IsAlgClosed k]
  (n : ℕ)
  (a : Fin n → k)
  (I : Ideal (MvPolynomial (Fin n) k))
  (h1 : I.IsMaximal)
  (h2 : I = Ideal.span (Set.range (fun i => MvPolynomial.X i - MvPolynomial.C (a i)))) :
  ∀ f : MvPolynomial (Fin n) k,
    Ideal.Quotient.mk I f = Ideal.Quotient.mk I (MvPolynomial.C (MvPolynomial.eval a f)) := by
  sorry









theorem theorem_909239_problem (Ω : Set ℂ) (f : ℂ → ℂ) (K : Set ℂ) (g : ℂ → ℂ)
  (h_domain : IsOpen Ω)
  (h_holo : DifferentiableOn ℂ f Ω)
  (h_nz : ∀ z ∈ Ω, f z ≠ 0)
  (h_K_sub : K ⊆ Ω)
  (h_K_cpt : IsCompact K)
  (h_K_ne : K.Nonempty)
  (h_g : ∀ z, g z = (f z)⁻¹) :
  sSup ((λ z ↦ Complex.abs (f z)) '' K) = (sInf ((λ z ↦ Complex.abs (g z)) '' K))⁻¹ := by
  sorry

theorem theorem_909491_problem
  (N T : ℕ)
  (hN : N > 0)
  (Obs : Type)
  (x : Fin T → Obs)
  -- P_joint represents P(x_1...x_T, Z_T = j | θ)
  (P_joint : (Fin T → Obs) → Fin N → ℝ)
  -- P_obs represents P(x_1...x_T | θ)
  (P_obs : (Fin T → Obs) → ℝ)
  -- Definition of forward probability alpha at time T
  (alpha_T : Fin N → ℝ)
  (h_alpha : ∀ j : Fin N, alpha_T j = P_joint x j)
  -- The Law of Total Probability inherent to the HMM structure
  (h_total_prob : P_obs x = ∑ j : Fin N, P_joint x j) :
  Real.log (P_obs x) = Real.log (∑ j : Fin N, alpha_T j) := by
  sorry

theorem theorem_908580_problem
  (a b c d e f : ℝ)
  (x₁ y₁ : ℝ)
  (h_on_curve : a * x₁^2 + b * x₁ * y₁ + c * y₁^2 + d * x₁ + e * y₁ + f = 0) :
  ∀ x y : ℝ,
    a * (x * x₁) + b * ((x * y₁ + x₁ * y) / 2) + c * (y * y₁) +
    d * ((x + x₁) / 2) + e * ((y + y₁) / 2) + f = 0 ↔
    (2 * a * x₁ + b * y₁ + d) * (x - x₁) + (b * x₁ + 2 * c * y₁ + e) * (y - y₁) = 0 := by
  sorry







theorem theorem_909298_problem
  (n : ℕ)
  (a b : Fin n → ℝ)
  (f : (Fin n → ℝ) → (Fin n → ℝ))
  (h_box : ∀ i, a i ≤ b i)
  (h_cont : ContinuousOn f (Set.pi Set.univ (fun i ↦ Set.Icc (a i) (b i))))
  (h_sign_lower : ∀ i, ∀ x ∈ Set.pi Set.univ (fun j ↦ Set.Icc (a j) (b j)),
    x i = a i → f x i ≤ 0)
  (h_sign_upper : ∀ i, ∀ x ∈ Set.pi Set.univ (fun j ↦ Set.Icc (a j) (b j)),
    x i = b i → f x i ≥ 0) :
  ∃ x ∈ Set.pi Set.univ (fun i ↦ Set.Icc (a i) (b i)), f x = 0 := by
  sorry





theorem theorem_909964_problem (A : ZFSet) (F : ZFSet → ZFSet)
  (h_unique : ∀ x ∈ A, ∃! y, F x = y) :
  ∃ C : ZFSet, ∀ y, y ∈ C ↔ ∃ x ∈ A, F x = y := by
  sorry



theorem theorem_909805_problem
  (a : ℝ) (f : ℝ → ℝ) (s : Set ℝ)
  (h_conn : IsConnected s)
  (hs : IsOpen s)
  (ha : a ≠ 0)
  (hf : DifferentiableOn ℝ f s)
  (hf2 : DifferentiableOn ℝ (deriv f) s)
  (hf_ne : ∀ x ∈ s, deriv f x ≠ 0)
  (h_ode : ∀ x ∈ s, deriv (deriv f) x / (deriv f x) ^ 2 = a) :
  ∃ C K : ℝ, ∀ x ∈ s, f x = - (1 / a) * Real.log (abs (C - a * x)) + K := by
  sorry

theorem theorem_910213_problem
  {P Q : Type*} [AddGroup Q]
  (ψ : P → Q)
  (h : Set.range ψ = (AddMonoidHom.ker (0 : Q →+ Q) : Set Q)) :
  Function.Surjective ψ := by
  sorry









theorem theorem_909740_problem (m₁ m₂ g h : ℝ)
  (v₁ v₂ y : ℝ → ℝ)
  (h_init_pos : y 0 = h)
  (h_init_v1 : v₁ 0 = 0)
  (h_init_v2 : v₂ 0 = 0)
  (h_conserved : ∀ t, m₁ * g * y t + (1/2 : ℝ) * m₁ * (v₁ t)^2 + (1/2 : ℝ) * m₂ * (v₂ t)^2 =
                      m₁ * g * y 0 + (1/2 : ℝ) * m₁ * (v₁ 0)^2 + (1/2 : ℝ) * m₂ * (v₂ 0)^2) :
  ∀ t, m₁ * g * y t + (1/2 : ℝ) * m₁ * (v₁ t)^2 + (1/2 : ℝ) * m₂ * (v₂ t)^2 = m₁ * g * h := by
  sorry

theorem theorem_910304_problem (k : Type*) [Field k] (G : Type*) [Group G] [Fintype G] :
  IsSemisimpleRing (MonoidAlgebra k G) ↔ ¬ (ringChar k ∣ Fintype.card G) := by
  sorry









theorem theorem_910443_problem :
  let obj := fun (x₁ x₂ x₃ : ℝ) ↦ 2 * x₁ + 3 * x₂ - x₃
  let feasible := fun (x₁ x₂ x₃ : ℝ) ↦
    -x₁ + 2 * x₂ - x₃ ≤ -2 ∧
    -2 * x₁ - x₂ + 2 * x₃ ≤ -3 ∧
    x₁ ≥ 0 ∧ x₂ ≥ 0 ∧ x₃ ≥ 0
  ∃ x₁ x₂ x₃ : ℝ, feasible x₁ x₂ x₃ ∧
    ∀ y₁ y₂ y₃ : ℝ, feasible y₁ y₂ y₃ → obj x₁ x₂ x₃ ≤ obj y₁ y₂ y₃ := by
  sorry

theorem theorem_910483_problem (p : ℕ) (hp : Nat.Prime p) :
  ∀ x : ℚ, (∃ (a : ℤ) (k : ℕ), x = a / ((p : ℚ) ^ k)) →
  ∀ n : ℕ, n > 0 →
  ∃ y : ℚ, (∃ (b : ℤ) (l : ℕ), y = b / ((p : ℚ) ^ l)) ∧
  ∃ (z : ℤ), (n : ℚ) * y - x = z := by
  sorry



theorem theorem_911013_problem (n : ℕ) (A B A' : Matrix (Fin n) (Fin n) ℝ)
  (hB : Invertible B)
  (hA' : A' = B * A * B⁻¹) :
  A'.det = A.det := by
  sorry







theorem theorem_910986_problem
  {X : Type*} [TopologicalSpace X]
  {x y z : X}
  (f₁ f₂ : Path x y)
  (g₁ g₂ : Path y z)
  (F : Path.Homotopy f₁ f₂)
  (G : Path.Homotopy g₁ g₂) :
  Path.Homotopic (f₁.trans g₁) (f₂.trans g₂) := by
  sorry





theorem theorem_911292_problem
  (m n : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix m n ℝ)
  (v : m → ℝ)
  (hv : ∀ i, v i ≠ 0) :
  ∃! A_bar : Matrix m n ℝ, ∀ i j, A_bar i j = (v i)⁻¹ * A i j := by
  sorry

theorem theorem_911427_problem
  (T : ℝ)
  (hT : T > 0)
  (f : ℝ → ℝ)
  (u₁ u₂ : ℝ → ℝ → ℝ)
  -- Conditions for u₁ (PDE, IC, BC)
  (h1_pde : ∀ x t, x ∈ Set.Ioo 0 1 → t ∈ Set.Ioo 0 T →
    deriv (u₁ x) t - deriv (fun x' => deriv (fun y => u₁ y t) x') x = 0)
  (h1_ic : ∀ x, x ∈ Set.Icc 0 1 → u₁ x 0 = f x)
  (h1_bc : ∀ t, t ∈ Set.Icc 0 T → u₁ 0 t = 0 ∧ u₁ 1 t = 0)
  -- Conditions for u₂ (PDE, IC, BC)
  (h2_pde : ∀ x t, x ∈ Set.Ioo 0 1 → t ∈ Set.Ioo 0 T →
    deriv (u₂ x) t - deriv (fun x' => deriv (fun y => u₂ y t) x') x = 0)
  (h2_ic : ∀ x, x ∈ Set.Icc 0 1 → u₂ x 0 = f x)
  (h2_bc : ∀ t, t ∈ Set.Icc 0 T → u₂ 0 t = 0 ∧ u₂ 1 t = 0) :
  -- Conclusion: Uniqueness
  ∀ x t, x ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 T → u₁ x t = u₂ x t := by
  sorry



theorem theorem_910620_problem (X : Matrix (Fin 2) (Fin 3) ℝ) :
  (X * !![(0 : ℝ), 1; 1, -3; 0, 0] = 1) ↔ 
  (∃ s t : ℝ, X = !![3, 1, s; 1, 0, t]) := by
  sorry

theorem theorem_911449_problem (T : ℕ → ℚ)
  (h1 : T 1 = -(1 : ℚ) / 2)
  (h2 : ∀ n : ℕ, n ≥ 2 → T n = T ((n + 1) / 2) + T (n / 2) + 2) :
  ∀ n : ℕ, n ≥ 1 → T n = (3 * n : ℚ) / 2 - 2 := by
  sorry

theorem theorem_910998_problem (a b c d : ℝ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
  |a / b^2 - (c / b^2 + d / b^3)| = |(b * (a - c) - d) / b^3| := by
  sorry







theorem theorem_911749_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
  (n : ℕ)
  [Fintype (ConnectedComponents M)]
  (h_n : Fintype.card (ConnectedComponents M) = n)
  (Or_M : Type*) [Fintype Or_M]
  (Or_comp : ConnectedComponents M → Type*) [∀ c, Fintype (Or_comp c)]
  (h_local : ∀ c, Fintype.card (Or_comp c) = 2)
  (h_struct : Nonempty (Or_M ≃ Π c, Or_comp c)) :
  Fintype.card Or_M = 2 ^ n := by
  sorry



theorem theorem_912010_problem {X : Type*} [TopologicalSpace X]
  (h_tau : ∀ U : Set X, IsOpen U ↔ U = ∅ ∨ U = Set.univ)
  (V : Set X) :
  IsPreconnected V := by
  sorry

theorem theorem_911458_problem
  (G : Type*) [Group G]
  (A : Type*)
  [MulAction G A] :
  {g : G | ∀ a : A, g • a = a} = {g : G | MulAction.toPermHom G A g = 1} := by
  sorry

theorem theorem_911591_problem
  (n q : ℕ)
  (hn : n > 0)
  (hq : IsPrimePow q)
  (K : Type*) [Field K] [Fintype K]
  (hK : Fintype.card K = q ^ (2 * n)) :
  let T : K → K := fun a => ∑ i in Finset.range (2 * n), a ^ (q ^ i)
  {x : K | T x = 0} = {y : K | ∃ a : K, y = a - a ^ q} := by
  sorry





theorem theorem_911900_problem (P : ℕ → Prop) 
  (h_base : P 0) 
  (h_step : ∀ k, P k → P (k + 1)) : 
  ∀ n, P n := by
  sorry

theorem theorem_911817_problem (a b c d e f : ℝ) (h_det : a * e - b * d ≠ 0) :
  ∃ h k : ℝ, a * h + b * k + c = 0 ∧ d * h + e * k + f = 0 := by
  sorry

