import Mathlib
import Mathlib.Tactic

theorem theorem_1047064_problem :
  let f : ℝ → ℝ := fun z ↦ z^2 - 2
  let K := {z : ℝ | ∃ M, ∀ n, |f^[n] z| ≤ M}
  K = Set.Icc (-2) 2 := by
  sorry























theorem theorem_1048764_problem (f : ℝ → ℝ)
  (h_cont : ContinuousOn f (Set.Icc 0 1))
  (h_int1 : ∫ x in (0 : ℝ)..1, f x = 0)
  (h_int2 : ∫ x in (0 : ℝ)..1, x * f x = 0)
  (h_nonzero : ¬ ∀ x ∈ Set.Icc 0 1, f x = 0) :
  ∃ x₁ ∈ Set.Ioo (0 : ℝ) 1, ∃ x₂ ∈ Set.Ioo (0 : ℝ) 1, x₁ ≠ x₂ ∧ f x₁ = 0 ∧ f x₂ = 0 := by
  sorry

theorem theorem_1048494_problem
  (α : Type*) [Membership α α]
  (x y z : α)
  (S : Set α)
  (hS : S = {x, y, z})
  (hx : x ∈ y)
  (hy : y ∈ z)
  (hz : z ∈ x)
  (h_foundation : ∀ (T : Set α), T.Nonempty → ∃ a ∈ T, ∀ b ∈ T, b ∉ a) :
  False := by
  sorry

theorem theorem_1048528_problem (S : Type*) [Nonempty S] [Countable S] :
  ∃ (m : MeasurableSpace S) (μ : @MeasureTheory.Measure S m),
    @MeasureTheory.IsProbabilityMeasure S m μ ∧ ∀ (s : Set S), @MeasurableSet S m s := by
  sorry

theorem theorem_1048484_problem
  (f g : ℝ → ℝ)
  (I : Set ℝ)
  (hI : IsOpen I)
  (hf : ContDiffOn ℝ 2 f I)
  (hg : ContDiffOn ℝ 2 g I)
  (hg_nz : ∀ x ∈ I, g x ≠ 0)
  (hf_nz : ∀ x ∈ I, f x ≠ 0)
  (h_concave : StrictConcaveOn ℝ I (fun x => f x / g x))
  (h_convex : StrictConvexOn ℝ I (fun x => g x / f x))
  (x_star : ℝ)
  (hx_star : x_star ∈ I)
  (h_opt : IsLocalMax (fun x => f x / g x) x_star) :
  deriv f x_star * g x_star = deriv g x_star * f x_star := by
  sorry

theorem theorem_1048404_problem (m c : ℝ) (f : ℝ → ℝ)
  (h_def : ∀ x, f x = m * x + c)
  (x y : ℝ) (α β : ℝ)
  (h_α : α ∈ Set.Icc 0 1)
  (h_β : β ∈ Set.Icc 0 1)
  (h_sum : α + β = 1) :
  f (α * x + β * y) ≤ α * f x + β * f y := by
  sorry

theorem theorem_1048432_problem
  (IsConsistent : (ℕ → ℤ) → Prop)
  (B : ℕ → ℕ → ℤ)
  (f : ℕ → ℤ)
  (hf : IsConsistent f) :
  ∃! c : ℕ → ℤ, ∀ n : ℕ, HasSum (fun i => c i * B i n) (f n) := by
  sorry

theorem theorem_1048458_problem (l j k : ℕ) :
  ∑ s in Finset.range (l + 1), Nat.choose (s + j) j * Nat.choose (l - s + k) k =
  Nat.choose (l + j + k + 1) l := by
  sorry



theorem theorem_1048685_problem
  {k : Type*} [Field k]
  (F G : MvPolynomial (Fin 2) k)
  (hF_nz : F ≠ 0)
  (hG_nz : G ≠ 0)
  (hF_irred : Irreducible F)
  (h_not_dvd : ¬ F ∣ G)
  (hV_inf : {x : Fin 2 → k | MvPolynomial.eval x F = 0}.Infinite) :
  {x : Fin 2 → k | MvPolynomial.eval x F = 0 ∧ MvPolynomial.eval x G = 0}.Finite := by
  sorry





theorem theorem_1049303_problem (m n : ℕ) (hm : m > 0) (hn : n > 0) :
  (1 / (m : ℝ)) ^ (1 / (n : ℝ)) + (1 / (n : ℝ)) ^ (1 / (m : ℝ)) > 1 := by
  sorry

theorem theorem_1049321_problem (b v x : ℝ)
  (h1 : b > x)
  (h2 : b - x ≠ 0)
  (y : ℝ)
  (hy : y = v / (b - x))
  (h_eq : y^3 + (b^2 / (b - x)) * y^2 - x^3 = 0) :
  v^3 + b^2 * v^2 - b^3 * x^3 + 3 * b^2 * x^4 - 3 * b * x^5 + x^6 = 0 := by
  sorry



theorem theorem_1048865_problem
  (n : ℕ)
  (C : Type*)
  [Fintype C] [DecidableEq C]
  (P : (Fin n → C) → ℝ)
  (h_exch : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → C), P (x ∘ σ) = P x)
  (k : ℕ)
  (I J : Fin k → Fin n)
  (hI : Function.Injective I)
  (hJ : Function.Injective J)
  (u v : Fin k → C) :
  (∑ x in Finset.univ.filter (fun x => x ∘ I = u ∧ x ∘ J = v), P x) =
  (∑ x in Finset.univ.filter (fun x => x ∘ J = u ∧ x ∘ I = v), P x) := by
  sorry

theorem theorem_1049984_problem (x : ℝ) :
  Real.exp x * Real.sin x = ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) / 2) * Real.sin ((n : ℝ) * Real.pi / 4) * x ^ n / n.factorial := by
  sorry





theorem theorem_1049967_problem :
  ¬ ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (C : Set Y),
  Continuous f → IsConnected C → IsConnected (f ⁻¹' C) := by
  sorry



theorem theorem_1050298_problem : Nonempty (Polynomial ℤ ≃ ℕ) := by
  sorry

theorem theorem_1049500_problem (n : ℕ) (P : Fin n → Fin n → ℝ)
  (h_n : n > 0)
  (h_sum : ∀ i j, i ≠ j → P i j + P j i = 1)
  (h_pos : ∀ i j, i ≠ j → P i j > 0) :
  ∀ w : Fin n → ℝ,
    (∀ i, w i > 0) →
    (∀ i j, i ≠ j → P i j = w i / (w i + w j)) →
    ∃ w' : Fin n → ℝ,
      (∀ i, w' i > 0) ∧
      (∀ i j, i ≠ j → P i j = w' i / (w' i + w' j)) ∧
      w' ≠ w := by
  sorry

theorem theorem_1049635_problem (n : ℕ) :
  ∑ k in Finset.range (n + 1), (if k % 4 = 3 then (n.choose k : ℝ) else 0) =
  (1 / 2 : ℝ) * ((2 : ℝ) ^ ((n : ℝ) - 1) - (2 : ℝ) ^ ((n : ℝ) / 2) * Real.sin (n * Real.pi / 4)) := by
  sorry



theorem theorem_1049810_problem (T D_0 g R_f delta_D_0 VTS_0 : ℝ)
  (h_Rf : R_f > g)
  (h_Rf_nonzero : 1 + R_f ≠ 0)
  (h_delta : delta_D_0 = D_0)
  (h_VTS : VTS_0 = T * D_0 + T * ∑' t : ℕ, if t = 0 then 0 else delta_D_0 * ((1 + g) / (1 + R_f)) ^ t) :
  VTS_0 = T * D_0 + T * (g * D_0) / (R_f - g) := by
  sorry

theorem theorem_1050220_problem
  (n : ℕ)
  (v w : Fin n → ℝ)         -- Components v^i, w^j in x coordinates
  (v' w' : Fin n → ℝ)       -- Components v'^k, w'^l in y coordinates
  (g : Fin n → Fin n → ℝ)   -- Metric components g_{ij} in x coordinates
  (g' : Fin n → Fin n → ℝ)  -- Metric components g'_{kl} in y coordinates
  (dx_dy : Fin n → Fin n → ℝ) -- Jacobian matrix components \partial x^i / \partial y^k
  (dy_dx : Fin n → Fin n → ℝ) -- Jacobian matrix components \partial y^k / \partial x^i
  -- Transformation law for vector components: v'^k = (\partial y^k / \partial x^i) v^i
  (hv : ∀ k, v' k = ∑ i, dy_dx k i * v i)
  (hw : ∀ l, w' l = ∑ j, dy_dx l j * w j)
  -- Transformation law for metric tensor: g'_{kl} = (\partial x^i / \partial y^k) (\partial x^j / \partial y^l) g_{ij}
  (hg : ∀ k l, g' k l = ∑ i, ∑ j, dx_dy i k * dx_dy j l * g i j)
  -- Chain rule for coordinate change: (\partial x^i / \partial y^k) (\partial y^k / \partial x^p) = \delta^i_p
  (h_chain : ∀ i p, ∑ k, dx_dy i k * dy_dx k p = if i = p then 1 else 0) :
  (∑ i, ∑ j, g i j * v i * w j) = (∑ k, ∑ l, g' k l * v' k * w' l) := by
  sorry

theorem theorem_1050234_problem (S : Type*) [Nonempty S] (P : S → Prop)
  (h : ∃ x₀ : S, ¬ P x₀) :
  ¬ (∀ x : S, P x) := by
  sorry

theorem theorem_1050524_problem (n : ℕ) (a : ℕ → ℂ) (k z : ℂ) (hz : Complex.abs z > 0) :
  Complex.abs (a 0 * z^2) ≤ Complex.abs (a n * z^n) + ∑ i in Finset.range (n - 1), Complex.abs ((a i - k * a (i + 1) - a (i + 2)) * z^(i + 2)) := by
  sorry



theorem theorem_1049838_problem (G : Type*) [Group G] [Fintype G]
  (hG : Fintype.card G = 420) (S : Sylow 7 G) :
  S.toSubgroup.Normal := by
  sorry

theorem theorem_1050799_problem (a b : ℕ → ℝ)
  (h1 : ∀ n, a n ≤ b n)
  (h2 : ∀ n, Set.Icc (a (n + 1)) (b (n + 1)) ⊆ Set.Icc (a n) (b n))
  (h3 : Filter.Tendsto (fun n ↦ b n - a n) Filter.atTop (nhds 0)) :
  ∃! x, x ∈ ⋂ n, Set.Icc (a n) (b n) := by
  sorry



theorem theorem_1050692_problem (K : ℝ → ℕ) :
  ∃ C : ℕ, C > 0 ∧ K (Real.sqrt 2) ≤ C := by
  sorry



theorem theorem_1050542_problem
  {X : Type*} [TopologicalSpace X]
  (K : Set X)
  (C : Set (Set X))
  (hK : IsCompact K)
  (h_open : ∀ U ∈ C, IsOpen U)
  (h_cover : K ⊆ ⋃₀ C) :
  ∃ C' ⊆ C, C'.Finite ∧ K ⊆ ⋃₀ C' := by
  sorry



theorem theorem_1050910_problem
  {n : ℕ}
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (b : Basis (Fin n) ℝ V)
  (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (df : V →ₗ[ℝ] ℝ)
  (grad_f : V)
  (G : Matrix (Fin n) (Fin n) ℝ)
  (G_inv : Matrix (Fin n) (Fin n) ℝ)
  (h_g_symm : ∀ u v, g u v = g v u)
  (h_grad_def : ∀ X, g grad_f X = df X)
  (h_G_def : ∀ i j, G i j = g (b i) (b j))
  (h_G_inv : G_inv * G = 1) :
  grad_f = ∑ i : Fin n, ∑ j : Fin n, (G_inv i j * df (b i)) • (b j) := by
  sorry

theorem theorem_1051025_problem (f : ℚ →+* ℚ) : ∀ x : ℚ, f x = x := by
  sorry



theorem theorem_1051048_problem (x : ℝ) (p : ℕ) (a b c d : ℚ)
  (hp : p.Prime)
  (hx : x^4 = p)
  (h_root : (a : ℝ) * x^3 + (b : ℝ) * x^2 + (c : ℝ) * x + (d : ℝ) = 0) :
  a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  sorry



theorem theorem_1050802_problem {I α : Type*} (X : I → Set α)
  (h : ∀ i, (X i).Nonempty) :
  ∃ f : I → α, ∀ i, f i ∈ X i := by
  sorry

theorem theorem_1051230_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (v : ℝ → E) (v₀ : ℝ)
  (h_diff : Differentiable ℝ v)
  (h_mag : ∀ t, inner (v t) (v t) = v₀ ^ 2) :
  ∀ t, inner (v t) (deriv v t) = (0 : ℝ) := by
  sorry







theorem theorem_1050686_problem
  {C' K : Type*} [Field K]
  (τ : Function.End C')
  (hτ : Function.Involutive τ)
  (f : C' → K) :
  (f ∘ τ = -f) ↔ (f + f ∘ τ = 0) := by
  sorry







theorem theorem_1051663_problem (p h : ℝ) (hp : 0 < p) (hp1 : p < 1) :
  let σ := fun (n : ℕ) => Real.sqrt ((n : ℝ) * p * (1 - p))
  let mgf_Zn := fun (n : ℕ) => Real.exp (-h * (n : ℝ) * p / (σ n)) * (1 - p + p * Real.exp (h / (σ n))) ^ n
  let limit := Real.exp (h ^ 2 / 2)
  let bound := fun (n : ℕ) => limit * |h ^ 3 * (1 - 2 * p) / (6 * Real.sqrt (p * (1 - p)))| * (1 / Real.sqrt (n : ℝ))
  (fun n => |mgf_Zn n - limit| - bound n) =O[atTop] (fun n => 1 / (n : ℝ)) := by
  sorry

theorem theorem_1051513_problem (f : ℝ → ℝ) (b : ℝ)
  (h_diff : ContDiffOn ℝ 3 f (Set.Icc 0 1))
  (h_bound : ∀ x ∈ Set.Icc 0 1, |iteratedDeriv 3 f x| < b)
  (h_f0 : f 0 = 1)
  (h_f1 : iteratedDeriv 1 f 0 = 1)
  (h_f2 : iteratedDeriv 2 f 0 = 2)
  (hb : b < 12) :
  f 1 < 5 := by
  sorry



theorem theorem_1050800_problem (z₁ z₂ z₃ : ℂ)
  (h_distinct : z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃)
  (h_circle : Complex.abs z₁ = Complex.abs z₂ ∧ Complex.abs z₂ = Complex.abs z₃) :
  ∃ k : ℤ, Complex.arg (z₁ / z₂) = 2 * Complex.arg ((z₃ - z₁) / (z₃ - z₂)) + 2 * Real.pi * k := by
  sorry

theorem theorem_1051321_problem (n : ℤ) (c_n : ℂ) (χ_n : ℝ)
  (h1 : c_n = ((-1 : ℂ) ^ n * (Real.sinh 3 : ℂ)) / (3 + Complex.I * (n : ℂ) * Real.pi))
  (h2 : χ_n = 2 * Complex.abs c_n) :
  χ_n = (2 * Real.sinh 3) / Real.sqrt (9 + (n : ℝ)^2 * Real.pi^2) := by
  sorry





theorem theorem_1051966_problem (τ : ℂ) (hτ : 0 < τ.im) :
  let Λ : Set ℂ := {z | ∃ n m : ℤ, z = (n : ℂ) + (m : ℂ) * τ} \ {0}
  ¬ Summable (fun z : Λ => 1 / (Complex.abs z) ^ 2) := by
  sorry

theorem theorem_1051690_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (S T : Finset V)
  (hS : LinearIndependent F (Subtype.val : S → V))
  (hT : LinearIndependent F (Subtype.val : T → V))
  (h_span : Submodule.span F (S : Set V) = Submodule.span F (T : Set V)) :
  S.card = T.card := by
  sorry

theorem theorem_1052161_problem
  (Priest : Type)
  (p : Priest)
  (Q : Prop)
  (A : Prop)
  (knows : Priest → Prop)
  (lies : Priest → Prop)
  (h1 : knows p → lies p)
  (h2 : lies p ↔ (A ↔ ¬ Q))
  (h3 : knows p) :
  A ↔ ¬ Q := by
  sorry







theorem theorem_1051821_problem
  (K N : ℕ)
  (L : Matrix (Fin K) (Fin N) ℝ)
  (X : Matrix (Fin N) (Fin K) ℝ)
  (h1 : IsUnit (X.transpose * X).det)
  (h2 : L = (X.transpose * X)⁻¹ * X.transpose)
  (h3 : IsUnit (L * L.transpose).det) :
  X = L.transpose * (L * L.transpose)⁻¹ := by
  sorry

theorem theorem_1051932_problem
  (n : ℕ)
  (S : Set ℤ)
  (hS : S.Finite)
  (T : Set (Fin n → ℤ))
  (hT : T = {t | ∀ i, t i ∈ S})
  (lex_lt : (Fin n → ℤ) → (Fin n → ℤ) → Prop)
  (h_lex : ∀ a b, lex_lt a b ↔ ∃ i, a i < b i ∧ ∀ j < i, a j = b j) :
  ∀ t ∈ T, ∃! k : ℕ, k = Set.ncard {t' ∈ T | lex_lt t' t} + 1 := by
  sorry









theorem theorem_1059334_problem 
  (x : ℕ → ℕ → ℕ)
  (a b : ℕ)
  (h_val : ∀ i j, i < 8 → j < 8 → x i j = 0 ∨ x i j = 1)
  (h_3x3 : ∀ i j, i + 2 < 8 → j + 2 < 8 → 
    (∑ r in Finset.Icc i (i + 2), ∑ c in Finset.Icc j (j + 2), x r c) = a)
  (h_2x4 : ∀ i j, i + 1 < 8 → j + 3 < 8 → 
    (∑ r in Finset.Icc i (i + 1), ∑ c in Finset.Icc j (j + 3), x r c) = b)
  (h_4x2 : ∀ i j, i + 3 < 8 → j + 1 < 8 → 
    (∑ r in Finset.Icc i (i + 3), ∑ c in Finset.Icc j (j + 1), x r c) = b)
  (h_nonempty : ∃ i j, i < 8 ∧ j < 8 ∧ x i j = 1) :
  a = 9 ∧ b = 8 := by
  sorry

theorem theorem_1059649_problem (m n : ℕ)
  (hm : m > 0) (hn : n > 0)
  (h1 : (2 * m) ∣ (n^2 + 1))
  (h2 : ∃ k : ℕ, k^2 = 2^(n - 1) + m + 4) :
  (m = 1 ∧ n = 3) ∨ (m = 61 ∧ n = 11) := by
  sorry

theorem theorem_1066287_problem (N : ℕ)
  (hN : N = ((Finset.Icc 1 (10^12)).filter (fun n => 9 ∈ n.digits 10 ∧ ¬ 9 ∣ n)).card) :
  (N : ℝ) / 10^12 > 1 / 2 := by
  sorry

theorem theorem_1067728_problem (a b p : ℕ) 
  (ha : 0 < a) (hb : 0 < b) (hp : p.Prime) 
  (h : (a + b) ^ p = p ^ a + p ^ b) : 
  a = 1 ∧ b = 1 ∧ p = 2 := by
  sorry

theorem theorem_1067569_problem
  {α : Type*} [DecidableEq α]
  (s : Finset α)
  (n : ℕ)
  (hn : 0 < n)
  (h_card : s.card = n)
  (A : Fin n → Finset α)
  (h_subset : ∀ i, A i ⊆ s)
  (h_distinct : Function.Injective A) :
  ∃ x ∈ s, Function.Injective (fun i ↦ (A i).erase x) := by
  sorry

theorem theorem_1070998_problem
  (A B C T B₁ H : EuclideanSpace ℝ (Fin 2))
  (h_mid : B₁ = midpoint ℝ B T)
  (h_ext : ∃ k : ℝ, k > 0 ∧ H - T = k • (T - A))
  (h_dist : dist T H = dist T B₁) :
  2 * dist A B + 2 * dist B C + 2 * dist C A > 4 * dist A T + 3 * dist B T + 2 * dist C T := by
  sorry



theorem theorem_1071738_problem (s d : ℝ) 
  (hs : s > 0) 
  (hd : d > 0) 
  (h_diag : d^2 = 2 * s^2) : 
  Irrational (s / d) := by
  sorry

theorem theorem_1068723_problem :
  {y : ℤ | ∃ (x : ℝ) (p : ℤ), p ≠ 0 ∧
    y = Int.floor ((x - (p : ℝ)) / (p : ℝ)) + Int.floor ((-x - 1) / (p : ℝ))} =
  ({-3, -2, -1, 0} : Set ℤ) := by
  sorry

theorem theorem_1074655_problem (a b n : ℕ)
  (ha : a > 0) (hb : b > 0) (hn : n > 0)
  (h_eq : (a^3 + b^3)^n = 4 * (a * b)^1995) :
  (a = 1 ∧ b = 1 ∧ n = 2) ∨
  (a = 2 ∧ b = 2 ∧ n = 998) ∨
  (a = 32 ∧ b = 32 ∧ n = 1247) ∨
  (a = 2^55 ∧ b = 2^55 ∧ n = 1322) ∨
  (a = 2^221 ∧ b = 2^221 ∧ n = 1328) := by
  sorry



theorem theorem_1078329_problem (x : ZMod 25 → ℝ)
  (h : ∀ i, 2 * x i - 5 * x (i + 1) + 3 * x (i + 2) ≥ 0) :
  ∀ i j, x i = x j := by
  sorry

theorem theorem_1084735_problem 
  (f s α : ℝ) 
  (hα : 0 < α ∧ α < Real.pi) 
  (hs : s > 0) 
  (hf : f > 0) : 
  (∃ a b c : ℝ, 
    a > 0 ∧ b > 0 ∧ c > 0 ∧ 
    a + b + c = 2 * s ∧ 
    a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * Real.cos α ∧ 
    f = (2 * b * c * Real.cos (α / 2)) / (b + c)) ↔ 
  f ≤ (s * (1 - Real.sin (α / 2))) / Real.cos (α / 2) := by
  sorry





theorem theorem_1088971_problem (p n : ℕ) (m : ℤ)
  (hp : Nat.Prime p)
  (hn : n > 0)
  (hm : m > 0)
  (h : (p : ℤ)^n + 144 = m^2) :
  (p = 5 ∧ n = 2 ∧ m = 13) ∨
  (p = 2 ∧ n = 8 ∧ m = 20) ∨
  (p = 3 ∧ n = 4 ∧ m = 15) := by
  sorry



theorem theorem_144771_problem
  (G : Type*) [TopologicalSpace G] [Group G] [TopologicalGroup G]
  [CompactSpace G] [T2Space G]
  (H : Set G) (hH : IsClosed H)
  (chi : H → ℂ) (hchi : Continuous chi) :
  ∃ phi : G → ℂ, Continuous phi ∧ ∀ x : H, phi x = chi x := by
  sorry



