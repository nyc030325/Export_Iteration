import Mathlib
import Mathlib.Tactic



theorem theorem_987456_problem
  (f g : ℝ → ℝ)
  (hf : ∀ x, f x = Real.log (1 - (Real.sin (x / 3)) ^ 2))
  (hg : ∀ x, g x = Real.log (1 - (Real.sin (x / 2)) ^ 2)) :
  Filter.Tendsto (fun x ↦ f x / g x) (nhdsWithin 0 {x | x ≠ 0}) (nhds ((4 : ℝ) / 9)) := by
  sorry







theorem theorem_987828_problem (n : ℕ) (hn : n > 0)
  (H : ℕ → ℝ) (H_gen : ℕ → ℕ → ℝ)
  (hH : ∀ k, H k = ∑ j in Finset.Icc 1 k, (1 : ℝ) / j)
  (hH_gen : ∀ k m, H_gen k m = ∑ j in Finset.Icc 1 k, (1 : ℝ) / ((j : ℝ) ^ m)) :
  ∑ k in Finset.Icc 1 n, ((H (k + 1)) ^ 2 - H_gen (k + 1) 2) / ((k : ℝ) + 2) =
  (1 / 3 : ℝ) * ((H n) ^ 3 - 3 * (H n) * (H_gen n 2) + 2 * (H_gen n 3)) +
  ((2 * n + 3 : ℝ) * ((H n) ^ 2 - H_gen n 2) + 2 * (H n)) / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by
  sorry

theorem theorem_988285_problem {G : Type*} (op : G → G → G)
  (h_assoc : ∀ a b c : G, op (op a b) c = op a (op b c))
  (h_identity_inverse : ∃ e : G, (∀ a : G, op e a = a ∧ op a e = a) ∧
    (∀ a : G, ∃ b : G, op a b = e ∧ op b a = e)) :
  ∃ (g : Group G), g.mul = op := by
  sorry

theorem theorem_987555_problem (n : ℝ) (c : ℂ) (hn : 0 < n) :
  {x : ℂ | x ^ (n : ℂ) = c}.Finite ∧ {x : ℂ | x ^ (n : ℂ) = c}.ncard ≤ Nat.ceil n := by
  sorry

theorem theorem_988607_problem
  (U : Set ℂ)
  (hU_open : IsOpen U)
  (hU_conn : IsConnected U)
  (f : ℂ → ℂ)
  (hf : DifferentiableOn ℂ f U)
  (hf_nz : ¬ Set.EqOn f 0 U) :
  ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U → (∀ z ∈ U, g z * f z = 0) → Set.EqOn g 0 U := by
  sorry













theorem theorem_988989_problem (p : ℕ) (hp : Nat.Prime p) (h : 4 ∣ (p - 1)) :
  ∃ H : Subgroup (ZMod p)ˣ, IsCyclic H ∧ Nat.card H = 4 := by
  sorry







theorem theorem_988796_problem (x x' : ℕ → ℝ)
  (h1 : ∀ ε > 0, ∃ m, ∀ n > m, |x n| < ε / 2)
  (h2 : ∀ n, 0 < n → x' n = (1 / (n : ℝ)) * ∑ k in Finset.Icc 1 n, x k) :
  ∀ ε > 0, ∃ n₀, ∀ n > n₀, |x' n| < ε := by
  sorry



theorem theorem_988618_problem :
  (∑' n : ℕ, (-1 : ℝ) ^ n / ((n : ℝ) ^ 2 + 1)) = 1 / 2 + Real.pi / (2 * Real.sinh Real.pi) := by
  sorry



theorem theorem_989426_problem (f : ℝ → ℝ) (h : ContDiff ℝ 2 f) (x : ℝ) :
  f x = f 0 + deriv f 0 * x + ∫ t in (0)..x, (deriv (deriv f) t) * (x - t) := by
  sorry









theorem theorem_989746_problem (A : Type*) [CommRing A] (q p : A)
  (hq : q ≠ 0) (hp : p ≠ 0) :
  let I : Ideal (Polynomial A) := Ideal.span {Polynomial.C q, Polynomial.C p}
  let J : Ideal A := Ideal.span {q}
  let A_bar := A ⧸ J
  let p_bar : Polynomial A_bar := Polynomial.C (Ideal.Quotient.mk J p)
  let K : Ideal (Polynomial A_bar) := Ideal.span {p_bar}
  let phi_raw : Polynomial A →+* (Polynomial A_bar ⧸ K) :=
    (Ideal.Quotient.mk K).comp (Polynomial.mapRingHom (Ideal.Quotient.mk J))
  ∀ (h : I ≤ RingHom.ker phi_raw), Function.Injective (Ideal.Quotient.lift I phi_raw h) := by
  sorry



theorem theorem_989973_problem (n : ℕ) (h : n > 1) :
  ¬ Module.Free ℤ (ZMod n) := by
  sorry





theorem theorem_990295_problem (n : ℕ) (hn : 0 < n) :
  Set.ncard { z : ℂ | Complex.abs z = 1 ∧ orderOf z = n } = Nat.totient n := by
  sorry

theorem theorem_989588_problem (p : ℝ → ℝ)
  (h_diff : Differentiable ℝ p)
  (h_indep : ∀ (r : ℝ) (θ₁ θ₂ : ℝ), r > 0 →
    p (r * Real.cos θ₁) * p (r * Real.sin θ₁) = p (r * Real.cos θ₂) * p (r * Real.sin θ₂)) :
  ∀ x y : ℝ, x > 0 → y > 0 → deriv p x / (x * p x) = deriv p y / (y * p y) := by
  sorry

theorem theorem_989475_problem (r t : ℝ) (hr : r > 0)
  (A : ℝ × ℝ := (r * Real.cos t, r * Real.sin t))
  (string_dir : ℝ × ℝ := (Real.sin t, -Real.cos t))
  (P : ℝ × ℝ := (A.1 + (r * t) * string_dir.1, A.2 + (r * t) * string_dir.2)) :
  P.1 = r * (Real.cos t + t * Real.sin t) ∧
  P.2 = r * (Real.sin t - t * Real.cos t) := by
  sorry



theorem theorem_990244_problem (a b : ℝ) (f : ℝ → ℝ)
  (h : ContinuousOn f (Set.Icc a b)) :
  UniformContinuousOn f (Set.Icc a b) := by
  sorry















theorem theorem_990404_problem (A : Type*) [TopologicalSpace A]
  (h_disc : ¬ ConnectedSpace A)
  (n : ℕ)
  (h_decomp : ∃ (U : Fin n → Set A),
    (∀ i, IsClopen (U i)) ∧
    (∀ i, (U i).Nonempty) ∧
    Pairwise (Disjoint on U) ∧
    (⋃ i, U i) = Set.univ) :
  ∃ (U : Fin n → Set A),
    (∀ i, IsClopen (U i)) ∧
    (∀ i, (U i).Nonempty) ∧
    Pairwise (Disjoint on U) ∧
    (⋃ i, U i) = Set.univ := by
  sorry

theorem theorem_990438_problem
  {X : Type*} [TopologicalSpace X]
  (Y : Set X)
  (K : Set X)
  (hK : K ⊆ Y)
  (h_compact_Y : IsCompact (Subtype.val ⁻¹' K : Set Y)) :
  IsCompact K := by
  sorry



theorem theorem_990744_problem (α : Type*) [Finite α] (L : Set (List α)) :
  Set.Countable L := by
  sorry

theorem theorem_991042_problem (A : Set ZFSet) (a : ZFSet) (h : a ∈ A) :
  ¬ ∃ x, x ∈ a ∧ x = a := by
  sorry

theorem theorem_988595_problem
  (a b c q r l_X : ℝ)
  (h_pos : 0 < a ∧ 0 < b ∧ 0 < c)
  (h_tri : a < b + c ∧ b < a + c ∧ c < a + b)
  (h_qr : q = c ∧ r = b)
  (h_bisector : ∃ (u v : ℝ),
    u > 0 ∧ v > 0 ∧
    u + v = a ∧
    u / v = c / b ∧
    b^2 * u + c^2 * v = a * (l_X^2 + u * v)) :
  l_X^2 = q * r * (1 - a^2 / (q + r)^2) := by
  sorry

theorem theorem_990729_problem (a b c : ℤ) 
  (h : c^2 = a^2 * b^2 - a^2 - b^2) : 
  a = 0 ∧ b = 0 ∧ c = 0 := by
  sorry



theorem theorem_991043_problem (f : ℝ → ℝ) (c : ℝ)
  (h_sign_change : ∃ ε > 0, 
    (∀ x ∈ Set.Ioo (c - ε) c, deriv (deriv f) x < 0 ∧ ∀ x ∈ Set.Ioo c (c + ε), deriv (deriv f) x > 0) ∨ 
    (∀ x ∈ Set.Ioo (c - ε) c, deriv (deriv f) x > 0 ∧ ∀ x ∈ Set.Ioo c (c + ε), deriv (deriv f) x < 0)) :
  ∃ ε > 0, 
    (ConcaveOn ℝ (Set.Ioo (c - ε) c) f ∧ ConvexOn ℝ (Set.Ioo c (c + ε)) f) ∨ 
    (ConvexOn ℝ (Set.Ioo (c - ε) c) f ∧ ConcaveOn ℝ (Set.Ioo c (c + ε)) f) := by
  sorry





theorem theorem_990721_problem
  -- Abstract definitions for the stochastic calculus components
  {Process : Type*}
  (isContinuousLocalMartingale : Process → Prop)
  (isPredictable : Process → Prop)
  (isWellDefinedStochasticIntegral : Process → Process → Prop)
  (stochasticIntegral : Process → Process → Process)   -- Represents H • M
  (covariation : Process → Process → Process)          -- Represents [X, Y]
  (integral : Process → Process → Process)             -- Represents ∫ H dX
  -- Variables
  (M H : Process)
  -- Conditions
  (hM : isContinuousLocalMartingale M)
  (hH : isPredictable H)
  (hDef : isWellDefinedStochasticIntegral H M) :
  -- Conclusion: [H•M, H•M] = ∫ H d[H•M, M]
  covariation (stochasticIntegral H M) (stochasticIntegral H M) = 
  integral H (covariation (stochasticIntegral H M) M) := by
  sorry

theorem theorem_991098_problem
  (n : ℕ)
  (D : Set (Fin n → ℝ))
  (hD_compact : IsCompact D)
  (hD_convex : Convex ℝ D)
  (hD_nonempty : D.Nonempty)
  (f : D → D)
  (hf_cont : Continuous f) :
  ∃ x : D, f x = x := by
  sorry



theorem theorem_990909_problem 
  (S B : Type*) [Fintype S] [Fintype B]
  (C : S → B → ℕ)
  (hC_range : ∀ s b, C s b = 0 ∨ C s b = 1)
  (A : Set (S → B))
  (hA : A = { f | ∀ s, C s (f s) = 1 })
  (h_nonempty : A.Nonempty) :
  ∃ f : S → B, ∀ s, C s (f s) = 1 := by
  sorry

theorem theorem_991353_problem (a b c : ℝ) 
  (h_pos : 0 < a ∧ 0 < b ∧ 0 < c) 
  (h_ineq : a + b > c ∧ b + c > a ∧ c + a > b) :
  (a = b ∧ b = c) → (a = b ∨ b = c ∨ c = a) := by
  sorry

theorem theorem_991257_problem (b x : ℝ) (h1 : 0 < b) (h2 : b ≠ 1) :
  deriv (fun t => b ^ t) x = b ^ x * Real.log b := by
  sorry







theorem theorem_991577_problem
  {Λ : Type*} (X : Λ → Type*) [∀ i, TopologicalSpace (X i)] :
  (Pi.topologicalSpace : TopologicalSpace (Π i, X i)) =
    TopologicalSpace.generateFrom {s | ∃ (U : Π i, Set (X i)), (∀ i, IsOpen (U i)) ∧ s = Set.pi Set.univ U} ↔
  Set.Finite {i | ¬ Subsingleton (X i)} := by
  sorry

theorem theorem_991314_problem (p : ℕ) (hp : Nat.Prime p) (h_p_gt_5 : p > 5) :
  p ∣ ∑ i in Finset.range (p - 1), 10 ^ i := by
  sorry







theorem theorem_991581_problem
  (E L : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup L] [NormedSpace ℝ L]
  (a : ℝ) (ha : a > 0)
  (p : ℝ) (hp : p = 6)
  (ι : E →ₗ[ℝ] L)
  (C : ℝ) (hC : C > 0)
  (h_emb : ∀ u, ‖ι u‖ ≤ C * ‖u‖) :
  Continuous (fun u ↦ a * ‖ι u‖ ^ p) := by
  sorry

theorem theorem_991044_problem {W : Type*} [LinearOrder W]
  (f : W → W) (hf : StrictMono f)
  (hW : ∀ X : Set W, X.Nonempty → ∃ z ∈ X, ∀ y ∈ X, z ≤ y) :
  ∀ x, x ≤ f x := by
  sorry









theorem theorem_992149_problem
  {α : Type*} [Fintype α] [DecidableEq α]
  (n : ℕ) (m : ℕ)
  (A : Fin n → Finset α)
  (hn : n ≥ 1)
  (hm : 1 ≤ m ∧ m ≤ n)
  (S : ℕ → ℕ)
  (L_m : ℕ)
  (hS : ∀ k, S k = (Finset.univ.filter (λ x => (Finset.univ.filter (λ i => x ∈ A i)).card = k)).card)
  (hL : L_m = (Finset.univ.filter (λ x => (Finset.univ.filter (λ i => x ∈ A i)).card ≥ m)).card) :
  L_m = ∑ k in Finset.Icc m n, (k - 1).choose (m - 1) * S k := by
  sorry

theorem theorem_992061_problem (a b : ℝ) (hab : a < b) :
  ¬ ∃ (γ : ℝ → ℝ × ℝ),
    (∀ t ∈ Set.Icc a b, γ t ≠ ((0 : ℝ), (0 : ℝ))) ∧
    γ a = ((1 : ℝ), (0 : ℝ)) ∧
    γ b = ((-1 : ℝ), (0 : ℝ)) ∧
    (∃ (p v : ℝ × ℝ), ∀ t ∈ Set.Icc a b, γ t = p + t • v) := by
  sorry





theorem theorem_991899_problem :
  let P : Polynomial ℤ := X^2 + X + 1
  let R := AdjoinRoot P
  let I := Ideal.span {(2 : R)}
  Nonempty (R ⧸ I ≃+* GaloisField 2 2) := by
  sorry



theorem theorem_992032_problem (n : ℕ) (i : Fin n)
  (boundary : Submodule ℝ (Fin n → ℝ))
  (h_boundary : ∀ x, x ∈ boundary ↔ x i = 0)
  (f : boundary → ℝ)
  (hf : ContDiff ℝ ⊤ f) :
  ∃ g : (Fin n → ℝ) → ℝ, ContDiff ℝ ⊤ g ∧ ∀ x : boundary, g x = f x := by
  sorry

theorem theorem_991941_problem
  (γ : ℤ → ℝ)
  (h_stationary : ∀ h : ℤ, γ h = γ (-h))
  (h_decay : Filter.Tendsto (fun h : ℕ ↦ γ h) Filter.atTop (nhds 0))
  (h_summable : Summable (fun h : ℕ ↦ γ h)) :
  Filter.Tendsto (fun T : ℕ ↦ (T : ℝ) * ((1 / (T : ℝ)^2) *
    ∑ t in Finset.range T, ∑ s in Finset.range T, γ ((t : ℤ) - s)))
  Filter.atTop (nhds (γ 0 + 2 * ∑' h : ℕ, γ (h + 1))) := by
  sorry



theorem theorem_992490_problem (c ν β γ : ℝ) (x : ℝ → ℝ)
  (h_diff : Differentiable ℝ x)
  (h_ode : ∀ t, deriv x t = 1 / (c * ν * (1 - x t) + β * x t * (1 - x t) - γ * x t))
  (h_ic : x 0 = 1) :
  ∀ t, c * ν * (x t) + (β - c * ν - γ) * (x t)^2 / 2 - β * (x t)^3 / 3 =
       t + c * ν + (β - c * ν - γ) / 2 - β / 3 := by
  sorry







theorem theorem_992541_problem (B : ℝ → ℝ) (X : ℝ → ℝ)
  (hB : Continuous B)
  (hX : ∀ t, X t = ∫ s in (0)..t, B s) :
  ∀ t, HasDerivAt X (B t) t := by
  sorry



theorem theorem_992731_problem
  (A B : Set ℝ)
  (f g : ℝ → ℝ)
  (a b : ℝ)
  (A' : Set ℝ)
  (hA' : A' = A ∩ f ⁻¹' B)
  (ha : a ∈ closure A')
  (hb : b ∈ B)
  (hf : Filter.Tendsto f (nhdsWithin a A') (nhds b))
  (hg : ContinuousWithinAt g B b) :
  Filter.Tendsto (g ∘ f) (nhdsWithin a A') (nhds (g b)) := by
  sorry





theorem theorem_992514_problem
  (f g : ℝ → ℝ)
  (S : Set ℝ)
  (hS : S.Finite)
  (hg_smooth : ContDiff ℝ ⊤ g)
  (hg_zero : ∀ x ∈ S, g x = 0)
  (hg_nonzero : ∀ x ∉ S, g x ≠ 0)
  (hf_diff : ∀ x ∉ S, DifferentiableAt ℝ f x)
  (hf_cont : Continuous f) :
  Differentiable ℝ (fun x ↦ f x * g x) := by
  sorry





theorem theorem_993379_problem (a b : ℝ) (f g : ℝ → ℝ)
  (hf_pos : ∀ x ∈ Set.Icc a b, 0 < f x)
  (hg_pos : ∀ x ∈ Set.Icc a b, 0 < g x)
  (hf_mono : MonotoneOn f (Set.Icc a b))
  (hg_mono : MonotoneOn g (Set.Icc a b))
  (hf_conv : ConvexOn ℝ (Set.Icc a b) f)
  (hg_conv : ConvexOn ℝ (Set.Icc a b) g) :
  ConvexOn ℝ (Set.Icc a b) (f * g) := by
  sorry





