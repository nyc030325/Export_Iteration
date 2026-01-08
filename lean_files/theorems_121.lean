import Mathlib
import Mathlib.Tactic



theorem theorem_655674_problem (X : Type*) [TopologicalSpace X]
  (h : IsClosed (Set.diagonal X)) :
  T2Space X := by
  sorry







theorem theorem_656176_problem
  (k : Type*) [Field k] [IsAlgClosed k]
  (A : Type*) [Ring A] [Algebra k A] [Module.Finite k A]
  (P P' : Type*)
  [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
  [Module.Finite k P] [Module.Projective A P]
  [AddCommGroup P'] [Module k P'] [Module A P'] [IsScalarTower k A P']
  [Module.Finite k P'] [Module.Projective A P']
  (h : ∀ (V : Type*) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V],
    Nonempty ((P →ₗ[A] V) ≃ₗ[k] (P' →ₗ[A] V))) :
  Nonempty (P ≃ₗ[A] P') := by
  sorry

theorem theorem_656253_problem
  (f : ℝ → ℝ)
  (h_diff : Differentiable ℝ f)
  (h_supp : HasCompactSupport f) :
  ∀ x : ℝ, |f x| ≤ (1 / 2) * ∫ t, |deriv f t| := by
  sorry

theorem theorem_655852_problem
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) ℝ)
  (A_plus : Matrix (Fin n) (Fin m) ℝ)
  (b db : Fin m → ℝ)
  (x dx : Fin n → ℝ)
  (σ₁ σr : ℝ)
  (h_σ_pos : 0 < σr)
  (h_σ_order : σr ≤ σ₁)
  (h_A_norm : ∀ v, ‖A.mulVec v‖ ≤ σ₁ * ‖v‖)
  (h_A_plus_norm : ∀ v, ‖A_plus.mulVec v‖ ≤ (1 / σr) * ‖v‖)
  (h_x : x = A_plus.mulVec b)
  (h_dx : dx = A_plus.mulVec db)
  (h_consistent : A.mulVec x = b)
  (h_b_nz : b ≠ 0)
  (h_x_nz : x ≠ 0) :
  ‖dx‖ / ‖x‖ ≤ (σ₁ / σr) * (‖db‖ / ‖b‖) := by
  sorry

theorem theorem_655676_problem 
  (f : ℝ → ℝ) (a b c : ℝ)
  (hc : a < c ∧ c < b)
  (h_int : ∀ x y, a < x → x < y → y < b → IntervalIntegrable f volume x y)
  (L1 L2 : ℝ)
  (h1 : Filter.Tendsto (fun h => ∫ x in a + h..c, f x) (nhdsWithin 0 (Set.Ioi 0)) (nhds L1))
  (h2 : Filter.Tendsto (fun k => ∫ x in c..b - k, f x) (nhdsWithin 0 (Set.Ioi 0)) (nhds L2)) :
  ∃ g : ℝ → ℝ,
    (∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), 
      Filter.Tendsto (fun k => ∫ x in a + h..b - k, f x) (nhdsWithin 0 (Set.Ioi 0)) (nhds (g h))) ∧
    Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (L1 + L2)) := by
  sorry



theorem theorem_656298_problem (x : ℝ) 
  (h1 : 0 < x) 
  (h2 : |Real.log x| < 1) : 
  HasDerivAt (fun y => Real.arcsin (Real.log y)) (1 / (x * Real.sqrt (1 - (Real.log x)^2))) x := by
  sorry

theorem theorem_655029_problem
  (a b c d : ℤ)
  (M : Matrix (Fin 2) (Fin 2) ℤ)
  (hM : M = !![a, b; c, d])
  (hM_inv : IsUnit M) :
  let ϕ : ℂˣ × ℂˣ → ℂˣ × ℂˣ := fun t ↦
    (t.1 ^ a * t.2 ^ (-b), t.1 ^ c * t.2 ^ (-d))
  Function.Bijective ϕ ∧ ∀ x y, ϕ (x * y) = ϕ x * ϕ y := by
  sorry

theorem theorem_655919_problem (L : Set (List Bool))
  (hL : L = {w | ∃ u v : List Bool, w = u ++ v ++ [true] ++ v ∧ v.length = 2 * u.length}) :
  ∃ f : List Bool →. Unit, Partrec f ∧ ∀ w, w ∈ L ↔ (f w).Dom := by
  sorry

theorem theorem_656521_problem (X : Type*) [TopologicalSpace X]
  (f : X → ℝ) (hf : Continuous f) (y : ℝ) :
  (⋂ (h : ℝ) (_ : 0 < h), f ⁻¹' (Set.Icc y (y + h))) = f ⁻¹' {y} := by
  sorry





theorem theorem_656102_problem
  {X : Type*} [MetricSpace X]
  (a b c : X)
  (h : dist a b + dist b c + dist a c < 2 * max (dist a b) (max (dist b c) (dist a c))) :
  ¬ ∃ ϕ : X → EuclideanSpace ℝ (Fin 2), ∀ x y, dist x y = dist (ϕ x) (ϕ y) := by
  sorry







theorem theorem_656465_problem (H : Subgroup (alternatingGroup (Fin 4))) :
  Nat.card H ≠ 6 := by
  sorry

theorem theorem_656982_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (r : ℝ → E)
  (I : Set ℝ)
  (c : ℝ)
  (hI : Convex ℝ I)
  (h_diff : ContDiffOn ℝ 2 r I)
  (hc : c > 0)
  (h_norm : ∀ t ∈ I, ‖deriv r t‖ = c) :
  ∀ t ∈ I, inner (deriv r t) (deriv (deriv r) t) = (0 : ℝ) := by
  sorry

theorem theorem_656670_problem (f : ℝ → ℝ) (x₀ : ℝ)
  (h_smooth : ContDiff ℝ ⊤ f) (h_compact : HasCompactSupport f) :
  ∫ x, f x ∂(MeasureTheory.Measure.dirac x₀) = f x₀ := by
  sorry





theorem theorem_656903_problem (f : ℝ → ℝ) (h_f : ∀ x, f x = 1 / (Real.exp x + 1)) (C : ℝ) :
  ∀ x, HasDerivAt (fun x => x - Real.log (1 + Real.exp x) + C) (f x) x := by
  sorry

















theorem theorem_657256_problem :
  CompleteSpace (ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ) := by
  sorry



theorem theorem_657262_problem (y : ℝ → ℝ)
  (h_diff : Differentiable ℝ y)
  (h_diff' : Differentiable ℝ (deriv y))
  (h_nonzero : ∀ x, y x ≠ 0)
  (h_de : ∀ x, deriv (deriv y) x / y x = 1 / 2 + (deriv y x) ^ 2 / (2 * (y x) ^ 2)) :
  ∃ A B : ℝ, ∀ x, y x = B * (Real.cosh (x / 2 + A)) ^ 2 := by
  sorry

theorem theorem_657745_problem (r h : ℝ) (hr : 0 < r) (hh : 0 < h) :
  let cone : Set (ℝ × ℝ × ℝ) := {p | 0 ≤ p.2.2 ∧ p.2.2 ≤ h ∧ p.1 ^ 2 + p.2.1 ^ 2 ≤ (r / h * p.2.2) ^ 2}
  MeasureTheory.volume cone = ENNReal.ofReal ((1 / 3 : ℝ) * Real.pi * r ^ 2 * h) := by
  sorry

theorem theorem_657543_problem :
  {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}.Infinite := by
  sorry

theorem theorem_658017_problem
  (m : ℕ) (hm : m > 1)
  (n : ℤ) (h_coprime : Int.gcd n m = 1)
  (g : ℤ) (hg : IsPrimitiveRoot (g : ZMod m) (Nat.totient m))
  (k : ℕ) (hk : (n : ZMod m) = (g : ZMod m) ^ k)
  (χ : DirichletCharacter ℂ m) :
  χ n = (χ g) ^ k := by
  sorry



theorem theorem_658033_problem
  (G H : Type*) [Group G] [Group H]
  (ϕ : G → H)
  (h_hom : ∀ g₁ g₂, ϕ (g₁ * g₂) = ϕ g₁ * ϕ g₂)
  (h_bij : Function.Bijective ϕ) :
  Nonempty (G ≃* H) := by
  sorry



theorem theorem_657688_problem
  (a b c : ℝ)
  (ha : a > 0)
  (h_pos : ∀ x : ℝ, a * x^2 + b * x + c > 0)
  (x : ℝ)
  (hx : x ≠ 0) :
  deriv (fun t => -Real.sqrt (a * t^2 + b * t + c) / (2 * c * t^2)) x =
  1 / (x^3 * Real.sqrt (a * x^2 + b * x + c)) +
  (b / (4 * c)) * (1 / (x^2 * Real.sqrt (a * x^2 + b * x + c))) := by
  sorry

theorem theorem_657386_problem
  -- We abstract the setting of divisors on a variety as an ordered group with lattice structure
  {Div : Type*} [OrderedAddCommGroup Div] [CompleteLattice Div]
  {K : Type*} -- The function field
  (principal_div : K → Div) -- Map taking a function to its principal divisor
  (D : Div)
  (VeryAmple : Div → Prop) -- Abstract predicate for "Very Ample"
  (h_very_ample : VeryAmple D)
  (n : ℕ)
  (f : Fin n → K) -- Basis functions f_1, ..., f_n
  -- The basis functions belong to L(D), meaning div(f_i) + D >= 0
  (h_basis_mem : ∀ i, principal_div (f i) + D ≥ 0)
  -- Definition of D' as the negative of the gcd (infimum) of the principal divisors
  (D' : Div)
  (h_D'_def : D' = - (⨅ i, principal_div (f i)))
  -- Hypothesis: The linear system corresponding to D' has no fixed components
  -- This means the gcd of the effective divisors relative to D' is 0
  (h_no_fixed : (⨅ i, principal_div (f i) + D') = 0) :
  D' = D := by
  sorry





theorem theorem_657482_problem (x : ℝ) (h1 : -1 < x) (h2 : x ≤ 4) :
  (1 + x) * Real.log (1 + x) - x - x^2 / 4 ≥ 0 := by
  sorry



theorem theorem_658010_problem :
  {q : Quaternion ℝ | ∀ x : Quaternion ℝ, q * x = x * q} = Set.range (algebraMap ℝ (Quaternion ℝ)) := by
  sorry

theorem theorem_658275_problem
  (I : Set ℝ) (hI_open : IsOpen I) (hI_conn : IsConnected I) (hI_one : 1 ∉ I)
  (y : ℝ → ℝ) (hy_diff : ContDiffOn ℝ 2 y I)
  (h_ode : ∀ x ∈ I, deriv (deriv y) x - (x / (x - 1)) * deriv y x + (1 / (x - 1)) * y x = 0) :
  ∃ C₁ C₂ : ℝ, ∀ x ∈ I, y x = C₁ * Real.exp x + C₂ * x := by
  sorry





theorem theorem_657625_problem (F : ℝ → ℝ) (r a b : ℝ) (G : ℝ → ℝ)
  (h_int : a ≤ b)
  (h_def : (∀ x, G x = -(F x - r * x)) ∨ (∀ x, G x = F (-x) + r * x))
  (h_mono : MonotoneOn G (Set.Icc a b)) :
  F b - F a ≤ r * (b - a) := by
  sorry



theorem theorem_658587_problem
  (n : ℕ)
  {K : Type*} [Field K]
  (A B C D : Matrix (Fin n) (Fin n) K)
  (hB : B.det = 0)
  (hD : D.det ≠ 0)
  (h_eq : A * B = C * D⁻¹) :
  C.det = 0 := by
  sorry



theorem theorem_658478_problem (K : Type*) [Field K] [TopologicalSpace K]
  (h : ∀ f : K → K, Continuous f ↔ ∃ p : Polynomial K, ∀ x, f x = Polynomial.eval x p) :
  False := by
  sorry





theorem theorem_659468_problem (x : ℕ → ℝ) 
  (h_bounded : ∃ M : ℝ, ∀ n : ℕ, |x n| ≤ M) :
  ∃ (φ : ℕ → ℕ) (a : ℝ), StrictMono φ ∧ Filter.Tendsto (x ∘ φ) Filter.atTop (nhds a) := by
  sorry

theorem theorem_658606_problem
  (n : ℕ)
  (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
  (hF : Fintype.card F = 2 ^ n)
  (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
  (∃ x : F, x ^ 2 + b * x + a = 0) ↔ Algebra.trace (ZMod 2) F (a / b ^ 2) = 0 := by
  sorry













theorem theorem_659174_problem (A B : Type*) [Ring A] [Ring B]
  (f : A →+* B) (hf : Function.Surjective f) :
  ringChar B ∣ ringChar A := by
  sorry

theorem theorem_659397_problem
  (a b r x₀ y₀ θ c : ℝ)
  (h_theta : 0 < θ ∧ θ < Real.pi)
  (h_c : c = Real.tan (θ / 2))
  (h_first_quad : x₀ > 0 ∧ y₀ > 0)
  (h_tan_xaxis : y₀ = r)
  (h_tan_line : abs (x₀ * Real.sin θ - y₀ * Real.cos θ) = r)
  (h_on_circle : (x₀ - a)^2 + (y₀ - b)^2 = r^2) :
  (r / c - a)^2 + (r - b)^2 = r^2 := by
  sorry





theorem theorem_658763_problem (n : ℕ) (hn : n > 0) :
  ∏ k in Finset.Ico 1 n, Real.cos ((k : ℝ) * Real.pi / n) =
  Real.sin ((n : ℝ) * Real.pi / 2) / (2 : ℝ) ^ (n - 1) := by
  sorry



theorem theorem_659611_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (K : Set H) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
  (y : H) (hy : y ∉ K)
  (x : H) (hx_in : x ∈ K)
  (hx_closest : ∀ w ∈ K, ‖x - y‖ ≤ ‖w - y‖)
  (z : H) (hz : z ∈ K) :
  ‖z - y‖ ≥ ‖x - y‖ := by
  sorry



theorem theorem_659663_problem
  {K : Type*} [Field K]
  {N : ℕ}
  {X : Type*} (x : X) (f : X → K)
  (M : Matrix (Fin N) (Fin N) K)
  (M' : Matrix (Fin N) (Fin N) K)
  (h_nonzero : f x ≠ 0)
  (h_def : ∀ i j, M' i j = M i j / f x) :
  M.det = (f x) ^ N * M'.det := by
  sorry

theorem theorem_660162_problem (V : Type*) :
  let C := fun (n : ℕ) => FreeAbelianGroup (Fin (n + 1) → V)
  let d := fun (n : ℕ) => FreeAbelianGroup.lift (fun (σ : Fin (n + 2) → V) =>
    ∑ i : Fin (n + 2), (-1 : ℤ)^(i : ℕ) • FreeAbelianGroup.of (σ ∘ i.succAbove))
  ∀ n : ℕ, (d n).comp (d (n + 1)) = 0 := by
  sorry



theorem theorem_659367_problem (h : ℝ) (h_ne_zero : h ≠ 0) :
  ¬ ∃ (α β : ℝ) (S : Set ℝ), IsOpen S ∧ S.Nonempty ∧
    ∀ x ∈ S, Real.sqrt (x^2 + h^2) = α * x + β := by
  sorry

theorem theorem_659994_problem :
  circleIntegral (fun z ↦ 1 / z) 0 1 = 2 * π * I := by
  sorry

theorem theorem_659737_problem (c : ℝ) (hc : 1 < c) (T : ℝ → ℕ)
  (hT : ∀ N : ℝ, N > 1 → N / c ^ (T N) ≤ 1 ∧ N / c ^ (T N - 1) > 1) :
  Asymptotics.IsBigO Filter.atTop (fun N ↦ (T N : ℝ)) (fun N ↦ Real.logb c N) := by
  sorry

theorem theorem_659816_problem {α : Type} (P : α → Prop) :
  (∃! x, P x) ↔ ∃ x, (P x ∧ ∀ y, P y → x = y) := by
  sorry





theorem theorem_659823_problem
  (A : Finset ℕ)
  (hA : ∀ a ∈ A, 0 < a)
  (S : Finset ℕ)
  (hS : S ⊆ A) :
  Finset.lcm S id = ∏ p in A.sup (fun a => a.factorization.support), p ^ (S.sup (fun a => a.factorization p)) := by
  sorry

theorem theorem_659592_problem (f : ℝ → ℝ)
  (h_diff : ∀ x ∈ Set.Icc 0 2, DifferentiableAt ℝ f x)
  (h_diff2 : ∀ x ∈ Set.Icc 0 2, DifferentiableAt ℝ (deriv f) x)
  (h_bound_f : ∀ x ∈ Set.Icc 0 2, |f x| ≤ 1)
  (h_bound_f'' : ∀ x ∈ Set.Icc 0 2, |deriv (deriv f) x| ≤ 1) :
  ∀ x ∈ Set.Icc 0 2, |deriv f x| ≤ 2 := by
  sorry

theorem theorem_660318_problem (S : ℕ → Set ℕ)
  (h₀ : S 0 = univ)
  (h₁ : ∀ n, S (n + 1) = S n \ {n}) :
  (⋂ n, S n) = ∅ := by
  sorry

theorem theorem_660239_problem 
  {U : Type*} 
  (M N : Set U) 
  (is_ordinal : U → Prop) 
  (is_ordinal_in_model : Set U → U → Prop) 
  (hM_card : Cardinal.mk M = Cardinal.mk (Set.univ : Set U))
  (hN_card : Cardinal.mk N = Cardinal.mk (Set.univ : Set U))
  (h_same_ord : {x | is_ordinal_in_model M x} = {x | is_ordinal_in_model N x}) :
  ∀ β, is_ordinal β → (is_ordinal_in_model M β ↔ is_ordinal_in_model N β) := by
  sorry





theorem theorem_660680_problem (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f) :
  ∀ φ : ℝ → ℝ, ContDiff ℝ ⊤ φ →
  let δ := fun (ψ : ℝ → ℝ) ↦ ψ 0
  let δ' := fun (ψ : ℝ → ℝ) ↦ -(deriv ψ 0)
  let lhs := δ' (fun x ↦ f x * φ x)
  let rhs := f 0 * δ' φ - (deriv f 0) * δ φ
  lhs = rhs := by
  sorry







theorem theorem_660519_problem (x y z : ℕ) (h : 2^x + 5^y = 7^z) :
  x = 1 ∧ y = 1 ∧ z = 1 := by
  sorry

theorem theorem_660742_problem (n : ℕ) (x : Fin (n + 1) → ℝ) (hx : x ≠ 0) :
  Function.Surjective (fun (v : Fin (n + 1) → ℝ) => 2 * ∑ i, x i * v i) := by
  sorry







