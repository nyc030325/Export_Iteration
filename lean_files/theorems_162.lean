import Mathlib
import Mathlib.Tactic



theorem theorem_881856_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA_symm : A.IsSymm) (hB_symm : B.IsSymm)
  (hA_psd : A.PosSemidef) (hB_psd : B.PosSemidef)
  (h_le : (B - A).PosSemidef)
  [NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ)]
  (h_norm_inv : ∀ (M : Matrix (Fin n) (Fin n) ℝ) (U V : Matrix (Fin n) (Fin n) ℝ),
    U ∈ Matrix.orthogonalGroup (Fin n) ℝ → V ∈ Matrix.orthogonalGroup (Fin n) ℝ →
    ‖U * M * V‖ = ‖M‖) :
  ‖A‖ ≤ ‖B‖ := by
  sorry

theorem theorem_881805_problem
  (p : ℕ) [Fact p.Prime] (hp : Odd p)
  (g : ZMod p) (hg : IsPrimitiveRoot g (p - 1))
  (a : ℤ) (ha : Odd a) :
  (g ^ a) ^ ((p - 1) / 2) = g ^ ((p - 1) / 2) := by
  sorry

theorem theorem_882158_problem {L : Type*} [LinearOrder L]
  (a b : L) (h : a < b) :
  Set.Icc a b ⊆ (Set.univ : Set L) := by
  sorry







theorem theorem_881774_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (x y : X) (h : x ≠ y) :
  ∃ f : X →L[𝕜] 𝕜, f x ≠ f y := by
  sorry



theorem theorem_882200_problem
  (d : ℕ) [NeZero d]
  (K : ℝ) (hK : 0 < K)
  (f : (Fin d → ℝ) → ℝ)
  (hf_cont : Continuous f)
  (hf_supp : HasCompactSupport f)
  (hf_supp_in : tsupport f ⊆ Set.pi Set.univ (fun _ => Set.Ioo (-K) K))
  (f_tilde : (Fin d → ℝ) → ℝ)
  (h_def : ∀ (x : Fin d → ℝ) (z : Fin d → ℤ),
    x ∈ Set.pi Set.univ (fun _ => Set.Ico (-K) K) →
    f_tilde (x + (fun i => 2 * K * (z i : ℝ))) = f x) :
  Continuous f_tilde := by
  sorry



theorem theorem_881357_problem (G : Type*) [Group G] (A : Set G)
  (h_gen : Subgroup.closure A = ⊤)
  (h_inf : Set.Infinite A) :
  Cardinal.mk A = Cardinal.mk G := by
  sorry











theorem theorem_882288_problem (α β γ : ℝ) (h : α < β) : 
  α + γ < β + γ := by
  sorry

theorem theorem_882587_problem
  (n : ℕ)
  (a b : Fin n → ℝ)
  (k : ℝ)
  (hn : 0 < n)
  (ha : ∀ i, 0 < a i)
  (hb : ∀ i, 0 < b i)
  (hk : 2 < k) :
  ∑ i, (a i) ^ k / (b i) ≥ (∑ i, a i) ^ k / ((n : ℝ) ^ (k - 2) * ∑ i, b i) := by
  sorry

theorem theorem_882169_problem
  (f : ℕ → ℝ → ℝ)
  (I : ℕ → ℝ)
  (h_f : ∀ n x, f n x = if 1 - x^2 / (2 * (n : ℝ)) ≥ 0 then (1 - x^2 / (2 * (n : ℝ))) ^ n else 0)
  (h_I : ∀ n, I n = ∫ x, f n x) :
  Filter.Tendsto I Filter.atTop (nhds (Real.sqrt (2 * Real.pi))) := by
  sorry







theorem theorem_882955_problem
  (E F : Type*)
  [Fintype E] [Fintype F]
  (hE_ne : Nonempty E)
  (hF_ne : Nonempty F)
  (σE : MeasurableSpace E)
  (σF : MeasurableSpace F)
  (hσE : σE = ⊤)
  (hσF : σF = ⊤) :
  @MeasurableSpace.prod E F σE σF = ⊤ := by
  sorry







theorem theorem_882869_problem (Q_plus : Set ℚ) (h : Q_plus = {q : ℚ | 0 < q}) :
  Set.Countable Q_plus := by
  sorry

theorem theorem_882816_problem
  (r : ℝ → (Fin 3 → ℝ))
  (v : ℝ → (Fin 3 → ℝ))
  (F : ℝ → (Fin 3 → ℝ))
  (f : ℝ → ℝ)
  (h_diff : ContDiff ℝ 2 r)
  (hv : v = deriv r)
  (h_force : ∀ t, F t = (f ‖r t‖) • r t)
  (h_motion : ∀ t, deriv v t = F t) :
  ∀ t, deriv (fun t ↦ crossProduct (r t) (v t)) t = 0 := by
  sorry







theorem theorem_883407_problem (r ω : ℝ) (hr : r > 0)
  (G : ℂ) (hG : G = 2 / (1 + Complex.I * ↑r * ↑ω) ^ 4) :
  Complex.arg G = -4 * Real.arctan (r * ω) := by
  sorry

theorem theorem_883104_problem (f : ℂ → ℂ)
  (hf : Differentiable ℂ f)
  (h : ∀ z, f (f z) ≠ z) :
  ∃ b : ℂ, b ≠ 0 ∧ ∀ z, f z = z + b := by
  sorry







theorem theorem_883787_problem
  (k : ℕ)
  (t : ℝ → ℝ)
  (f : ℕ → ℝ)
  (K : ℝ)
  (h_def : ∀ n, f n = t (2 ^ (2 ^ n)))
  (h_rec : ∀ n, n > 0 → f n = 1 + f (n - 1))
  (h_init : t 2 = f 0)
  (h_K : K = 2 ^ (2 ^ k)) :
  f k = Real.logb 2 (Real.logb 2 K) + t 2 := by
  sorry

theorem theorem_883616_problem (x' : ℝ) :
  let L : (ℝ → ℝ) → (ℝ → ℝ) := fun f x ↦ - (deriv (deriv f) x)
  let G : ℝ → ℝ := fun x ↦ - |x - x'| / 2
  ∀ φ : ℝ → ℝ, ContDiff ℝ ⊤ φ → HasCompactSupport φ →
  ∫ x, G x * (L φ x) = φ x' := by
  sorry

theorem theorem_884176_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (A B : (V →ₗ[K] V) → Prop)
  (S_A S_B : Set (V →ₗ[K] V))
  (hSA : S_A = { T | A T })
  (hSB : S_B = { T | B T })
  (h : ∀ T, A T → B T) :
  S_A ⊆ S_B := by
  sorry

theorem theorem_884066_problem (x : ℝ) (hx : x > 0) :
  Complex.exp (Complex.I * (Real.log x)) = 
  (Real.cos (Real.log x) : ℂ) + Complex.I * (Real.sin (Real.log x)) := by
  sorry





theorem theorem_883510_problem
  (A : Type*) [CommRing A]
  (P Q : Ideal A) [hP : P.IsPrime] [hQ : Q.IsPrime]
  (hPQ : P ≤ Q)
  -- The problem statement assumes the localization of A_Q at PA_Q exists,
  -- which implies PA_Q is a prime ideal in A_Q.
  [hP_ext_prime : (P.map (algebraMap A (Localization.AtPrime Q))).IsPrime] :
  Nonempty (Localization.AtPrime P ≃+* Localization.AtPrime (P.map (algebraMap A (Localization.AtPrime Q)))) := by
  sorry





theorem theorem_884162_problem (f : ℝ × ℝ → ℝ)
  (h : ∀ x y, f (x, y) = (x^3 + 3 * x^2 * y + 7 * y^3) / (2 * x^2 + 5 * y^2)) :
  Filter.Tendsto f (nhdsWithin 0 {p | p ≠ 0}) (nhds 0) := by
  sorry







theorem theorem_884491_problem (A : Type*) [AddCommGroup A]
  (h : Module.Free ℤ (A ⧸ AddCommGroup.torsion A)) :
  Nonempty (A ≃+ (AddCommGroup.torsion A) × (A ⧸ AddCommGroup.torsion A)) := by
  sorry



theorem theorem_884943_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (J : E → ℝ) (u v : E)
  (hJ : ContDiff ℝ 1 J) :
  J v - J u = ∫ t in (0 : ℝ)..1, (fderiv ℝ J (u + t • (v - u))) (v - u) := by
  sorry





theorem theorem_884829_problem (m n r : ℕ) :
  IsClosed {A : Matrix (Fin m) (Fin n) ℝ | A.rank ≤ r} := by
  sorry

theorem theorem_885031_problem
  (n k : ℕ)
  (p : ℝ)
  (I : ℝ → ℝ → ℝ → ℝ)
  (hk : 1 ≤ k)
  (hkn : k ≤ n)
  (hp : 0 < p ∧ p < 1)
  (hI_symm : ∀ x a b, 0 < x → x < 1 → I x a b = 1 - I (1 - x) b a)
  (P_X_le : ℝ := I (1 - p) (n - k + 1) k)
  (P_F_le : ℝ → ℝ := fun x ↦
    let m : ℝ := 2 * k
    let n_deg : ℝ := 2 * (n - k + 1)
    I ((m * x) / (m * x + n_deg)) (m / 2) (n_deg / 2)) :
  let val := ((n - k + 1) : ℝ) / k * (p / (1 - p))
  P_X_le = 1 - P_F_le val := by
  sorry



theorem theorem_884816_problem (a b : ℝ) :
  Real.sin a + Real.sin b = 2 * Real.sin ((a + b) / 2) * Real.cos ((a - b) / 2) := by
  sorry

theorem theorem_884562_problem :
  ∃ (f : ℝ → ℝ) (a : ℝ),
    HasDerivWithinAt f 0 (Set.Ioi a) a ∧
    ¬ (∃ ε > 0, ∀ x, a < x ∧ x < a + ε → f x = f a) := by
  sorry

theorem theorem_885102_problem (A B N x y : ℝ) 
  (r theta : ℝ)
  (h_r : r = Real.sqrt (x ^ 2 + y ^ 2))
  (h_theta : theta = Real.arctan (y / x))
  (h_eq : Real.exp (A / r) = B * Real.tan (theta / (2 * N))) :
  Real.exp (A / Real.sqrt (x ^ 2 + y ^ 2)) = B * Real.tan (Real.arctan (y / x) / (2 * N)) := by
  sorry

theorem theorem_885151_problem
  (a b : ℝ)
  (F : ℝ → ℝ → ℝ)
  (h_meas : Measurable (Function.uncurry F))
  (h_sym : ∀ x, ∀ᵐ y ∂volume, F x y = F x (-y))
  (h_indep : ∀ x₁ x₂, ∀ᵐ y ∂volume, F x₁ y = F x₂ y)
  (h_int : ∀ x, IntervalIntegrable (fun y ↦ F x y * y) volume a b) :
  ∃ G : ℝ → ℝ, ∀ x, ∫ y in a..b, F x y * y = ∫ y in a..b, G y * y := by
  sorry







theorem theorem_885530_problem (B : Prop) (h : ¬B → False) : B := by
  sorry

theorem theorem_885411_problem (I : Set ℝ) (hI_open : IsOpen I) (hI_conn : IsConnected I)
  (h_domain : ∀ x ∈ I, Real.sin (2 * x) ≠ 0)
  (y : ℝ → ℝ) (hy_diff : ContDiffOn ℝ 2 y I)
  (h_ode : ∀ x ∈ I, deriv (deriv y) x + 4 * y x = 3 / Real.sin (2 * x)) :
  ∃ c₁ c₂ : ℝ, ∀ x ∈ I, y x = c₁ * Real.cos (2 * x) + c₂ * Real.sin (2 * x) -
    (3 / 2) * x * Real.cos (2 * x) + (3 / 4) * Real.sin (2 * x) * Real.log (abs (Real.sin (2 * x))) := by
  sorry

theorem theorem_885456_problem
  (g : ℂ → ℂ)
  (h_bij : Function.Bijective g)
  (h_holo : Differentiable ℂ g)
  (h_inv_holo : Differentiable ℂ (Function.invFun g)) :
  ∀ z w : ℂ, w = g z ↔ z = Function.invFun g w := by
  sorry











theorem theorem_885400_problem :
  ∃ (R : Type) (_ : LinearOrderedRing R), ∃ (a : ℕ → R), ∀ n, a (n + 1) < a n := by
  sorry







theorem theorem_885970_problem
  (n : ℕ)
  (hn : n > 0)
  (x : Fin n → ℝ)
  (hx_pos : ∀ i, x i > 0)
  (hx_rat : ∀ i, ∃ q : ℚ, x i = q)
  (m : ℕ)
  (hm_pos : m > 0)
  (hm_int : ∀ i, ∃ k : ℤ, m * x i = k)
  (hm_min : ∀ k : ℕ, k > 0 → (∀ i, ∃ j : ℤ, k * x i = j) → m ≤ k)
  (d : ℕ)
  (hd : d = Finset.gcd Finset.univ (fun i => Int.natAbs (Int.floor (m * x i)))) :
  let h := (d : ℝ) / m
  (∀ i, ∃ k : ℤ, x i = k * h) ∧
  (∀ h' : ℝ, h' > 0 → (∀ i, ∃ k : ℤ, x i = k * h') → h' ≤ h) := by
  sorry









theorem theorem_886350_problem
  {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
  (B : Matrix m n ℝ)
  (C : Matrix p n ℝ)
  (h_rank : C.rank = 3)
  (h_inv : Invertible (C.transpose * C)) :
  let A := B * ⅟(C.transpose * C) * C.transpose
  A * C = B := by
  sorry

theorem theorem_886577_problem 
  (n : ℕ) 
  (k : ℝ) 
  (A : Matrix (Fin n) (Fin n) ℝ)
  (h_inv : Invertible A)
  (h_sum : ∀ i, ∑ j, A i j = k)
  (hk : k ≠ 0) :
  ∀ i, ∑ j, (A⁻¹) i j = 1 / k := by
  sorry





theorem theorem_885659_problem (a b c d e : ℕ)
  (h : a + b + e + 1 ≤ c + d + 1) :
  ∑ k in Finset.range (c + d - b - a + 1),
    (Nat.choose (k + a) a) * (Nat.choose (c - a - k) b) * (Nat.choose (d + k) e) =
  Nat.choose (c + d + 1) (a + b + e + 1) := by
  sorry

theorem theorem_887053_problem {G : Type*} [Group G]
  (h : IsCyclic (G ⧸ Subgroup.center G)) :
  ∀ a b : G, a * b = b * a := by
  sorry





theorem theorem_886138_problem
  (n k : ℕ)
  (P_X : ℕ → ℝ)
  (p : Fin k → ℝ)
  (b : Fin k → ℕ)
  (hn : 1 ≤ n)
  (hp_sum : ∑ i, p i = 1)
  (hp_nonneg : ∀ i, 0 ≤ p i)
  (hb_sum : 1 ≤ ∑ i, b i ∧ ∑ i, b i ≤ n) :
  (∑ m in Finset.Icc 1 n, P_X m * 
    if ∑ i, b i = m then 
      ((m.factorial : ℝ) / (∏ i, ((b i).factorial : ℝ))) * (∏ i, (p i) ^ (b i))
    else 0) = 
  P_X (∑ i, b i) * ((∑ i, b i).factorial : ℝ) / (∏ i, ((b i).factorial : ℝ)) * (∏ i, (p i) ^ (b i)) := by
  sorry















theorem theorem_887883_problem
  (a b s m n : ℤ)
  (x : ℕ)
  (hx : 0 < x)
  (h1 : a ^ x ≡ s [ZMOD n])
  (h2 : b ^ x ≡ s [ZMOD m]) :
  (a * b) ^ x ≡ s * (a ^ x + b ^ x - s) [ZMOD m * n] := by
  sorry

theorem theorem_887118_problem :
  let f := fun x : ℝ => Real.log (1 + Real.tan x)
  (iteratedDeriv 0 f 0) / (Nat.factorial 0 : ℝ) = 0 ∧
  (iteratedDeriv 1 f 0) / (Nat.factorial 1 : ℝ) = 1 ∧
  (iteratedDeriv 2 f 0) / (Nat.factorial 2 : ℝ) = -1/2 ∧
  (iteratedDeriv 3 f 0) / (Nat.factorial 3 : ℝ) = 2/3 ∧
  (iteratedDeriv 4 f 0) / (Nat.factorial 4 : ℝ) = -7/12 ∧
  (iteratedDeriv 5 f 0) / (Nat.factorial 5 : ℝ) = 2/3 ∧
  (iteratedDeriv 6 f 0) / (Nat.factorial 6 : ℝ) = -31/45 ∧
  (iteratedDeriv 7 f 0) / (Nat.factorial 7 : ℝ) = 244/315 := by
  sorry

