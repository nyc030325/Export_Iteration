import Mathlib
import Mathlib.Tactic









theorem theorem_1017414_problem :
  let z : ℂ := -Complex.exp 1
  let v1 : ℂ := 1 + Complex.I * (Real.pi : ℂ)
  let v2 : ℂ := 1 + 3 * Complex.I * (Real.pi : ℂ)
  let v3 : ℂ := 1 + 5 * Complex.I * (Real.pi : ℂ)
  Complex.exp v1 = z ∧ Complex.exp v2 = z ∧ Complex.exp v3 = z := by
  sorry



theorem theorem_1017913_problem
  (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
  (G : X × unitInterval → Y) (hG : Continuous G)
  (τ : unitInterval → unitInterval) (hτ : Continuous τ)
  (F : X × unitInterval → Y)
  (hF : F = G ∘ (Prod.map id τ)) :
  Continuous F := by
  sorry







theorem theorem_1017937_problem (p : ℝ) (h : 0 < p) :
  Summable (fun (n : ℕ+) => 1 / (n : ℝ) ^ p) ↔ 1 < p := by
  sorry

theorem theorem_1017877_problem
  {E : Type*} [AddCommGroup E] [Module ℝ E]
  (D : Set E) (hD : Convex ℝ D) (f : E → ℝ) :
  ConvexOn ℝ D f ↔
  ∀ x₁ ∈ D, ∀ x₂ ∈ D, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
    f (θ • x₁ + (1 - θ) • x₂) ≤ θ • f x₁ + (1 - θ) • f x₂ := by
  sorry







theorem theorem_1018322_problem (f : ℝ → ℝ) (M : ℝ) (y₀ : ℝ)
  (hM : M > 0)
  (hf_bound : ∀ y, |f y| < M)
  (hf_diff : ContDiff ℝ 1 f) :
  ∃ y : ℝ → ℝ, y 0 = y₀ ∧ ∀ x, HasDerivAt y (f (y x)) x := by
  sorry

theorem theorem_1018036_problem (f : ℝ → ℝ) (c : ℝ)
  (h : DifferentiableAt ℝ f c) :
  ContinuousAt f c := by
  sorry

theorem theorem_1017909_problem (k b : ℝ) (hb : b ≠ 0) (hk : k ≠ 0)
  (a₁ a₂ a₃ : ℝ)
  (h_a₁ : a₁ = Real.arctan k)
  (h_a₂ : a₂ = - k / (b * (k^2 + 1)))
  (h_a₃ : a₃ = k / (b^2 * (k^2 + 1)^2))
  (c₁ c₂ c₃ : ℝ)
  (h_rev₁ : a₁ * c₁ = 1)
  (h_rev₂ : a₁ * c₂ + a₂ * c₁^2 = 0)
  (h_rev₃ : a₁ * c₃ + 2 * a₂ * c₁ * c₂ + a₃ * c₁^3 = 0) :
  c₁ = 1 / Real.arctan k ∧
  c₂ = k / (b * (k^2 + 1) * (Real.arctan k)^3) ∧
  c₃ = (k * (2 * k - Real.arctan k)) / (b^2 * (k^2 + 1)^2 * (Real.arctan k)^5) := by
  sorry

theorem theorem_1018125_problem
  (Cn : Type*) [AddCommGroup Cn] [Module ℝ Cn] -- Representing the set of n-chains as a real vector space
  (Omegan : Type*) [AddCommGroup Omegan] [Module ℝ Omegan] -- Representing the set of n-forms as a real vector space
  (integration : Cn →ₗ[ℝ] Omegan →ₗ[ℝ] ℝ) -- Integration as a bilinear map
  (Γ : Cn) -- The chain Gamma
  (hΓ : Γ = 0) -- Condition that Gamma is the zero chain
  : ∀ ω : Omegan, integration Γ ω = 0 := by
  sorry



theorem theorem_1018602_problem
  (SyntaxL SemanticsM : Type*)
  (D : SyntaxL → SemanticsM) :
  ∀ P : SyntaxL, ∃ S : SemanticsM, D P = S := by
  sorry

theorem theorem_1018600_problem 
  (y : ℝ → ℝ) 
  (h_diff : ContDiff ℝ 2 y) 
  (h_bc0 : y 0 = 0) 
  (h_bc1 : y 1 = 1) 
  (h_min : ∀ z : ℝ → ℝ, ContDiff ℝ 2 z → z 0 = 0 → z 1 = 1 → 
    ∫ x in (0)..1, ((deriv y x)^2 + 12 * x * y x) ≤ 
    ∫ x in (0)..1, ((deriv z x)^2 + 12 * x * z x)) : 
  ∀ x ∈ Set.Icc 0 1, y x = x^3 := by
  sorry



theorem theorem_1018285_problem (m : ℕ) (r : ℝ) (h : |r| < 1/2) :
  (∑' n : ℕ, if m ≤ n then r ^ (2 * n) * (Nat.choose (2 * n) (n - m) : ℝ) else 0) =
  (1 / Real.sqrt (1 - 4 * r ^ 2)) * ((1 - Real.sqrt (1 - 4 * r ^ 2)) / (2 * r)) ^ (2 * m) := by
  sorry



theorem theorem_1018578_problem (p : ℕ) [Fact p.Prime] :
  let P : Ideal ℤ := Ideal.span {↑p}
  ∀ [P.IsPrime],
  let Z_p := Localization.AtPrime P
  let I_local : Ideal Z_p := Ideal.span {algebraMap ℤ Z_p ↑p}
  Nonempty ((Z_p ⧸ I_local) ≃+* ZMod p) := by
  sorry

theorem theorem_1018613_problem (f : ℝ → ℝ)
  (h : ∀ x, f x = (x^4 + 1) / ((x + 1) ^ ((1 : ℝ) / 3) + (x - 1) ^ ((1 : ℝ) / 3))) :
  StrictMonoOn f (Set.Ioi 2) := by
  sorry





theorem theorem_1018802_problem
  -- Definitions of the objects involved
  (LinkDiagram : Type)
  (Kh : LinkDiagram → Type)
  [∀ D, AddCommGroup (Kh D)] -- Khovanov homology has additive structure allowing for "up to sign"
  (D₀ D₀' D₁ D₁' : LinkDiagram)
  -- Condition: Diagrams related by Reidemeister moves
  (reid_related : LinkDiagram → LinkDiagram → Prop)
  (h₀ : reid_related D₀ D₀')
  (h₁ : reid_related D₁ D₁')
  -- Condition: Isomorphisms induced by Reidemeister moves
  (phi : ∀ {A B : LinkDiagram}, reid_related A B → (Kh A →+ Kh B))
  -- Condition: Maps induced by a cobordism
  -- We model the cobordism abstractly to ensure F and F' come from the *same* cobordism
  (Cobordism : Type)
  (C : Cobordism)
  (induced_map : Cobordism → ∀ (A B : LinkDiagram), (Kh A →+ Kh B))
  -- Specific instances of the maps for this problem
  (F : Kh D₀ →+ Kh D₁)
  (hF : F = induced_map C D₀ D₁)
  (F' : Kh D₀' →+ Kh D₁')
  (hF' : F' = induced_map C D₀' D₁')
  (φ₀ : Kh D₀ →+ Kh D₀')
  (hφ₀ : φ₀ = phi h₀)
  (φ₁ : Kh D₁ →+ Kh D₁')
  (hφ₁ : φ₁ = phi h₁) :
  -- Conclusion: The diagram commutes up to sign
  φ₁.comp F = F'.comp φ₀ ∨ φ₁.comp F = - (F'.comp φ₀) := by
  sorry





theorem theorem_1019018_problem (f : ℂ → ℂ) 
  (h_entire : Differentiable ℂ f) 
  (h_neq_zero : ∀ z : ℂ, f z ≠ 0) : 
  ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z : ℂ, f z = Complex.exp (g z) := by
  sorry



theorem theorem_1019515_problem {Y : Type*} [TopologicalSpace Y] 
  (K : Set Y) (hK : K ≠ ∅) : 
  (∀ U ∈ ({Set.univ} : Set (Set Y)), IsOpen U) ∧ K ⊆ ⋃₀ {Set.univ} := by
  sorry

theorem theorem_1019053_problem (R : ℝ) (q : ℚ)
  (hR : IsIntegral ℤ R)
  (hq : IsIntegral ℤ (q : ℝ)) :
  ∃ ε > 0, |R - (q : ℝ)| < ε → R = (q : ℝ) := by
  sorry

theorem theorem_1019194_problem (a b c d k x y : ℝ)
  (h_d : d = Real.sqrt (a^2 + b^2))
  (h_d_nz : d ≠ 0)
  (h_cos : Real.cos y = a / d)
  (h_sin : Real.sin y = b / d) :
  Real.sin (x + y) * (k * Real.sin (x + y) + c / d) = 1 / d * Real.sin x := by
  sorry











theorem theorem_1018979_problem (m N : ℕ) (h : m ≤ N) :
  ∑ i in Finset.range (m + 1), Nat.choose (N - i) (m - i) = Nat.choose (N + 1) m := by
  sorry





















theorem theorem_1019720_problem
  (P : ℤ → ℤ → ℝ)
  (f : ℝ → ℝ → ℝ)
  (hP_bound : ∀ n d : ℤ, n < d → P n d = 0)
  (hP_neg : ∀ n d : ℤ, d < 0 → P n d = 0)
  (hP_rec : ∀ n d : ℤ, P n d = 2 * P (n - d) d + P (n - 2 * d + 1) (d - 1) - P (n - 2 * d) d)
  (hf : ∀ t x : ℝ, f t x = ∑' (n : ℕ) (d : ℕ), P n d * t ^ d * x ^ n)
  (h_summable : ∀ t x : ℝ, Summable (fun (p : ℕ × ℕ) => P p.1 p.2 * t ^ p.2 * x ^ p.1)) :
  ∀ t x : ℝ, f t x = 2 * f (t * x) x - (1 - t * x) * f (t * x ^ 2) x := by
  sorry

theorem theorem_1020188_problem
  (A K L : Type*) [CommRing A] [IsDedekindDomain A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [Algebra.IsAlgebraic K L] [Normal K L]
  (q q' : Ideal (integralClosure A L))
  [q.IsMaximal] [q'.IsMaximal]
  (h_eq : q.comap (algebraMap A (integralClosure A L)) = q'.comap (algebraMap A (integralClosure A L))) :
  ∃ σ : L ≃ₐ[K] L, ∀ x : (integralClosure A L), x ∈ q ↔ ∃ y ∈ q', σ (x : L) = (y : L) := by
  sorry

theorem theorem_1020869_problem (n : ℕ) (hn : n ≥ 3) :
  (Nat.choose n 2) ^ 2 - (Nat.choose n 2) = 6 * (Nat.choose (n + 1) 4) := by
  sorry

theorem theorem_1021108_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  (β : Basis n F V)
  (γ : Basis m F V)
  (T : V →ₗ[F] V) :
  ∀ x : V, Matrix.mulVec (LinearMap.toMatrix β γ T) (β.equivFun x) = γ.equivFun (T x) := by
  sorry



theorem theorem_1020621_problem
  (w : ℕ → ℝ)
  (p : ℝ)
  (hp : 0 < p)
  (hw_pos : ∀ i, 0 < w i)
  (h_inf : sInf (Set.range w) = 0) :
  ¬ ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧
    ∀ (x : ℕ → ℝ), Summable (fun i => |x i| ^ p) →
      c * (∑' i, |x i| ^ p) ^ (1 / p) ≤ (∑' i, |x i| ^ p * w i) ^ (1 / p) ∧
      (∑' i, |x i| ^ p * w i) ^ (1 / p) ≤ C * (∑' i, |x i| ^ p) ^ (1 / p) := by
  sorry



theorem theorem_1020594_problem
  (r : ℤ)
  (s : Finset ℕ)
  (hs_prime : ∀ p ∈ s, Nat.Prime p)
  (a : ℕ → ℕ)
  (h : r^2 = (∏ p in s, p ^ (2 * a p) : ℤ)) :
  r = (∏ p in s, p ^ (a p) : ℤ) ∨ r = -(∏ p in s, p ^ (a p) : ℤ) := by
  sorry

theorem theorem_1020742_problem
  (I : Ideal (Polynomial ℤ))
  (hI : I = Ideal.span {X ^ 2 - X - 1, 2 * X + 1}) :
  Subsingleton ((Polynomial ℤ) ⧸ I) := by
  sorry



theorem theorem_1020975_problem
  (n k C : ℕ)
  (x : Fin n → ℕ)
  (h_bin : ∀ i, x i = 0 ∨ x i = 1)
  (h_sum : ∑ i, x i = C)
  (x' : Fin n → ℕ)
  (h_neigh : ∃ I₀ I₁ : Finset (Fin n),
    I₀.card = k ∧
    I₁.card = k ∧
    (∀ i ∈ I₀, x i = 0) ∧
    (∀ i ∈ I₁, x i = 1) ∧
    ∀ i, x' i = if i ∈ I₀ then 1 else if i ∈ I₁ then 0 else x i) :
  ∑ i, x' i = C := by
  sorry

theorem theorem_1021233_problem (a : ℕ → ℝ) 
  (h : Summable a → False) : 
  ¬ Summable a := by
  sorry



















theorem theorem_1019649_problem (n : ℕ) (hn : 2 ≤ n) :
  ¬ ∃ C : ℝ, C > 0 ∧ ∀ (A B : Matrix (Fin n) (Fin n) ℝ),
    0 ≤ (A * B).det →
    |((1 / 2 : ℝ) • (A + B)).det - Real.sqrt ((A * B).det)| ≤ C * Real.sqrt (∑ i, ∑ j, (A i j - B i j) ^ 2) := by
  sorry















theorem theorem_1021749_problem (S : Set ℕ)
  (h_nonempty : S.Nonempty)
  (h_re : ∃ f : ℕ → ℕ, Computable f ∧ S = Set.range f) :
  ∃ (n : ℕ) (P : MvPolynomial (Fin n) ℤ),
    S = { y : ℕ | ∃ x : Fin n → ℕ, MvPolynomial.eval (fun i => (x i : ℤ)) P = ↑y } := by
  sorry





theorem theorem_1021617_problem (n : ℕ) (c θ : ℝ)
  (hn : n ≥ 2) (hc : c ≠ 0)
  (h_sin : Real.sin (c * θ) ≠ 0) (h_cos : Real.cos (c * θ) ≠ 0) :
  HasDerivAt (fun x => - (Real.sin (c * x)) ^ (1 - (n : ℤ)) / (c * (n - 1 : ℝ)))
    ((Real.sin (c * θ)) ^ (-(n : ℤ)) * (Real.cos (c * θ))⁻¹ -
     (1 / c) * (Real.cos (c * θ))⁻¹ * (Real.sin (c * θ)) ^ (2 - (n : ℤ)))
    θ := by
  sorry





theorem theorem_1021865_problem
  (K : Type*) [Field K]
  (L : Subfield K)
  (n : ℕ) (hn : n > 0)
  (a : K)
  (r : K)
  (h_root : r ^ n = a)
  (h_in_L : r ∈ L) :
  ∀ k : ℕ, k < n → r ^ k ∈ L := by
  sorry

theorem theorem_1022048_problem (m : ℕ) (hm : m > 0)
  (h_prime : Nat.Prime (2^m + 1)) :
  ∃ k : ℕ, m = 2^k := by
  sorry

theorem theorem_1022337_problem (a : ℕ → ℤ)
  (h_def : ∀ n, a n = (5 : ℤ)^n + (3 : ℤ)^n - 2 * (4 : ℤ)^n)
  (n : ℕ) (hn : 2 ≤ n) :
  a n > 0 := by
  sorry

theorem theorem_1022729_problem (α : Type*) (A : Set α) : ∅ ∈ 𝒫 A := by
  sorry



theorem theorem_1022692_problem 
  {V : Type*} 
  (K : Set (Set V))
  (hK : ∀ s ∈ K, ∀ t ⊆ s, t.Nonempty → t ∈ K)
  {ι : Type*} [Finite ι] [Nonempty ι]
  (τ : ι → Set V)
  (hτ : ∀ i, τ i ∈ K) :
  (⋂ i, τ i) = ∅ ∨ (⋂ i, τ i) ∈ K := by
  sorry

theorem theorem_1023028_problem
  (I : Type*)
  (B : I → Type*)
  [∀ i, BooleanRing (B i)] :
  Nonempty (PrimeSpectrum (Π i, B i) ≃ₜ StoneCech (Σ i, PrimeSpectrum (B i))) := by
  sorry

theorem theorem_1022396_problem
  (f : ℝ → ℝ)
  (x₀ x₁ : ℝ)
  (hx₀ : x₀ ∈ Set.Icc (-1 : ℝ) 1)
  (hx₁ : x₁ ∈ Set.Icc (-1 : ℝ) 1)
  (hne : x₀ ≠ x₁)
  (hf : ContDiffOn ℝ 2 f (Set.Icc (-1) 1)) :
  let W := fun x ↦ 1 / Real.sqrt (1 - x^2)
  let π₁ := fun x ↦ ((x - x₁) / (x₀ - x₁)) * f x₀ + ((x - x₀) / (x₁ - x₀)) * f x₁
  let I := ∫ x in (-1)..1, W x * f x
  let Q := ∫ x in (-1)..1, W x * π₁ x
  let E₂ := I - Q
  let M := ⨆ x ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv 2 f x|
  |E₂| ≤ (2 * Real.pi * M) / 6 := by
  sorry



theorem theorem_1022581_problem :
  ∃ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : ℂ,
    ∀ X Y Z : ℂ,
      let E₁ := X + Y + Z
      let E₂ := X * Y + Y * Z + Z * X
      let E₃ := X * Y * Z
      ((X - Y) * (Y - Z) * (Z - X))^2 =
        c₁ * E₁^6 + c₂ * E₁^4 * E₂ + c₃ * E₁^3 * E₃ +
        c₄ * E₁^2 * E₂^2 + c₅ * E₁ * E₂ * E₃ + c₆ * E₂^3 + c₇ * E₃^2 := by
  sorry

theorem theorem_1023050_problem (G K : Type*) [Group G] [Group K] (H : Subgroup G) [H.Normal] :
  let Y := { ψ : G →* K // H ≤ ψ.ker }
  let X := G ⧸ H →* K
  let Φ : Y → X := fun ψ ↦ QuotientGroup.lift H ψ.val ψ.property
  Function.Bijective Φ := by
  sorry



