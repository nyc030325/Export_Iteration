import Mathlib
import Mathlib.Tactic







theorem theorem_999424_problem
  (T₁ T₂ : ℝ × ℝ → ℝ × ℝ)
  (hT₁ : ∀ x y : ℝ, T₁ (x, y) = (x, 0))
  (hT₂ : ∀ x y : ℝ, T₂ (x, y) = (0, y)) :
  ¬ ∃ U₁ : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ), T₁ = T₂ ∘ U₁ := by
  sorry



theorem theorem_999347_problem :
  (∀ x y : ℝ, x^2 - 1 ≤ 0 → -y ≤ 0 → y - 2 ≤ 0 → x^2 + y^2 ≤ 5) ∧
  (∃ x y : ℝ, x^2 - 1 ≤ 0 ∧ -y ≤ 0 ∧ y - 2 ≤ 0 ∧ x^2 + y^2 = 5) := by
  sorry





theorem theorem_999091_problem
  (n : ℕ)
  (S Q R Q' R' : Matrix (Fin n) (Fin n) ℝ)
  (hS_inv : IsUnit S)
  (hQR : S = Q * R)
  (hQR' : S = Q' * R')
  (hQ_orth : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ)
  (hQ'_orth : Q' ∈ Matrix.orthogonalGroup (Fin n) ℝ)
  (hR_ut : ∀ i j, i > j → R i j = 0)
  (hR'_ut : ∀ i j, i > j → R' i j = 0)
  (hR_pos : ∀ i, 0 < R i i)
  (hR'_pos : ∀ i, 0 < R' i i) :
  Q = Q' ∧ R = R' := by
  sorry

theorem theorem_999158_problem (a : ℕ → ℝ)
  (h : Summable (fun n ↦ (a (n + 1)) ^ 2)) :
  Summable (fun n ↦ a (n + 1) / (n + 1 : ℝ)) := by
  sorry



theorem theorem_999578_problem
  (F : Type*) [Field F]
  (V : Type*) [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (W : Submodule F V) :
  ∃ T : Module.Dual F (V ⧸ W) ≃ₗ[F] W.dualAnnihilator,
    ∀ (ψ : Module.Dual F (V ⧸ W)) (v : V),
      (T ψ).1 v = ψ (Submodule.mkQ W v) := by
  sorry

theorem theorem_999622_problem
  {R : Type*} [Field R]
  (A₁₁ A₁₂ A₂₁ A₂₂ : Matrix (Fin 3) (Fin 3) R)
  (A P : Matrix (Sum (Fin 3) (Fin 3)) (Sum (Fin 3) (Fin 3)) R)
  (hA : A = Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)
  (hP : P = Matrix.fromBlocks 0 1 1 0) :
  P⁻¹ * A * P = Matrix.fromBlocks A₂₂ A₂₁ A₁₂ A₁₁ := by
  sorry



theorem theorem_999951_problem
  (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
  (x₀ : X) (y₀ : Y) :
  Nonempty (FundamentalGroup (X × Y) (x₀, y₀) ≃* FundamentalGroup X x₀ × FundamentalGroup Y y₀) := by
  sorry

theorem theorem_999595_problem (a : ℕ → ℝ)
  (h : ∀ n, a n = 1 / (3 * (n : ℝ) + 2 * Real.cos n)) :
  ¬ Summable a := by
  sorry



theorem theorem_999989_problem (f θ : ℝ → ℝ)
  (hf : ContDiff ℝ 2 f)
  (hθ : Differentiable ℝ θ)
  (h_cos : ∀ t, Real.cos (θ t) = -(deriv f t) / Real.sqrt ((deriv f t)^2 + 1))
  (h_sin : ∀ t, Real.sin (θ t) = 1 / Real.sqrt ((deriv f t)^2 + 1)) :
  ∀ t, deriv θ t = (deriv (deriv f) t) / ((deriv f t)^2 + 1) := by
  sorry







theorem theorem_1000094_problem (a : ℝ) (h : 0 < a) :
  ∫ x : ℝ, 1 / (x^2 + a^2) = π / a := by
  sorry

theorem theorem_1000201_problem {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (U : Submodule F V) (u₁ u₂ : V) (h₁ : u₁ ∈ U) (h₂ : u₂ ∈ U) :
  u₂ - u₁ ∈ U := by
  sorry







theorem theorem_999845_problem
  {E F : Type*}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  (X : Set E) (Y : Set F)
  (hX_ne : X.Nonempty) (hY_ne : Y.Nonempty)
  (hX_cp : IsCompact X) (hX_cv : Convex ℝ X)
  (hY_cv : Convex ℝ Y)
  (f : E → F → ℝ)
  (h1 : ∀ x ∈ X, LowerSemicontinuousOn (fun y ↦ f x y) Y ∧ ConvexOn ℝ Y (fun y ↦ f x y))
  (h2 : ∀ y ∈ Y, UpperSemicontinuousOn (fun x ↦ f x y) X ∧ ConcaveOn ℝ X (fun x ↦ f x y)) :
  (⨆ x ∈ X, ⨅ y ∈ Y, f x y) = (⨅ y ∈ Y, ⨆ x ∈ X, f x y) := by
  sorry

theorem theorem_1000488_problem (a b : ℝ) (hab : a ≤ b) (S : Set (Set ℝ))
  (h_cover : Set.Icc a b ⊆ ⋃₀ S)
  (h_shape : ∀ I ∈ S, (∃ c d, I = Set.Ioo c d) ∨
                      (∃ c d, I = Set.Ico c d) ∨
                      (∃ c d, I = Set.Ioc c d) ∨
                      (I = Set.Icc a b)) :
  ∃ S', S' ⊆ S ∧ S'.Finite ∧ Set.Icc a b ⊆ ⋃₀ S' := by
  sorry



theorem theorem_1000192_problem
  (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
  (h_int : Algebra.IsIntegral A B)
  (q : Ideal B) [q.IsPrime]
  (h_inter : Ideal.comap (algebraMap A B) q = ⊥) :
  q = ⊥ := by
  sorry





theorem theorem_1001254_problem
  {Sx Sf Ω : Type*}
  (P : (Ω → Prop) → ℝ)
  (X : ℕ → Ω → Sx)
  (PX : Sx → Sx → ℝ)
  (f : Sx ≃ Sf)
  (h_markov : ∀ (t : ℕ) (i j : Sx), P (λ ω ↦ X t ω = i) ≠ 0 →
    P (λ ω ↦ X (t + 1) ω = j ∧ X t ω = i) / P (λ ω ↦ X t ω = i) = PX i j) :
  ∀ (t : ℕ) (u v : Sf), P (λ ω ↦ f (X t ω) = u) ≠ 0 →
    P (λ ω ↦ f (X (t + 1) ω) = v ∧ f (X t ω) = u) / P (λ ω ↦ f (X t ω) = u) =
    PX (f.symm u) (f.symm v) := by
  sorry

theorem theorem_1000759_problem (x : ℝ) (h : |x| < 1) :
  HasDerivAt (fun t => Real.arctan (t^3)) (3 * x^2 * ∑' n : ℕ, (-x^6)^n) x := by
  sorry



theorem theorem_1000188_problem 
  (H : ℕ → ℕ → ℕ → ℕ)
  (h0 : ∀ a b, H 0 a b = b + 1)
  (h1 : ∀ a, H 1 a 0 = a)
  (h2 : ∀ a, H 2 a 0 = 0)
  (h3 : ∀ n a, n ≥ 3 → H n a 0 = 1)
  (h_rec : ∀ n a b, n > 0 → b > 0 → H n a b = H (n - 1) a (H n a (b - 1))) :
  (∀ a b, H 1 a b = a + b) ∧ 
  (∀ a b, H 2 a b = a * b) ∧ 
  (∀ a b, H 3 a b = a ^ b) := by
  sorry

theorem theorem_1000706_problem (n : ℝ) (hn : 0 < n) :
  ¬ (fun x => x * (Real.exp (x / n) - Real.exp ((x - 1) / n))) =O[Filter.atTop] 
    (fun x => Real.exp ((x - 1) / n)) := by
  sorry

theorem theorem_1000816_problem
  (n m : ℕ)
  (i j : Fin m → ℕ)
  (hn : n ≥ 2)
  (h_div : (X ^ n - 1 : Polynomial ℤ) ∣ ∑ k : Fin m, (X ^ (j k) * (X ^ (i k) - 1))) :
  n ∣ ∑ k : Fin m, i k := by
  sorry





theorem theorem_1001628_problem
  {M : Type*} [AddGroup M]
  (Z : M × M → M)
  (h : ∀ x₁ y₁ x₂ y₂ : M, x₁ + y₁ = x₂ + y₂ → Z (x₁, y₁) - Z (x₂, y₂) = 0) :
  ∀ x₁ y₁ x₂ y₂ : M, x₁ + y₁ = x₂ + y₂ → Z (x₁, y₁) = Z (x₂, y₂) := by
  sorry





theorem theorem_1000981_problem (x : ℝ) (n : ℕ) (hn : n > 0) :
  ∑ i in Finset.range n, ⌈x - (i : ℝ) / n⌉ = ⌈n * x⌉ := by
  sorry

theorem theorem_1002046_problem {U : Type*} (mem : U → U → Prop) (S : U)
  (h_ind : (∃ u, mem u S ∧ ∀ z, ¬ mem z u) ∧
           (∀ x, mem x S → ∃ v, mem v S ∧ ∀ w, mem w v ↔ mem w x ∨ w = x)) :
  ∃ u, mem u S ∧ ∀ z, ¬ mem z u := by
  sorry



theorem theorem_1002005_problem 
  (H : ℕ → ℝ → ℝ → ℝ)
  (h1 : ∀ a b, H 1 a b = a + b)
  (h2 : ∀ a b, H 2 a b = a * b)
  (h3 : ∀ a b, H 3 a b = a ^ b)
  (h_rec : ∀ n, n ≥ 3 → ∀ a b, H (n + 1) a b = H n a (H (n + 1) a (b - 1)))
  (HasNontrivialFunctionalEquation : (ℝ → ℝ → ℝ) → Prop) :
  ∀ n, n > 3 → ¬ HasNontrivialFunctionalEquation (H n) := by
  sorry

theorem theorem_1001551_problem (n : ℤ) (k : ℤ) (hn : n ≥ 2) :
  let ζ : ℂ := Complex.exp ((2 * ↑Real.pi * Complex.I) / ↑n)
  1 - ζ ^ k = 2 * Complex.sin ((↑Real.pi * ↑k) / ↑n) * 
    Complex.exp (-(↑Real.pi * Complex.I) / 2 + (↑Real.pi * Complex.I * ↑k) / ↑n) := by
  sorry





theorem theorem_1002353_problem (n : ℕ) (C : Set (Fin n → ℝ))
  (hC_compact : IsCompact C) (hC_nonempty : C.Nonempty)
  (f : C → ℝ) (hf_cont : Continuous f) :
  ∃ x_star : C, ∀ x : C, f x ≤ f x_star := by
  sorry

theorem theorem_1002219_problem (d : ℕ) (x : ℕ → (Fin d → ℝ))
  (h_bound : ∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) :
  ∃ (y : Fin d → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ Filter.Tendsto (x ∘ φ) Filter.atTop (nhds y) := by
  sorry

theorem theorem_1002254_problem
  (y : ℝ → ℝ)
  (A : ℝ → ℝ → ℝ → ℝ → ℝ)
  (A_1 A_2 A_3 A_4 : ℝ → ℝ → ℝ → ℝ → ℝ)
  (x : ℝ)
  (hy : ContDiff ℝ 3 y)
  (hA : ContDiff ℝ 1 (fun v : ℝ × ℝ × ℝ × ℝ => A v.1 v.2.1 v.2.2.1 v.2.2.2))
  (hA1 : ∀ a b c d, A_1 a b c d = deriv (fun t => A t b c d) a)
  (hA2 : ∀ a b c d, A_2 a b c d = deriv (fun t => A a t c d) b)
  (hA3 : ∀ a b c d, A_3 a b c d = deriv (fun t => A a b t d) c)
  (hA4 : ∀ a b c d, A_4 a b c d = deriv (fun t => A a b c t) d)
  (h_const : deriv (fun t => A t (y t) (deriv y t) (deriv^[2] y t)) x = 0)
  (h_denom : A_4 x (y x) (deriv y x) (deriv^[2] y x) ≠ 0) :
  deriv^[3] y x = - (A_1 x (y x) (deriv y x) (deriv^[2] y x) + 
                     A_2 x (y x) (deriv y x) (deriv^[2] y x) * deriv y x + 
                     A_3 x (y x) (deriv y x) (deriv^[2] y x) * deriv^[2] y x) / 
                     A_4 x (y x) (deriv y x) (deriv^[2] y x) := by
  sorry

theorem theorem_1002571_problem (p : ℕ) (hp : p.Prime) (h : p % 3 = 2) :
  Function.Bijective (fun (x : ZMod p) => x ^ 3) := by
  sorry





theorem theorem_1002326_problem (f g : ℝ → ℝ) (k : ℝ)
  (h1 : Filter.Tendsto f Filter.atTop (nhds 1))
  (h2 : Filter.Tendsto g Filter.atTop Filter.atTop)
  (h3 : Filter.Tendsto (fun x => (f x - 1) * g x) Filter.atTop (nhds k)) :
  Filter.Tendsto (fun x => f x ^ g x) Filter.atTop (nhds (Real.exp k)) := by
  sorry

theorem theorem_1002899_problem (a b : ℝ) (f : ℝ → ℝ)
  (h : ContinuousOn f (Set.Icc a b)) :
  ∃ m M : ℝ, ∀ x ∈ Set.Icc a b, m ≤ f x ∧ f x ≤ M := by
  sorry

theorem theorem_1002520_problem
  (a b : ℝ) (f g : ℝ → ℝ)
  (hab : a < b)
  (hf_cont : ContinuousOn f (Set.Icc a b))
  (hg_cont : ContinuousOn g (Set.Icc a b))
  (hf_diff : DifferentiableOn ℝ f (Set.Ioo a b))
  (hg_diff : DifferentiableOn ℝ g (Set.Ioo a b))
  (hg_deriv : ∀ x ∈ Set.Ioo a b, deriv g x ≠ 0) :
  ∃ c ∈ Set.Ioo a b, (deriv f c) / (deriv g c) = (f b - f a) / (g b - g a) := by
  sorry



theorem theorem_1003082_problem (n : ℕ) :
  ∑ k in Finset.range (n + 1), (Nat.choose n k) * k = n * 2 ^ (n - 1) := by
  sorry







theorem theorem_1002831_problem (L1 L2 theta2 theta3 : ℝ)
  (xp1 L4 : ℝ)
  (h1 : xp1 = L1 * Real.cos theta2)
  (h2 : L4 - xp1 = L2 * Real.sin theta3) :
  L4 = L1 * Real.cos theta2 + L2 * Real.sin theta3 := by
  sorry

theorem theorem_1002958_problem (x y z : ℕ)
  (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (h : (x * y : ℝ) / z + (x * z : ℝ) / y + (y * z : ℝ) / x = 3) :
  x = 1 ∧ y = 1 ∧ z = 1 := by
  sorry





theorem theorem_1003360_problem (a b : ℝ) (f g : ℝ → ℝ)
  (h_le : a ≤ b)
  (h_inv_le : Function.invFun g a ≤ Function.invFun g b)
  (hf : ContinuousOn f (Set.Icc a b))
  (hg_diff : ContDiffOn ℝ 1 g (Set.Icc (Function.invFun g a) (Function.invFun g b)))
  (hg_inj : Function.Injective g)
  (hg_map : Set.MapsTo g (Set.Icc (Function.invFun g a) (Function.invFun g b)) (Set.Icc a b))
  (ha_rg : a ∈ Set.range g)
  (hb_rg : b ∈ Set.range g) :
  ∫ x in a..b, f x = ∫ t in (Function.invFun g a)..(Function.invFun g b), f (g t) * deriv g t := by
  sorry

theorem theorem_1003541_problem (K L : Type*) [Field K] [Field L] [Algebra K L]
  (f g : Polynomial K) (h : IsCoprime f g) :
  IsCoprime (f.map (algebraMap K L)) (g.map (algebraMap K L)) := by
  sorry

theorem theorem_1003348_problem (x y z : ℝ) :
  (x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ Real.sqrt x + Real.sqrt y + Real.sqrt z ≤ 1) ↔
  (0 ≤ x ∧ x ≤ 1 ∧
   0 ≤ y ∧ y ≤ (1 - Real.sqrt x) ^ 2 ∧
   0 ≤ z ∧ z ≤ (1 - Real.sqrt x - Real.sqrt y) ^ 2) := by
  sorry

theorem theorem_1003167_problem
  {α : Type*}
  (mem : α → α → Prop)
  (is_finite : α → Prop)
  (B : α)
  (h_inf : ¬ is_finite B)
  (h_def : ∀ x, mem x B ↔ is_finite x) :
  ¬ mem B B := by
  sorry

theorem theorem_1003154_problem
  (α : ℝ) (hα : Irrational α)
  (a b : ℝ) (ha : 0 ≤ a ∧ a < 1) (hb : 0 ≤ b ∧ b < 1) (hab : a ≠ b)
  (δ : ℝ) (hδ : 0 < δ) :
  ∃ s : Finset ℕ,
    let I := fun n ↦
      let u := Int.fract (a + n * α)
      let v := Int.fract (b + n * α)
      if u ≤ v then Set.Icc u v else Set.Ico u 1 ∪ Set.Icc 0 v
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (I i) (I j)) ∧
    (MeasureTheory.volume (⋃ i ∈ s, I i)).toReal > 1 - δ := by
  sorry

theorem theorem_1003204_problem (x : ℝ) :
  Filter.Tendsto (fun ε => Real.sin x / Real.sqrt ((Real.sin x)^2 + ε^2))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sign (Real.sin x))) := by
  sorry

theorem theorem_1003931_problem (j k : ℤ) (f : ℤ → ℝ) (h : k = 1) :
  ∏ i in Finset.Icc (j + 1) (j + k - 1), f i = 1 := by
  sorry

theorem theorem_1003997_problem
  (X Y : Type*)
  [MetricSpace X] [MetricSpace Y]
  [CompleteSpace X] [CompleteSpace Y] :
  CompleteSpace (X × Y) := by
  sorry

theorem theorem_1003972_problem (n : ℕ) (a b : ℝ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (γ : ℝ → EuclideanSpace ℝ (Fin n))
  (hf : Differentiable ℝ f)
  (hγ : ContDiff ℝ ⊤ γ) :
  ∫ t in a..b, inner (gradient f (γ t)) (deriv γ t) = f (γ b) - f (γ a) := by
  sorry







theorem theorem_1003877_problem (a : ℝ) (y : ℝ → ℝ)
  (ha : a ≠ 0)
  (hy : ContDiff ℝ 2 y)
  (h_ode : ∀ x, a * (deriv (deriv y) x) + deriv (fun t => t^3 * y t) x = 0)
  (h_cond : ∀ x, a * deriv y x + x^3 * y x = 0) :
  ∃ C : ℝ, ∀ x, y x = C * Real.exp (-(x^4) / (4 * a)) := by
  sorry

theorem theorem_1003776_problem
  (F A X Y : Type*)
  [Field F] [Ring A] [Algebra F A]
  [AddCommGroup X] [Module A X]
  [Module F X] [IsScalarTower F A X]
  [AddCommGroup Y] [Module A Y]
  [Module F Y] [IsScalarTower F A Y]
  (φ : X →ₗ[F] Y) :
  IsLinearMap A φ ↔ ∀ (a : A) (v : X), φ (a • v) = a • φ v := by
  sorry

theorem theorem_1004052_problem
  (a b : ℝ) (n : ℕ) (f : ℝ → ℂ) (ω_n : ℝ)
  (h_n : n ≥ 2)
  (Δ : ℝ) (hΔ : Δ = (b - a) / n)
  (t : ℕ → ℝ) (ht : ∀ k, t k = a + k * Δ)
  (θ : ℝ) (hθ : θ = ω_n * Δ)
  (approx : ℂ → ℂ → Prop) :
  ∃ (W : ℝ → ℂ) (α : ℕ → ℝ → ℂ),
    approx
      (∫ x in a..b, f x * Complex.exp (Complex.I * ↑ω_n * ↑x))
      (↑Δ * Complex.exp (Complex.I * ↑ω_n * ↑a) *
        (W θ * (∑ k in Finset.range (n + 1), f (t k) * Complex.exp (Complex.I * ↑k * ↑θ)) +
         α 0 θ * f (t 0) + α 1 θ * f (t 1) +
         Complex.exp (Complex.I * ↑ω_n * (↑b - ↑a)) * (α (n - 2) θ * f (t (n - 2)) + α (n - 1) θ * f (t (n - 1))))) := by
  sorry



theorem theorem_1003891_problem (R : Type*) [CommRing R] (I : Ideal R)
  (g : (↥I ⧸ (Submodule.comap (Submodule.subtype I) (I ^ 3))) →ₗ[R] (R ⧸ I))
  (h : ∀ x, x ≠ 0 → g x = 0) :
  ∀ x, g x = 0 := by
  sorry



theorem theorem_1003992_problem (G : Type*) [Group G] [Finite G]
  (p q a b : ℕ)
  (hp : p.Prime)
  (hq : q.Prime)
  (hpq : p ≠ q)
  (ha : 1 ≤ a)
  (hb : 1 ≤ b)
  (hG : Nat.card G = p ^ a * q ^ b) :
  ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  sorry











theorem theorem_1004601_problem {α : Type*} (B : ℕ → Set α) 
  (h : ∀ i, (B i).Countable) : 
  (⋃ i, B i).Countable := by
  sorry

theorem theorem_1004698_problem (ε : ℝ) (hε : 0 < ε) :
  Filter.Tendsto (fun x ↦ Real.log x / x ^ ε) Filter.atTop (nhds 0) := by
  sorry

theorem theorem_1004870_problem (K : Type*) [LinearOrderedField K]
  (h_complete : ∀ (s : Set K), s.Nonempty → BddAbove s → ∃ x, IsLUB s x) :
  Nonempty (K ≃+*o Real) := by
  sorry

theorem theorem_1004385_problem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
  (h : ∀ X : Matrix (Fin n) (Fin n) ℝ,
    (∃ p q : Fin n, p ≤ q ∧ X = Matrix.stdBasisMatrix p q 1) → A * X = X * A) :
  ∃ s : ℝ, A = s • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  sorry

theorem theorem_1004300_problem
  (E T E_hat T_hat : Type*)
  [TopologicalSpace E] [TopologicalSpace T]
  [TopologicalSpace E_hat] [TopologicalSpace T_hat]
  (πE : E_hat → E) (πT : T_hat → T)
  (hπE : IsCoveringMap πE)
  (hπT : IsCoveringMap πT)
  (h_card_E : ∀ x : E, Set.ncard (πE ⁻¹' {x}) = 2)
  (h_card_T : ∀ x : T, Set.ncard (πT ⁻¹' {x}) = 2)
  (Φ : T_hat ≃ₜ E_hat)
  (hΦ : ∀ t : T, ∃ e : E, Φ '' (πT ⁻¹' {t}) = πE ⁻¹' {e}) :
  ∃ ψ : T ≃ₜ E, ψ ∘ πT = πE ∘ Φ := by
  sorry



theorem theorem_1004885_problem
  (a b c : ℝ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h_pyth : a^2 + b^2 = c^2)
  (A B C : ℝ)
  (hA : A = (Real.sqrt 3 / 4) * a^2)
  (hB : B = a * b / 2)
  (hC : C = Real.sqrt (((a + 2 * c) / 2) * (((a + 2 * c) / 2) - a) * (((a + 2 * c) / 2) - c)^2)) :
  A^2 + B^2 = C^2 := by
  sorry

theorem theorem_1004641_problem (a b r : ℝ)
  (hb : 0 < b)
  (hab : b < a)
  (h_intrinsic : deriv (fun x ↦ (a * x) / (b + x)) 0 = 1 + r) :
  r = a / b - 1 := by
  sorry

