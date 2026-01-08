import Mathlib
import Mathlib.Tactic



theorem theorem_616695_problem (x y : ℕ) (hx : x > 0) (hy : y > 0)
  (h : x ≡ y [MOD 20]) :
  x ^ x ≡ y ^ y [MOD 10] := by
  sorry



theorem theorem_617074_problem (m n : ℕ) 
  (f : (Fin m → ℝ) ≃ₜ (Fin n → ℝ)) : 
  m = n := by
  sorry



theorem theorem_617400_problem
  (γ₁ γ₂ : ℝ → (Fin 2 → ℝ))
  (t₁ t₂ : ℝ)
  (hγ₁ : ContDiff ℝ ⊤ γ₁)
  (hγ₂ : ContDiff ℝ ⊤ γ₂)
  (h_inter : γ₁ t₁ = γ₂ t₂) :
  (Submodule.span ℝ {deriv γ₁ t₁} ⊔ Submodule.span ℝ {deriv γ₂ t₂} = ⊤) ↔
  LinearIndependent ℝ ![deriv γ₁ t₁, deriv γ₂ t₂] := by
  sorry



theorem theorem_617033_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (U : Set E) (f : E → ℝ)
  (hU_conv : Convex ℝ U)
  (hU_open : IsOpen U)
  (hf_diff : DifferentiableOn ℝ f U)
  (hf_bound : ∃ M, ∀ z ∈ U, ‖fderiv ℝ f z‖ ≤ M)
  (x y : E) (hx : x ∈ U) (hy : y ∈ U) :
  ∃ c ∈ segment ℝ x y, f y - f x = fderiv ℝ f c (y - x) := by
  sorry







theorem theorem_617449_problem {G : Type*} [AddCommGroup G] [Module.Free ℤ G]
  (x₁ : G) (hx₁ : x₁ ≠ 0) (n : ℤ) (hn : n • x₁ = 0) :
  n = 0 := by
  sorry

theorem theorem_618033_problem
  {X M : Type*} [TopologicalSpace X] [AddCommGroup M] [TopologicalSpace M] [TopologicalAddGroup M]
  (n : ℕ) (f : Fin (n + 1) → X → M)
  (h_sum : Continuous (fun x => ∑ i, f i x))
  (h_others : ∀ i : Fin (n + 1), i ≠ 0 → Continuous (f i)) :
  Continuous (f 0) := by
  sorry





theorem theorem_618008_problem 
  (α : Type) 
  (Predicative : (α → Prop) → Prop) 
  (ϕ : α → Prop) : 
  ∃ ψ : α → Prop, Predicative ψ ∧ (∀ x, ϕ x ↔ ψ x) := by
  sorry







theorem theorem_618032_problem
  (n : ℕ)
  (x₀ v₀ a : Fin n → ℝ)
  (x : Fin n → ℝ → ℝ)
  (h_def : ∀ i : Fin n, ∀ t : ℝ, x i t = x₀ i + v₀ i * t + (1 / 2 : ℝ) * a i * t^2)
  (k : Fin n)
  (h_min : ∀ j : Fin n, j ≠ k → |a k| < |a j|) :
  ∃ T : ℝ, ∀ t : ℝ, t > T → ∀ j : Fin n, j ≠ k → |x k t| < |x j t| := by
  sorry

theorem theorem_618307_problem
  {G : Type*} [Group G] [Fintype G]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ G V)
  (avg_inner : V → V → ℂ)
  (h_avg : ∀ x y, avg_inner x y = (1 / (Fintype.card G : ℂ)) * ∑ g : G, inner (ρ g x) (ρ g y)) :
  ∀ (h : G) (x y : V), avg_inner (ρ h x) (ρ h y) = avg_inner x y := by
  sorry









theorem theorem_618091_problem :
  ∃ (A : Type) (P1 P2 : PMF (A × A × A)),
    P1.map (fun ⟨x, y, z⟩ ↦ (x, y)) = P2.map (fun ⟨x, y, z⟩ ↦ (x, y)) ∧
    P1.map (fun ⟨x, y, z⟩ ↦ (x, z)) = P2.map (fun ⟨x, y, z⟩ ↦ (x, z)) ∧
    P1.map (fun ⟨x, y, z⟩ ↦ (y, z)) = P2.map (fun ⟨x, y, z⟩ ↦ (y, z)) ∧
    P1 ≠ P2 := by
  sorry

theorem theorem_618224_problem (C : ℝ) :
  Asymptotics.IsBigO Filter.atTop
    (fun (x : ℝ) => ∏ p in (Finset.range (Nat.floor x + 1)).filter Nat.Prime,
      (1 + 4 / (3 * (p : ℝ)) + C / ((p : ℝ) ^ ((3 : ℝ) / 2))))
    (fun (x : ℝ) => (Real.log x) ^ ((4 : ℝ) / 3)) := by
  sorry

theorem theorem_618203_problem (f : Set ℕ → Set ℕ)
  (h : ∀ A : Set ℕ, (f A).Finite) :
  ¬ Function.Surjective f := by
  sorry





theorem theorem_618848_problem (a b : ℝ) :
  ∫ x in a..b, |Real.sin x| = ∫ x in a..b, Real.sqrt ((Real.sin x)^2) := by
  sorry

theorem theorem_618683_problem
  {F : Type*} [Field F]
  (ϕ : Polynomial ℂ →+* F)
  (hϕ : Function.Injective ϕ)
  (ψ : RatFunc ℂ →+* F)
  (hψ : ∀ p : Polynomial ℂ, ψ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = ϕ p) :
  Function.Injective ψ := by
  sorry



theorem theorem_618446_problem
  (D2 : Set (ℝ × ℝ))
  (hD2 : D2 = {p | p.1^2 + p.2^2 ≤ 1})
  (S1 : Set (ℝ × ℝ))
  (hS1 : S1 = {p | p.1^2 + p.2^2 = 1})
  (S2 : Set (ℝ × ℝ × ℝ))
  (hS2 : S2 = {p | p.1^2 + p.2.1^2 + p.2.2^2 = 1})
  (r : D2 → D2 → Prop)
  (hr : r = fun x y ↦ x = y ∨ (x.1 ∈ S1 ∧ y.1 ∈ S1))
  (s : Setoid D2)
  (hs : s.r = r) :
  Nonempty (Quotient s ≃ₜ S2) := by
  sorry













theorem theorem_618621_problem
  (Y : ℕ → ℤ → ℝ → ℝ → ℝ) :
  ∃ C : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℝ,
    ∀ (l1 l2 : ℕ) (m1 m2 : ℤ) (θ φ : ℝ),
      |m1| ≤ (l1 : ℤ) → |m2| ≤ (l2 : ℤ) →
      Y l1 m1 θ φ * Y l2 m2 θ φ =
      ∑ l in Finset.Icc (Nat.dist l1 l2) (l1 + l2),
        ∑ m in Finset.Icc (-(l : ℤ)) (l : ℤ),
          C l1 l2 l m1 m2 m * Y l m θ φ := by
  sorry



theorem theorem_618978_problem (u : ℝ → ℝ → ℝ)
  -- u is differentiable in both variables
  (h_diff_x : ∀ t ≥ 0, Differentiable ℝ (fun x ↦ u x t))
  (h_diff_t : ∀ x ≥ 0, Differentiable ℝ (fun t ↦ u x t))
  -- The PDE holds: u_t + u_x = 0
  (h_pde : ∀ x ≥ 0, ∀ t ≥ 0, deriv (fun s ↦ u x s) t + deriv (fun s ↦ u s t) x = 0)
  -- Boundary conditions from the problem statement
  -- u(0, x) = 0 implies condition on the x=0 boundary (if x is 2nd arg here) or just literal transcription
  (h_cond1 : ∀ x ≥ 0, u 0 x = 0)
  -- u(t, 0) = 0 implies condition on the t=0 boundary (initial condition)
  (h_cond2 : ∀ t ≥ 0, u t 0 = 0) :
  -- Conclusion
  ∀ x ≥ 0, ∀ t ≥ 0, u x t = 0 := by
  sorry





theorem theorem_618721_problem (p k : ℕ) (hp : Nat.Prime p) (hk : k > 1)
  (f : Polynomial (ZMod (p ^ k)))
  (h_monic : f.Monic)
  (h_irred_mod_p : Irreducible (Polynomial.map (ZMod.castHom (dvd_pow_self p (by linarith)) (ZMod p)) f)) :
  Irreducible f := by
  sorry

theorem theorem_619265_problem (G : Type*) [Group G] (hG : Nontrivial G)
  (f : G → ℤ)
  (h_deg : ∀ g h : G, f (g * h) = f g * f h)
  (h_range : ∀ g : G, f g = 1 ∨ f g = -1)
  (h_cond : ∀ g : G, g ≠ 1 → f g = -1) :
  Nonempty (G ≃* Multiplicative (ZMod 2)) := by
  sorry



theorem theorem_618882_problem (p : Polynomial ℝ)
  (h : ∫ x in (0 : ℝ)..1, p.eval x = 0) :
  ∃ c ∈ Set.Ioo 0 1, p.eval c = 0 := by
  sorry



theorem theorem_619888_problem
  (k : Type*) [Field k]
  (V W : Type*) [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [FiniteDimensional k V] [FiniteDimensional k W]
  (n : ℕ) (h : FiniteDimensional.finrank k V = n)
  (T : V →ₗ[k] W) :
  FiniteDimensional.finrank k (LinearMap.range (LinearMap.dualMap T)) ≤ n := by
  sorry

theorem theorem_619709_problem
  (X Z Y : Type*)
  [tX : TopologicalSpace X]
  [tZ : TopologicalSpace Z]
  (f : Y ↪ X)
  (g : Y ↪ Z)
  (h_ne : Nonempty Y)
  (h_top_eq : TopologicalSpace.induced f tX = TopologicalSpace.induced g tZ)
  (h_connected : @ConnectedSpace Y (TopologicalSpace.induced f tX)) :
  @ConnectedSpace Y (TopologicalSpace.induced g tZ) := by
  sorry







theorem theorem_619995_problem (X : Type*) (E : Set X) :
  {x : X | Set.indicator E (fun _ ↦ (1 : ℝ)) x < 1/2} = Eᶜ := by
  sorry





theorem theorem_619877_problem
  (a b : Fin 3 → ℝ)
  (ε : Fin 3 → Fin 3 → Fin 3 → ℝ)
  (T_sigma_i : Fin 3 → Fin 3 → ℝ)
  (T_j_alpha : Fin 3 → Fin 3 → ℝ) :
  (fun σ => ∑ i : Fin 3, T_sigma_i σ i *
    (∑ j : Fin 3, ∑ k : Fin 3, ε i j k *
      (∑ α : Fin 3, T_j_alpha j α * a α) *
      (∑ β : Fin 3, T_j_alpha k β * b β))) =
  (fun σ => ∑ α : Fin 3, ∑ β : Fin 3,
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ε i j k * T_sigma_i σ i * T_j_alpha j α * T_j_alpha k β) *
    a α * b β) := by
  sorry





theorem theorem_620271_problem (x : ℝ)
  (h : ∀ a : ℝ, a > 0 → |x| < a) :
  x = 0 := by
  sorry



theorem theorem_620373_problem (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  sorry

theorem theorem_619942_problem (p : ℝ) (h : 1 < p) :
  Summable (fun k : ℕ => 1 / ((k + 16 : ℝ) * Real.log (k + 16) * (Real.log (Real.log (k + 16))) ^ p)) ↔ 1 < p := by
  sorry





theorem theorem_619675_problem
  (n : ℕ)
  (d : ℕ → ℕ → ℝ)
  (t : ℕ → ℝ)
  (h_d00_pos : d 0 0 > 0) :
  let S := (∑ i in Finset.Icc 1 n, d i 0 * t i) / d 0 0
  let numerator := ∫ x : ℝ, x * Real.exp (- (d 0 0 / 2) * (x + S) ^ 2)
  let denominator := ∫ x : ℝ, Real.exp (- (d 0 0 / 2) * (x + S) ^ 2)
  numerator / denominator = - ∑ i in Finset.Icc 1 n, (d i 0 / d 0 0) * t i := by
  sorry











theorem theorem_620485_problem
  (Y : Type*) [Fintype Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y] :
  let X := ℤ → Y
  let T : Equiv.Perm X :=
    { toFun := fun x i ↦ x (i + 1)
      invFun := fun x i ↦ x (i - 1)
      left_inv := by intro x; ext i; simp
      right_inv := by intro x; ext i; simp }
  let A : MeasurableSpace X := MeasurableSpace.comap (fun x ↦ x 0) inferInstance
  let B : MeasurableSpace X := inferInstance
  (⨆ i : ℤ, MeasurableSpace.comap (T ^ i) A) = B := by
  sorry



theorem theorem_620571_problem
  (a : ℕ → ℝ) (b : ℕ → ℂ)
  (h_mono : Monotone a ∨ Antitone a)
  (h_lim : Filter.Tendsto a Filter.atTop (nhds 0))
  (h_bound : ∃ M > 0, ∀ N, Complex.abs (∑ n in Finset.range N, b n) < M) :
  Summable (fun n => (a n : ℂ) * b n) := by
  sorry

theorem theorem_619580_problem
  (k : ℕ)
  (m : Fin k → ℕ)
  (h_coprime : ∀ (i j : Fin k), i ≠ j → Nat.Coprime (m i) (m j))
  (h_gt_1 : ∀ (i : Fin k), 1 < m i)
  (ε : ℝ)
  (h_eps_pos : 0 < ε)
  (h_eps_le : ε ≤ 1 / (k : ℝ)) :
  ∃ t : ℝ, ∀ (i : Fin k), ε ≤ min (Int.fract (t / (m i : ℝ))) (1 - Int.fract (t / (m i : ℝ))) := by
  sorry





theorem theorem_620803_problem :
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
    ∃ f : ℤ → ℝ,
      (∀ k l : ℤ, |f k - f l| = |(k : ℝ) - (l : ℝ)| / n) ∧
      (∀ x : ℝ, ∃ k : ℤ, |x - f k| < ε) := by
  sorry





theorem theorem_621330_problem
  (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [LocalRing R]
  (p : R) (hp : Prime p)
  (h_unique : ∀ q : R, Prime q → Associated p q)
  (v : R → ℕ)
  (hv : ∀ r : R, r ≠ 0 → ∃ (u : Rˣ), r = u * p ^ (v r)) :
  ∀ a b : R, b ≠ 0 → ∃ q r : R, a = b * q + r ∧ (r = 0 ∨ v r < v b) := by
  sorry





theorem theorem_620902_problem
  (f : ℝ → ℝ)
  (C α β c₁ : ℝ)
  (hC : C > 0)
  (h_diff : DifferentiableOn ℝ f (Set.Ioi 0))
  (h_ineq : ∀ x ∈ Set.Ioi 0, |deriv f x| ≤ C * (f x / x))
  (h_ab : 1 < α ∧ α < β)
  (h_lim_α : Filter.Tendsto (fun x ↦ x ^ α * f x) (nhdsWithin 0 (Set.Ioi 0)) (nhds c₁))
  (hc₁ : c₁ > 0)
  (h_lim_β : Filter.Tendsto (fun x ↦ x ^ β * f x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
  ∃ γ ∈ Set.Ico α β, ∃ c > 0, Filter.Tendsto (fun x ↦ x ^ γ * f x) (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
  sorry

theorem theorem_621092_problem (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
  (a b c : V) :
  (ExteriorAlgebra.ι K a * ExteriorAlgebra.ι K b) * ExteriorAlgebra.ι K c =
  ExteriorAlgebra.ι K a * (ExteriorAlgebra.ι K b * ExteriorAlgebra.ι K c) := by
  sorry

theorem theorem_621072_problem
  (ρ : ℝ)
  (hρ : 0 ≤ ρ ∧ ρ < 1)
  (π : ℕ → ℝ)
  (h_steady : ∀ n, π n = (1 - ρ) * ρ ^ n)
  (a : ℕ → ℝ)
  (h_pasta : ∀ n, a n = π n)
  (η : ℕ → ℝ)
  (h_eta : ∀ i, i ≥ 1 → η i = a (i - 1)) :
  ∀ i, i ≥ 1 → η i = ρ ^ (i - 1) * (1 - ρ) := by
  sorry



theorem theorem_621650_problem
  (D : Type*)
  [AddCommGroup D]
  [TopologicalSpace D]
  (conv : D → D → D)
  (translate : ℝ → D → D)
  (u delta exp_neg : D)
  (h s w g : D)
  (h_assoc : ∀ f g k, conv (conv f g) k = conv f (conv g k))
  (h_def : h = u - translate 1 u)
  (s_def : s = ∑' (k : ℤ), translate (2 * (k : ℝ)) delta)
  (w_def : w = conv s h)
  (g_def : g = conv h exp_neg) :
  conv w exp_neg = conv s g := by
  sorry













theorem theorem_622038_problem
  (Var Formula : Type)
  (derives : Set Formula → Formula → Prop)
  (apply_renaming : Formula → (Var → Var) → Formula)
  (is_consistent_renaming : (Var → Var) → Formula → Prop)
  (Γ : Set Formula)
  (A : Formula)
  (σ : Var → Var)
  (h1 : derives Γ A)
  (h2 : is_consistent_renaming σ A) :
  derives Γ (apply_renaming A σ) := by
  sorry







