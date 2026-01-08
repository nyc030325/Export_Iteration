import Mathlib
import Mathlib.Tactic

theorem theorem_760642_problem
  (k : Type*) [Field k]
  (n : ℕ)
  (p : Fin n → MvPolynomial (Fin n) k)
  (h_nz : ∀ i, p i ≠ 0)
  (h_dim : Module.Finite k (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range p))) :
  Set.Finite {x : Fin n → k | ∀ i, MvPolynomial.eval x (p i) = 0} := by
  sorry

theorem theorem_760229_problem
  (S : Type*) [Fintype S]
  (s : Setoid S)
  (n : ℕ)
  (classes : Fin n → Quotient s)
  (h_classes : Function.Bijective classes) :
  ∃ f : Quotient s ≃ Fin n,
    ∀ (i j : Fin n), f (classes i) < f (classes j) ↔ i < j := by
  sorry

theorem theorem_760547_problem :
  Real.pi = 16 * Real.arctan (1 / 5) - 4 * Real.arctan (1 / 239) := by
  sorry

theorem theorem_760634_problem (A : Set (ℝ × ℝ))
  (hA : A = {p : ℝ × ℝ | p.2 ≤ p.1}) :
  ¬ ∃ (X Y : Set ℝ), A = X ×ˢ Y := by
  sorry

theorem theorem_761309_problem
  {A B C : Type*} [Group A] [Group B] [Group C]
  (f : A →* B) (g : B →* C)
  (h_surj : Function.Surjective g)
  (h_ker_eq_img : g.ker = f.range) :
  Nonempty (C ≃* B ⧸ g.ker) := by
  sorry

theorem theorem_761428_problem (x₁ x₂ t : ℝ)
  (hx₁ : 0 < x₁)
  (hx₂ : 0 < x₂)
  (ht : 0 < t ∧ t < 1) :
  -t * Real.log x₁ - (1 - t) * Real.log x₂ ≥ -Real.log (t * x₁ + (1 - t) * x₂) := by
  sorry

theorem theorem_760926_problem : P = 1 - 1 / u3 := by
  sorry



theorem theorem_760359_problem : Language.IsContextFree L := by
  sorry

theorem theorem_760583_problem (a : ℝ) :
  (∃ x y : ℝ, x ≠ y ∧ (∀ z : ℝ, Real.exp (z ^ 2) = a * z ↔ z = x ∨ z = y)) ↔
  abs a > Real.sqrt 2 * Real.exp (1 / 2) := by
  sorry

theorem theorem_761197_problem
  {X Y : Type*} [Fintype X] [Fintype Y]
  (q : Y → X → ℝ) (r : X → Y → ℝ)
  (hq_pos : ∀ y x, 0 < q y x)
  (hq_sum : ∀ y, ∑ x, q y x = 1)
  (hr_pos : ∀ x y, 0 < r x y)
  (hr_sum : ∀ x, ∑ y, r x y = 1) :
  (∃ p : X → Y → ℝ,
    (∀ x y, 0 < p x y) ∧
    (∑ x, ∑ y, p x y) = 1 ∧
    (∀ x y, q y x = p x y / (∑ x', p x' y)) ∧
    (∀ x y, r x y = p x y / (∑ y', p x y'))) ↔
  (∃ (f : X → ℝ) (g : Y → ℝ), ∀ x y, q y x / r x y = f x * g y) := by
  sorry

theorem theorem_761366_problem (f : ℝ → ℝ) (h_diff : Differentiable ℝ f)
  (x a b : ℝ)
  (g : ℝ → ℝ) (hg : ∀ y, g y = f (x + a * y)) :
  deriv g b = a * deriv f (x + a * b) := by
  sorry





theorem theorem_760807_problem
  (F E : Type*) [Field F] [Fintype F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (m : ℕ) (hm : FiniteDimensional.finrank F E = m)
  (α : Basis (Fin m) F E) :
  ∃ φ : E ≃ₗ[F] (Fin m → F),
    ∀ (β : E) (i : Fin m),
      algebraMap F E (φ β i) = ∑ k : Fin m, (α i * β) ^ ((Fintype.card F) ^ (k : ℕ)) := by
  sorry

theorem theorem_761183_problem (a b : ℝ) (hab : a < b) (f : ℝ → ℝ)
  (hf : ContDiff ℝ ⊤ f) :
  ∫ x in a..b, deriv f x = f b - f a := by
  sorry

theorem theorem_762192_problem
  {α I : Type*}
  (A : I → Set α)
  (h_nonempty : ∀ i, (A i).Nonempty)
  (h_disjoint : Pairwise (Disjoint on A))
  (h_infinite : Infinite I) :
  ∃ f : I → α, ∀ i, f i ∈ A i := by
  sorry









theorem theorem_761614_problem
  (f g : ℝ → ℝ)
  (p : ℝ)
  (h1 : ∀ s, HasDerivAt f (g s) s)
  (h2 : ∀ s, HasDerivAt g (-p^2 * (f s - 1)) s) :
  ∃ C : ℝ, ∀ s, (p * (f s - 1))^2 + (g s)^2 = C := by
  sorry



theorem theorem_761350_problem (x : ℝ) :
  HasDerivAt (fun x => Real.log (abs (Real.exp (-x) + 1)) - Real.exp (-x))
    (1 / (Real.exp x + Real.exp (2 * x))) x := by
  sorry

theorem theorem_761867_problem (g : ℂ → ℂ) :
  Function.Surjective g ↔ ∀ c : ℂ, ∃ z : ℂ, g z = c := by
  sorry

theorem theorem_761773_problem :
  ∃ (X : Type) (t₁ t₂ : TopologicalSpace X) (K : Set X),
    t₁ ≤ t₂ ∧ @IsCompact X t₁ K ∧ ¬ @IsCompact X t₂ K := by
  sorry





theorem theorem_761947_problem (α β δ : ℝ) :
  -- Define the coefficients of the SDE for Y_t as given in the problem
  let drift_Y (y : ℝ) := α - β * y
  let diff_Y (y : ℝ) := δ

  -- Define the transformation relating V_t and Y_t
  let f (y : ℝ) := y ^ 2

  -- Define the target coefficients of the SDE for V_t as claimed in the problem
  let drift_V_target (v : ℝ) := δ^2 + 2 * α * Real.sqrt v - 2 * β * v
  let diff_V_target (v : ℝ) := 2 * δ * Real.sqrt v

  -- The theorem asserts that applying Ito's Lemma to Y yields the claimed SDE for V
  -- We consider the domain y ≥ 0 consistent with y = √v
  ∀ y : ℝ, 0 ≤ y →
    let v := f y
    -- Calculate drift and diffusion for V using the standard Ito formula:
    -- μ_V = f'(y)μ_Y + 1/2 f''(y)σ_Y^2
    let drift_V_calc := (deriv f y) * (drift_Y y) + (1/2 : ℝ) * (deriv (deriv f) y) * (diff_Y y)^2
    -- σ_V = f'(y)σ_Y
    let diff_V_calc := (deriv f y) * (diff_Y y)
    
    -- Conclusion: The calculated coefficients match the target coefficients
    drift_V_calc = drift_V_target v ∧ diff_V_calc = diff_V_target v := by
  sorry

theorem theorem_761976_problem (x y p : ℝ)
  (hx : x > 0) (hy : y > 0)
  (hp_pos : 0 < p) (hp_lt_1 : p < 1) :
  |x ^ (1 / p) - y ^ (1 / p)| ^ p ≥ |x - y| := by
  sorry



theorem theorem_762380_problem
  (V : Type*)
  (E : V → V → Prop)
  (s t : V)
  (k : ℕ) :
  (∃ p : List V, p.length ≤ k + 1 ∧ p.Chain' E ∧ p.head? = some s ∧ p.getLast? = some t) ↔
  (∃ j, j ≤ k ∧ Relation.ReflTransGen
    (fun (u v : V × ℕ) => u.2 < k ∧ v.2 = u.2 + 1 ∧ E u.1 v.1)
    (s, 0) (t, j)) := by
  sorry





theorem theorem_761809_problem 
  (G X Y : Type*) 
  [Group G] 
  [MulAction G X] 
  [Fintype X] 
  [Fintype Y] 
  (n m : ℕ)
  (ϕ : X → Y)
  (h_trans : MulAction.IsPretransitive G X)
  (h_surj : Function.Surjective ϕ)
  (hn : Fintype.card X = n)
  (hm : Fintype.card Y = m)
  (h_neq : n ≠ m) :
  ¬ ∃ (act : MulAction G Y), ∀ (g : G) (x : X), ϕ (g • x) = @SMul.smul _ _ act.toSMul g (ϕ x) := by
  sorry



theorem theorem_762762_problem (j k n : ℕ) (h1 : j ≤ k) (h2 : k ≤ n) :
  ∑ m in Finset.range (n + 1), Nat.choose m j * Nat.choose (n - m) (k - j) = Nat.choose (n + 1) (k + 1) := by
  sorry



theorem theorem_762870_problem
  {R : Type*} [CommRing R]
  (n : ℤ)
  (x h1 h2 : ℤ → R)
  (K L : Finset ℤ) :
  ∑ k in K, ∑ l in L, x l * h1 (n - k - l) * h2 k =
  ∑ l in L, x l * ∑ k in K, h1 (n - k - l) * h2 k := by
  sorry

theorem theorem_763254_problem
  (f : ℝ → ℝ)
  (u : ℝ → ℝ → ℝ)
  (h1 : ∀ x y : ℝ, deriv (fun t => u t y) x + deriv (fun t => u x t) y = 1)
  (h2 : ∀ x : ℝ, u x 0 = f x) :
  ∀ x y : ℝ, u x y = y + f (x - y) := by
  sorry





theorem theorem_763279_problem (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X]
  (F : Set X) (hF : IsClosed F) :
  LocallyCompactSpace F := by
  sorry

theorem theorem_762770_problem (k : ℕ) (hk : k ≥ 1) :
  Set.ncard {n : ℕ | round (Real.sqrt (2 * (n : ℝ))) = (k : ℤ)} = k := by
  sorry



theorem theorem_763260_problem
  {V : Type*}
  (G : SimpleGraph V)
  (S : Set V)
  (H : SimpleGraph V)
  -- H is the induced subgraph. We define its adjacency explicitly to allow comparing the path list directly.
  (hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ u ∈ S ∧ v ∈ S)
  (p : List V)
  -- p is a path in G (Chain of adjacency and No duplicates)
  (hp_G : p.Chain' G.Adj)
  (hp_nodup : p.Nodup)
  -- p is preserved in H (all vertices are in the sampled set S)
  (h_preserved : ∀ v ∈ p, v ∈ S) :
  -- Conclusion: p is a valid path in H (retains same order/structure)
  p.Chain' H.Adj ∧ p.Nodup := by
  sorry

theorem theorem_763174_problem (h k a b c d e x y : ℝ) :
  ((x - h)^2 / a^2 - (y - k)^2 / b^2 - 1) * (y - c * (x - d)^2 - e) = 0 ↔
  ((x - h)^2 / a^2 - (y - k)^2 / b^2 = 1) ∨ (y = c * (x - d)^2 + e) := by
  sorry

theorem theorem_762982_problem (S : Set ℕ) :
  (∃ E : ℕ →. ℕ, Partrec E ∧ S = {k | ∃ n, k ∈ E n}) ↔
  (∃ M : ℕ →. ℕ, Partrec M ∧ S = {n | (M n).Dom}) := by
  sorry





theorem theorem_763818_problem 
  (G : Type*) [Group G] 
  (V₁ V₂ : Type*) [MulAction G V₁] 
  (E : Set V₁) (hE : ∃ x : V₁, E = MulAction.orbit G x) 
  (B : Set (V₁ × V₂)) (hB : B = E ×ˢ (Set.univ : Set V₂)) :
  ∀ (g : G) (b : V₁ × V₂), b ∈ B → (g • b.1, b.2) ∈ B := by
  sorry











theorem theorem_763500_problem (n : ℕ) :
  let S1 := {z : ℂ // Complex.abs z = 1}
  let Sn := {w : Fin (n + 1) → ℂ // ‖w‖ = 1}
  let P := S1 × Sn
  ∃ (s : Setoid P),
    (∀ x y : P, s.r x y ↔ x = y ∨ (x.1.val = -y.1.val ∧ x.2.val = -y.2.val)) ∧
    Nonempty (Quotient s ≃ₜ P) := by
  sorry

theorem theorem_763753_problem (f g : ℕ → ℝ)
  (hf : ∀ n, f n = 3 ^ ((n : ℝ) ^ 3))
  (hg : ∀ n, g n = 7 ^ (2 * (n : ℝ) + (n : ℝ) * Real.logb 3 n)) :
  Filter.Tendsto (fun n => Real.log (f n) / Real.log (g n)) Filter.atTop Filter.atTop := by
  sorry

theorem theorem_763836_problem (x y : ℚ) (q p r : ℤ)
  (hx : x = (q : ℚ) / (r : ℚ))
  (hy : y = (p : ℚ) / (r : ℚ))
  (h1 : Int.gcd q r = 1)
  (h2 : Int.gcd p r = 1) :
  x^2 + y^2 ≠ 3 := by
  sorry









theorem theorem_763599_problem
  (U : Set (ℝ × ℝ))
  (hU : IsOpen U)
  (f : ℝ × ℝ → ℝ)
  -- Condition: First-order partial derivatives exist on U
  (h_fx_exist : ∀ p ∈ U, DifferentiableAt ℝ (fun x ↦ f (x, p.2)) p.1)
  (h_fy_exist : ∀ p ∈ U, DifferentiableAt ℝ (fun y ↦ f (p.1, y)) p.2)
  -- Condition: First-order partial derivatives are continuous on U
  (h_fx_cont : ContinuousOn (fun p ↦ deriv (fun x ↦ f (x, p.2)) p.1) U)
  (h_fy_cont : ContinuousOn (fun p ↦ deriv (fun y ↦ f (p.1, y)) p.2) U)
  -- Condition: Second-order mixed partial derivatives exist on U
  (h_fxy_exist : ∀ p ∈ U, DifferentiableAt ℝ (fun y ↦ deriv (fun x ↦ f (x, y)) p.1) p.2)
  (h_fyx_exist : ∀ p ∈ U, DifferentiableAt ℝ (fun x ↦ deriv (fun y ↦ f (x, y)) p.2) p.1) :
  -- Conclusion: The mixed partial derivatives are equal
  ∀ p ∈ U, deriv (fun y ↦ deriv (fun x ↦ f (x, y)) p.1) p.2 = 
           deriv (fun x ↦ deriv (fun y ↦ f (x, y)) p.2) p.1 := by
  sorry

theorem theorem_763413_problem (m n : ℕ)
  (hm : m > 0)
  (hn : n = 2 * m + 1)
  (A B : Polynomial ℤ)
  (hA : A = ∑ k in Finset.Icc 1 m, X ^ (2 * k))
  (hB : B = ∑ k in Finset.Icc 1 m, X ^ (2 * k - 1)) :
  (A * B).coeff n = m := by
  sorry





theorem theorem_764091_problem (z : ℂ) (d : ℕ) :
  Complex.abs (Complex.exp z - ∑ j in Finset.range d, z ^ j / (j.factorial : ℂ)) ≤ 
  (Complex.abs z ^ d / (d.factorial : ℝ)) * max 1 (Real.exp z.re) := by
  sorry

theorem theorem_764471_problem
  {F : Type*} [Field F]
  {S : Type*}
  {V : Type*} [AddCommGroup V] [Module F V]
  {W : Type*} [AddCommGroup W] [Module F W]
  (b : Basis S F V)
  (f : S → W) :
  ∃! T : V →ₗ[F] W, ∀ s : S, T (b s) = f s := by
  sorry

















theorem theorem_764108_problem (x z : ℝ) (Φ : ℝ → ℝ)
  (hΦ : ∀ w, HasDerivAt Φ ((1 / Real.sqrt (2 * Real.pi)) * Real.exp (- w^2 / 2)) w)
  (hx : x > 0) :
  HasDerivAt (fun z => Φ (z / x)) 
    ((1 / (|x| * Real.sqrt (2 * Real.pi))) * Real.exp (- z^2 / (2 * x^2))) z := by
  sorry





theorem theorem_764791_problem (u_r u_l : ℝ) (f : ℝ → ℝ)
  (h_ord : u_r < u_l)
  (h_cvx : StrictConvexOn ℝ (Set.Icc u_r u_l) f)
  (h_diff : ∀ x ∈ Set.Icc u_r u_l, DifferentiableAt ℝ f x) :
  deriv f u_r < (f u_l - f u_r) / (u_l - u_r) ∧
  (f u_l - f u_r) / (u_l - u_r) < deriv f u_l := by
  sorry







theorem theorem_764839_problem 
  (ComplexManifold : Type → Prop)
  (HolomorphicVectorBundle : ∀ {M : Type}, ComplexManifold M → Type → Prop)
  (Subbundle : ∀ {M E : Type} {hM : ComplexManifold M}, HolomorphicVectorBundle hM E → Type)
  (IsHolomorphicSubbundle : ∀ {M E : Type} {hM : ComplexManifold M} {hE : HolomorphicVectorBundle hM E}, 
    Subbundle hE → Prop)
  (HermitianMetric : ∀ {M E : Type} {hM : ComplexManifold M}, HolomorphicVectorBundle hM E → Type)
  (OrthogonalComplement : ∀ {M E : Type} {hM : ComplexManifold M} {hE : HolomorphicVectorBundle hM E} 
    (F : Subbundle hE), HermitianMetric hE → Subbundle hE) :
  ¬ (∀ (M E : Type) (hM : ComplexManifold M) (hE : HolomorphicVectorBundle hM E) 
       (F : Subbundle hE) (hF : IsHolomorphicSubbundle F) (h : HermitianMetric hE),
     IsHolomorphicSubbundle (OrthogonalComplement F h)) := by
  sorry



theorem theorem_765029_problem
  (X : Type u) [TopologicalSpace X]
  (Y : Type u) [TopologicalSpace Y]
  (r : Setoid X)
  (q : X → Y)
  (hq_cont : Continuous q)
  (hq_resp : ∀ x y, r.Rel x y → q x = q y)
  (h_univ : ∀ (Z : Type u) [TopologicalSpace Z] (f : X → Z),
    Continuous f → (∀ x y, r.Rel x y → f x = f y) →
    ∃! g : Y → Z, Continuous g ∧ g ∘ q = f) :
  Nonempty (Quotient r ≃ₜ Y) := by
  sorry

theorem theorem_765237_problem
  (H : ℕ → Type*)
  [∀ n, AddCommGroup (H n)]
  (cup : ∀ {n m : ℕ}, H n → H m → H (n + m))
  (n : ℕ)
  (eta : H n)
  (h_coboundary : cup eta eta = 0) :
  cup eta eta = 0 := by
  sorry

theorem theorem_765388_problem {A B : Type*} (f : A → B) (B' B'' : Set B)
  (h : B' ⊆ B'') : f ⁻¹' B' ⊆ f ⁻¹' B'' := by
  sorry

theorem theorem_764675_problem (a b : ℝ) (f g : ℝ → ℝ)
  (hab : a < b)
  (hf_cont : ContinuousOn f (Set.Icc a b))
  (hg_cont : ContinuousOn g (Set.Icc a b))
  (hf_diff : DifferentiableOn ℝ f (Set.Ioo a b))
  (hg_diff : DifferentiableOn ℝ g (Set.Ioo a b)) :
  ∃ c ∈ Set.Ioo a b, deriv f c * (g b - g a) = deriv g c * (f b - f a) := by
  sorry

theorem theorem_765661_problem (f : ℝ → ℝ)
  (h1 : Differentiable ℝ f)
  (h2 : Differentiable ℝ (deriv f)) :
  deriv (fun t => deriv f t + f t) = deriv (deriv f) + deriv f := by
  sorry



theorem theorem_764272_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (u v : ℝ → E)
  (I : Set ℝ)
  (t₀ : ℝ)
  (hI : IsOpen I)
  (ht₀ : t₀ ∈ I)
  (hu_diff : DifferentiableOn ℝ u I)
  (hv_diff : DifferentiableOn ℝ v I)
  (hu_nz : ∀ t ∈ I, u t ≠ 0)
  (hv_nz : ∀ t ∈ I, v t ≠ 0)
  (theta : ℝ → ℝ)
  (h_theta_def : ∀ t ∈ I, theta t = InnerProductGeometry.angle (u t) (v t))
  (h_parallel : ∃ c : ℝ, u t₀ = c • v t₀) :
  ¬ DifferentiableAt ℝ theta t₀ := by
  sorry

theorem theorem_765655_problem (V : Set ℝ)
  (h : ∀ x : ℝ, ∃! v ∈ V, ∃ q : ℚ, x = v + (q : ℝ)) :
  ¬ MeasureTheory.NullMeasurableSet V MeasureTheory.volume := by
  sorry











theorem theorem_765462_problem
  (n : ℕ) (w : ℕ → ℝ) (b : ℝ)
  (hn : n ≥ 1)
  (hb : ∀ m : ℕ, m ≥ 1 → b ^ m ≠ 1)
  (h_recurrence : ∀ i : ℕ, 1 ≤ i ∧ i ≤ n → b ^ (i - 1) * w i = w 1)
  (h_loop : w 1 = b ^ n * w 1) :
  ∀ i : ℕ, 1 ≤ i ∧ i ≤ n → w i = 0 := by
  sorry

