import Mathlib
import Mathlib.Tactic

theorem theorem_993393_problem
  {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (F : W → ℝ) (G : E → W) (x : E)
  (hG : DifferentiableAt ℝ G x)
  (hF : DifferentiableAt ℝ F (G x)) :
  fderiv ℝ (F ∘ G) x = (fderiv ℝ F (G x)).comp (fderiv ℝ G x) := by
  sorry



theorem theorem_993274_problem (a : ℝ) (ha : 0 < a) :
  ∫ x in (0)..Real.pi, (x * Real.sin x) / (a + (Real.cos x) ^ 2) =
  (Real.pi / Real.sqrt a) * Real.arctan (1 / Real.sqrt a) := by
  sorry

theorem theorem_993489_problem (f : ℝ → ℝ) (a b h : ℝ)
  (h_def : h = b - a)
  (T_h : ℝ)
  (h_T_h : T_h = (h / 2) * (1 * f a + 0 * f ((a + b) / 2) + 1 * f b))
  (T_h_half : ℝ)
  (h_T_h_half : T_h_half = (h / 4) * (1 * f a + 2 * f ((a + b) / 2) + 1 * f b)) :
  (4 * T_h_half - T_h) / 3 = (h / 6) * (f a + 4 * f ((a + b) / 2) + f b) := by
  sorry











theorem theorem_994017_problem
  (a b c : ℕ → ℝ)
  (L : ℝ)
  (h_lim_a : Filter.Tendsto a Filter.atTop (nhds L))
  (h_lim_b : Filter.Tendsto b Filter.atTop (nhds L))
  (h_c : ∀ n, c n = if Odd n then a n else b n) :
  Filter.Tendsto c Filter.atTop (nhds L) := by
  sorry

theorem theorem_993835_problem (n : ℕ) :
  ∑ k in Finset.range (n + 1), ((-1 : ℝ) ^ k / (2 * k + 1) * (Nat.choose n k : ℝ)) =
  (4 : ℝ) ^ n / ((2 * n + 1) * (Nat.choose (2 * n) n : ℝ)) := by
  sorry

theorem theorem_994425_problem (x : ℝ) : x^2 ≥ 0 := by
  sorry



theorem theorem_993915_problem (r b α : ℝ)
  (hr : 0 < r)
  (hb : 0 < b)
  (h_range : 0 < α ∧ α ≤ Real.pi)
  (h_geom : 2 * r * Real.sin (α / 2) = b * Real.sqrt 2) :
  α = 2 * Real.arcsin ((b * Real.sqrt 2 / 2) / r) := by
  sorry



theorem theorem_993273_problem (a b : ℤ) (h_ab : a ≤ b)
  (P : ℤ → Prop)
  (Q : ℤ → Prop)
  (hQ : ∀ n, Q n ↔ P (b - n) ∨ n > b - a)
  (h1 : P 0)
  (h2 : ∀ n, a ≤ n ∧ n < b → Q n → Q (n + 1)) :
  ∀ n, a ≤ n ∧ n ≤ b → P n := by
  sorry

theorem theorem_994126_problem (f : ℝ → ℝ) (x₀ : ℝ)
  (h : ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε) :
  ContinuousAt f x₀ := by
  sorry

theorem theorem_993542_problem
  (X : Type*) [TopologicalSpace X] [CompactSpace X]
  (f : X → X) (h_emb : Embedding f)
  (h_shrink : ∀ (U : Set (Set X)), (∀ u ∈ U, IsOpen u) → ⋃₀ U = Set.univ →
    ∃ N : ℕ, ∃ u ∈ U, Set.range (f^[N]) ⊆ u) :
  ∀ x : X, ∃ p : X, Filter.Tendsto (fun n ↦ f^[n] x) Filter.atTop (nhds p) := by
  sorry



theorem theorem_994523_problem {X : Type*} [TopologicalSpace X] (A : Set X)
  (h1 : A ≠ ∅)
  (h2 : IsOpen A) :
  interior (frontier A) = ∅ := by
  sorry



theorem theorem_994519_problem {n : ℕ} {K : Type*} [Field K] [DecidableEq K]
  (A : Matrix (Fin n) (Fin n) K)
  (hA : IsUnit A.det)
  (h_a0 : (Matrix.charpoly A).coeff 0 ≠ 0) :
  A⁻¹ = -((Matrix.charpoly A).coeff 0)⁻¹ • ∑ i in Finset.range n, (Matrix.charpoly A).coeff (i + 1) • A ^ i := by
  sorry

theorem theorem_994488_problem (r : ℝ) (a b : ℕ → ℝ)
  (h_init_a0 : a 0 = b 0)
  (h_init_a1 : a 1 = b 1)
  (h_rec_a : ∀ n : ℕ, n ≥ 2 → a n = - (a (n - 2)) / ((n + r) * (n + r - 1) + 2 * (n + r) - 5 / 16))
  (h_rec_b : ∀ n : ℕ, n ≥ 2 → b n = - (b (n - 2)) / ((n + r) * (n + r - 1) + 2 * (n + r) - 5 / 16)) :
  a = b := by
  sorry





theorem theorem_995551_problem (a b c : ℝ) :
  b^2 * c + b * c^2 + a^2 * c + a * c^2 + a^2 * b + a * b^2 + 2 * a * b * c = 
  (b + c) * (b + a) * (a + c) := by
  sorry



theorem theorem_995536_problem
  (h : ℝ × ℝ → ℝ)
  (G : ℝ × ℝ → ℝ × ℝ)
  (h_diff : ContDiff ℝ 1 h)
  (G_diff : ContDiff ℝ 1 G)
  (G_curl_zero : ∀ x y, deriv (fun x' => (G (x', y)).2) x = deriv (fun y' => (G (x, y')).1) y) :
  (∀ x y, deriv (fun x' => h (x', y) * (G (x', y)).2) x = deriv (fun y' => h (x, y') * (G (x, y')).1) y) ↔
  (∃ lam : ℝ × ℝ → ℝ, ∀ x y,
    (deriv (fun x' => h (x', y)) x, deriv (fun y' => h (x, y')) y) = lam (x, y) • G (x, y)) := by
  sorry

theorem theorem_995135_problem (r θ : ℝ → ℝ) (k : ℝ)
  (h_smooth_r : ContDiff ℝ ⊤ r)
  (h_smooth_θ : ContDiff ℝ ⊤ θ)
  (h_eq : ∀ t, (r t)^2 * deriv θ t = k) :
  ∀ t, 2 * deriv r t * deriv θ t + r t * deriv (deriv θ) t = 0 := by
  sorry

theorem theorem_994984_problem
  (LineIntegral : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ)
  (DoubleIntegral : (ℝ → ℝ → ℝ) → ℝ)
  (Area : ℝ)
  (h_area : Area = DoubleIntegral (fun _ _ => 1))
  (h_linear : ∀ c : ℝ, DoubleIntegral (fun _ _ => c) = c * DoubleIntegral (fun _ _ => 1))
  (h_green : ∀ (P Q : ℝ → ℝ → ℝ),
    LineIntegral P Q = DoubleIntegral (fun x y => deriv (fun x => Q x y) x - deriv (fun y => P x y) y)) :
  Area = (1 / 2) * LineIntegral (fun _ y => -y) (fun x _ => x) := by
  sorry









theorem theorem_994939_problem
  (R : Type*) [Ring R]
  (M : Type*) [AddCommGroup M] [Module R M]
  (hR : ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0)
  (hM : ∀ (r : R) (m : M), r • m = 0 → r = 0 ∨ m = 0) :
  Subsingleton M := by
  sorry



theorem theorem_995401_problem (a b : ℝ) (f : ℝ → ℝ → ℝ)
  (hf : Continuous (fun p : ℝ × ℝ ↦ f p.1 p.2)) :
  let x : ℝ → ℝ := fun t ↦ a * Real.cos t
  let y : ℝ → ℝ := fun t ↦ b * Real.sin t
  ∫ t in (0)..2 * Real.pi, f (x t) (y t) * Real.sqrt ((deriv x t)^2 + (deriv y t)^2) =
  ∫ t in (0)..2 * Real.pi, f (a * Real.cos t) (b * Real.sin t) * Real.sqrt ((-a * Real.sin t)^2 + (b * Real.cos t)^2) := by
  sorry

theorem theorem_995361_problem {R : Type*} [CommRing R] (I : Ideal R)
  (h1 : I ≠ ⊤)
  (h2 : I ≠ sInf {P : Ideal R | P.IsPrime})
  (h3 : (I : Set R) ⊆ ⋃ (P : Ideal R) (_ : P.IsPrime), (P : Set R)) :
  ∃ P : Ideal R, P.IsPrime ∧ I ≤ P := by
  sorry







theorem theorem_995663_problem (a : ℝ) (f : ℝ → ℝ)
  (h_cont : ContinuousOn f (Set.Ici a))
  (h_mono : AntitoneOn f (Set.Ici a))
  (h_pos : ∀ x, a ≤ x → 0 < f x)
  (F G : ℝ → ℝ)
  (hF : ∀ t, F t = ∫ x in a..t, f x)
  (hG : ∀ t, G t = ∫ x in a..t, Real.sqrt (f x)) :
  ∀ t, a < t → deriv F t = (deriv G t)^2 := by
  sorry

theorem theorem_995681_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (II : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (A : V →ₗ[ℝ] V)
  (hA : ∀ u v, ⟪A u, v⟫_ℝ = II u v)
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) :
  (1 / (FiniteDimensional.finrank ℝ V : ℝ)) * ∑ i, II (b i) (b i) =
  (1 / (FiniteDimensional.finrank ℝ V : ℝ)) * LinearMap.trace ℝ V A := by
  sorry

theorem theorem_995893_problem (k p : ℕ) (m : Fin k → ℕ)
  (hm : ∀ i, m i > 0) (hp : p > 0) :
  FiniteDimensional.finrank ℝ (MultilinearMap ℝ (fun i => Fin (m i) → ℝ) (Fin p → ℝ)) =
  (∏ i, m i) * p := by
  sorry

theorem theorem_995246_problem
  (a b : ℝ) (h_ab : a < b)
  (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
  (F : ℝ → ℝ) (hF : ∀ x ∈ Set.Icc a b, HasDerivWithinAt F (f x) (Set.Icc a b) x)
  (y : ℝ → ℝ) :
  (∀ x ∈ Set.Icc a b, HasDerivWithinAt y (f x * y x) (Set.Icc a b) x) ↔
  (∃ C : ℝ, ∀ x ∈ Set.Icc a b, y x = C * Real.exp (F x)) := by
  sorry





theorem theorem_995619_problem (a b : ℤ) (k : ℕ)
  (ha : Prime a)
  (hk_gt : k > 3)
  (hk_odd : Odd k)
  (h_eq : b ^ k = a) :
  False := by
  sorry





theorem theorem_995965_problem (r θ φ : ℝ) 
  (hr : r > 0)
  (hθ : θ ∈ Set.Icc 0 Real.pi)
  (hφ : φ ∈ Set.Ico 0 (2 * Real.pi)) :
  let r_vec (t p : ℝ) : ℝ × ℝ × ℝ := 
    (r * Real.sin t * Real.cos p, r * Real.sin t * Real.sin p, r * Real.cos t)
  let e_r : ℝ × ℝ × ℝ := 
    (Real.sin θ * Real.cos φ, Real.sin θ * Real.sin φ, Real.cos θ)
  let partial_theta := deriv (fun t => r_vec t φ) θ
  let partial_phi := deriv (fun p => r_vec θ p) φ
  let cross (u v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := 
    (u.2.1 * v.2.2 - u.2.2 * v.2.1, 
     u.2.2 * v.1 - u.1 * v.2.2, 
     u.1 * v.2.1 - u.2.1 * v.1)
  let smul (c : ℝ) (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
    (c * v.1, c * v.2.1, c * v.2.2)
  cross partial_theta partial_phi = smul (r^2 * Real.sin θ) e_r := by
  sorry











theorem theorem_996271_problem {G H : Type*} [Group G] [Group H]
  (f : G → H)
  (h_bij : Function.Bijective f)
  (h_hom : ∀ a b : G, f (a * b) = f a * f b) :
  Nonempty (G ≃* H) := by
  sorry



theorem theorem_996299_problem (f : ℝ → ℝ)
  (h_cont : ContinuousOn f (Set.Icc 0 1))
  (h_int : ∀ x ∈ Set.Icc 0 1, ∫ t in (0)..x, f t = 0) :
  ∀ x ∈ Set.Icc 0 1, f x = 0 := by
  sorry



theorem theorem_996665_problem
  (Θ S : Type*)
  (f : Θ → S → ℝ)
  (x : S)
  (Likelihood : Θ → ℝ)
  (hLikelihood : ∀ θ, Likelihood θ = f θ x)
  (MLE : Set Θ)
  (hMLE : MLE = {θ | ∀ θ', Likelihood θ' ≤ Likelihood θ}) :
  MLE = {θ | ∀ θ', f θ' x ≤ f θ x} := by
  sorry



theorem theorem_996230_problem
  {X : Type*} [TopologicalSpace X]
  (F : Set X) (x : X)
  (hx : x ∈ F)
  (h : IsClosed (F \ {x})) :
  ∃ U, IsOpen U ∧ F ∩ U = {x} := by
  sorry

theorem theorem_996978_problem (A B : Set ℝ)
  (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty)
  (hA_bdd_above : BddAbove A) (hB_bdd_above : BddAbove B)
  (hA_bdd_below : BddBelow A) (hB_bdd_below : BddBelow B)
  (hA_inf : 0 ≤ sInf A) (hB_inf : 0 ≤ sInf B) :
  sSup {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b} ≤ sSup A * sSup B := by
  sorry



theorem theorem_997334_problem
  (X : Type*) [TopologicalSpace X]
  (A : Set X)
  (i : A → X) (hi : i = Subtype.val)
  (Y : Type*) [TopologicalSpace Y]
  (f : Y → A) :
  Continuous f ↔ Continuous (i ∘ f) := by
  sorry



theorem theorem_996681_problem (F : Type*)
  [LinearOrderedField F] [MetricSpace F] [CompleteSpace F] [Archimedean F] :
  ∃ φ : F →+*o ℝ, Function.Injective φ := by
  sorry



theorem theorem_997340_problem (R : Type*) [CommRing R] (P : ℕ → Ideal R)
  (h_prime : ∀ i, (P i).IsPrime)
  (h_chain : ∀ i j, i ≤ j → P j ≤ P i) :
  (⨅ i, P i).IsPrime := by
  sorry





theorem theorem_997419_problem (x y z : ℝ) (h : ![x, y, z] ≠ 0) :
  {u : Fin 3 → ℝ | ∃ (hu : u ≠ 0), Projectivization.mk ℝ u hu = Projectivization.mk ℝ ![x, y, z] h} =
  {u : Fin 3 → ℝ | ∃ (k : ℝ), k ≠ 0 ∧ u = k • ![x, y, z]} := by
  sorry







theorem theorem_996340_problem
  (k₁ k₂ Y : ℝ)
  (c₁ c₂ : ℝ → ℝ)
  (hY : Y ≠ 0)
  (hk₁ : k₁ ≠ 0)
  (hc₁ : Differentiable ℝ c₁)
  (hc₂ : Differentiable ℝ c₂)
  (h_ne : ∀ t, c₁ t ≠ k₂ / k₁)
  (h1 : ∀ t, deriv c₁ t = Y * k₁ * c₁ t - k₂)
  (h2 : ∀ t, deriv c₂ t = -k₁ * c₁ t + k₂) :
  ∃ K : ℝ, ∀ t, c₁ t + (k₂ / k₁) * (1 - 1 / Y) * Real.log (abs (c₁ t - k₂ / k₁)) = -c₂ t / Y + K := by
  sorry



theorem theorem_997045_problem (A : Set cantorSet) (hA_clopen : IsClopen A) (hA_nonempty : A.Nonempty) :
  ∃ A₁ A₂ : Set cantorSet, IsClopen A₁ ∧ IsClopen A₂ ∧ A₁.Nonempty ∧ A₂.Nonempty ∧
  A = A₁ ∪ A₂ ∧ A₁ ∩ A₂ = ∅ := by
  sorry









theorem theorem_997252_problem
  (C : Set (Set (ℝ × ℝ)))
  (L : ℝ)
  (hL : 0 < L)
  (h_disjoint : C.PairwiseDisjoint id)
  (h_intervals : ∀ s ∈ C, ∃ (a b : ℝ × ℝ), s = openSegment ℝ a b ∧ dist a b = L) :
  ⋃₀ C ≠ univ := by
  sorry









theorem theorem_997874_problem {A B : Type*} [Group A] [Group B] (θ : A →* B) :
  let ρ : Setoid A := Setoid.ker θ
  ∃ ψ : Quotient ρ ≃ θ.range,
    (∀ a, ψ ⟦a⟧ = ⟨θ a, Set.mem_range_self a⟩) ∧
    (∀ a b, ψ ⟦a * b⟧ = ψ ⟦a⟧ * ψ ⟦b⟧) := by
  sorry

theorem theorem_997662_problem (x : ℝ) (h : -1 < x ∧ x < 1) :
  HasDerivAt (fun t => Real.sqrt (1 - t^2) / (1 - t))
    (1 / ((1 - x) * Real.sqrt (1 - x^2))) x := by
  sorry













theorem theorem_998406_problem {X : Type*} [TopologicalSpace X] (x : X) (N : Set X) :
  N ∈ nhds x ↔ ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ N := by
  sorry

theorem theorem_998539_problem
  {K V : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup V] [NormedSpace K V] [CompleteSpace V]
  (A : V ≃L[K] V)
  (B : V ≃ₗ[K] V)
  (C : V ≃L[K] V)
  (hC : C.toLinearEquiv = B.symm.trans (A.toLinearEquiv.trans B)) :
  C.symm.toLinearEquiv = B.symm.trans (A.symm.toLinearEquiv.trans B) := by
  sorry

theorem theorem_998331_problem (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
  (hB : ∀ i j, 0 ≤ B i j)
  (B_tilde : Matrix (Fin (n + 1)) (Fin (n + 1)) EReal)
  (h_def : ∀ (i j : Fin (n + 1)), B_tilde i j =
    if h : i.val < n ∧ j.val < n then
      let i' : Fin n := ⟨i.val, h.1⟩
      let j' : Fin n := ⟨j.val, h.2⟩
      if B i' j' = 0 then ⊥ else ((Real.log (B i' j')) : EReal)
    else if i = Fin.last n ∧ j = Fin.last n then
      ⊥
    else
      0) :
  (∀ (i j : Fin n), B_tilde i.castSucc j.castSucc = if B i j = 0 then ⊥ else ((Real.log (B i j)) : EReal)) ∧
  (∀ (i : Fin n), B_tilde i.castSucc (Fin.last n) = 0) ∧
  (∀ (j : Fin n), B_tilde (Fin.last n) j.castSucc = 0) ∧
  (B_tilde (Fin.last n) (Fin.last n) = ⊥) := by
  sorry



