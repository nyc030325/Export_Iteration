import Mathlib
import Mathlib.Tactic







theorem theorem_600920_problem (a : ℝ) (n : ℤ) (ha : a < 0) :
  (a : ℂ) ^ (n : ℂ) = (a : ℂ) ^ n := by
  sorry

theorem theorem_601348_problem
  (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (h_distinct : p ≠ q)
  (n : ℕ) (hn : n = p * q)
  (φ : ℕ) (hφ : φ = (p - 1) * (q - 1))
  (e d : ℕ) (h_ed : e * d ≡ 1 [MOD φ])
  (M : ℤ) (h_coprime : Int.gcd M n = 1) :
  M ^ (e * d) ≡ M [ZMOD n] := by
  sorry



theorem theorem_601292_problem (n : ℕ) (hn : 0 < n) :
  Transcendental ℚ (Real.pi ^ n) := by
  sorry



theorem theorem_601751_problem
  {G : Type*} [Group G]
  (S : Set G)
  (hS_fin : S.Finite)
  (hS_gen : Subgroup.closure S = ⊤)
  (hS_irr : ∀ s ∈ S, Subgroup.closure (S \ {s}) ≠ ⊤)
  (φ : G → G)
  (hφ : (∃ f : G ≃* G, φ = f) ∨ (∃ f : G ≃* MulOpposite G, φ = λ x ↦ MulOpposite.unop (f x))) :
  Subgroup.closure (φ '' S) = ⊤ ∧
  ∀ s' ∈ φ '' S, Subgroup.closure ((φ '' S) \ {s'}) ≠ ⊤ := by
  sorry



theorem theorem_602349_problem {S : Type*} [CommSemigroup S]
  (n : ℕ) (hn : n > 0) (a : Fin n → S) (φ : Equiv.Perm (Fin n)) :
  match List.ofFn a, List.ofFn (a ∘ φ) with
  | h1 :: t1, h2 :: t2 => List.foldl (· * ·) h1 t1 = List.foldl (· * ·) h2 t2
  | _, _ => True := by
  sorry









theorem theorem_602042_problem (V E F : ℕ)
  (h_V : V = 10)
  (h_E : E = 15)
  (h_euler : V + F = E + 2)
  (face_degrees : List ℕ)
  (h_F_card : face_degrees.length = F)
  (h_faces_hex : ∀ d ∈ face_degrees, d = 6)
  (h_handshaking : face_degrees.sum = 2 * E) :
  False := by
  sorry

theorem theorem_600777_problem (s₁ t₁ s₂ t₂ : ℝ)
  (hs₁ : 0 < s₁) (ht₁ : 0 < t₁ ∧ t₁ < 2 * Real.pi)
  (hs₂ : 0 < s₂) (ht₂ : 0 < t₂ ∧ t₂ < 2 * Real.pi)
  (hG : (Real.cosh s₁ * Real.cos t₁, Real.sinh s₁ * Real.sin t₁) = 
        (Real.cosh s₂ * Real.cos t₂, Real.sinh s₂ * Real.sin t₂)) :
  s₁ = s₂ ∧ t₁ = t₂ := by
  sorry

theorem theorem_602277_problem (n m : ℕ) :
  (∃ (U : Set (Fin m → ℝ)), IsOpen U ∧ Nonempty ((Fin n → ℝ) ≃ₜ U)) ↔ n = m := by
  sorry

theorem theorem_601929_problem (X : Type*) [TopologicalSpace X] (A : ℕ → Set X) :
  interior (⋂ i, interior (A i)) ⊆ interior (⋂ i, A i) := by
  sorry







theorem theorem_602250_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (f : H →L[ℝ] ℝ)
  (c : ℝ)
  (S : Set H)
  (hS : S = f ⁻¹' {c}) :
  IsClosed S := by
  sorry





theorem theorem_602507_problem :
  let z1 : ℂ := Real.exp 1
  let z2 : ℂ := 1
  let z3 : ℂ := 1 - (Real.sqrt 3 : ℂ)
  -- Condition 1: Verify the first segment corresponds to the line from e to 1
  (∀ t : ℝ, 0 ≤ t ∧ t ≤ 1 → gamma_602507 t = (1 - (t : ℂ)) * z1 + (t : ℂ) * z2) ∧
  -- Condition 2: Verify the second segment corresponds to the line from 1 to 1-sqrt(3)
  -- Note: The parameterization for segment z2->z3 over [1,2] maps t to (2-t)z2 + (t-1)z3
  (∀ t : ℝ, 1 < t ∧ t ≤ 2 → gamma_602507 t = (1 - ((t : ℂ) - 1)) * z2 + ((t : ℂ) - 1) * z3) ∧
  -- Condition 3: Verify the function is continuous on the entire interval [0, 2]
  ContinuousOn gamma_602507 (Set.Icc 0 2) := by
  sorry

theorem theorem_602934_problem (m n : ℤ) (a k : ℝ)
  (hmn : m ≠ n) (hk : k > 0) :
  (Complex.sin ((m - n : ℂ) * (k : ℂ) * (a : ℂ)) / (m - n : ℂ)) =
  (1 / 2 : ℂ) * ∫ t in (-k * a)..(k * a), Complex.exp (Complex.I * (m - n : ℂ) * (t : ℂ)) := by
  sorry

theorem theorem_602190_problem (I : ℕ → ℝ)
  (hI0 : I 0 = 1)
  (hI_rec : ∀ n : ℕ, n ≥ 1 → I n = (n : ℝ) * (Real.pi / 2) ^ (n - 1) - I (n - 1)) :
  ∀ n : ℕ, n ≥ 2 → I n = ∑ i in Finset.Icc 2 n, (-1 : ℝ) ^ (n - i) * (i : ℝ) * (Real.pi / 2) ^ (i - 1) := by
  sorry







theorem theorem_602748_problem (f : ℝ → ℝ)
  (h_rat : ∀ x : ℝ, (∃ q : ℚ, (q : ℝ) = x) → f x = 0)
  (h_irr : ∀ x : ℝ, (¬ ∃ q : ℚ, (q : ℝ) = x) → f x = 1) :
  ∀ x₀ : ℝ, ¬ ContinuousAt f x₀ := by
  sorry





theorem theorem_602796_problem
  {m n k : ℕ}
  (X : Matrix (Fin m) (Fin n) ℝ)
  (L : Matrix (Fin k) (Fin n) ℝ)
  (hX : (X.transpose * X).PosDef)
  (h_inv : (L * (X.transpose * X)⁻¹ * L.transpose).det ≠ 0) :
  let C := (X.transpose * X)⁻¹ * L.transpose * (L * (X.transpose * X)⁻¹ * L.transpose)⁻¹ * L * (X.transpose * X)⁻¹
  C.PosSemidef := by
  sorry





theorem theorem_602576_problem
  (Link Component : Type)
  (L : Link)
  (L1 L2 : Component)
  (components : Link → Set Component)
  (h_comp : components L = {L1, L2})
  (h_distinct : L1 ≠ L2)
  (is_represented_by_reduced_alternating_diagram : Link → Prop)
  (h_red_alt : is_represented_by_reduced_alternating_diagram L)
  (satisfies_taits_conjecture : Link → Prop)
  (h_tait : satisfies_taits_conjecture L)
  (can_transform_L1_to_unknot_preserving_inter_crossing : Link → Component → Component → Prop) :
  ¬ can_transform_L1_to_unknot_preserving_inter_crossing L L1 L2 := by
  sorry





theorem theorem_603036_problem (m n : ℤ) 
  (a b c d : ℤ) 
  (h_a : a = (m + n) * (m - n))
  (h_b : b = 2 * m * n)
  (h_c : c = n * (m - n))
  (h_d : d = m^2 - m * n + 2 * n^2) : 
  d * (a + b - c) = a^2 + b^2 - c^2 := by
  sorry

theorem theorem_602900_problem
  (n m : ℕ)
  (F : (Fin n → ℝ) × (Fin m → ℝ) → (Fin m → ℝ))
  (x₀ : Fin n → ℝ)
  (y₀ : Fin m → ℝ)
  (hF_diff : ContDiff ℝ 1 F)
  (hF_zero : F (x₀, y₀) = 0)
  (hF_jac : IsUnit (fderiv ℝ (fun y ↦ F (x₀, y)) y₀)) :
  ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x₀ ∈ U ∧
  ∃ g : (Fin n → ℝ) → (Fin m → ℝ),
    ContDiffOn ℝ 1 g U ∧
    g x₀ = y₀ ∧
    ∀ x ∈ U, F (x, g x) = 0 := by
  sorry



theorem theorem_603261_problem (x y r theta : ℝ)
  (hr : 0 ≤ r)
  (hx : x = r * Real.cos theta)
  (hy : y = r * Real.sin theta) :
  Real.sqrt (x^2 + y^2) = r := by
  sorry



theorem theorem_602728_problem (n : ℕ) (hn : 0 < n) (x y : Fin n → ℝ) :
  ∃ B > 0, ∀ b > B, Convex ℝ { p : ℝ × ℝ | ∏ i, Real.sqrt ((p.1 - x i)^2 + (p.2 - y i)^2) ≤ b^n } := by
  sorry





theorem theorem_603163_problem
  (num_c num_t : ℕ)
  (c : Fin num_c → EuclideanSpace ℝ (Fin 3) → ℝ)
  (S2 : Set (EuclideanSpace ℝ (Fin 3)))
  (hS2 : S2 = Metric.sphere 0 1)
  (hc_vals : ∀ i, ∀ x ∈ S2, c i x = 0 ∨ c i x = 1)
  (T : Fin num_t → Set (EuclideanSpace ℝ (Fin 3)))
  (h_cover : S2 = ⋃ k, T k)
  (A : Set (Fin num_t))
  (hA : A = {k | ∀ x ∈ T k, ∑ i, c i x > 0}) :
  (⋃ k ∈ A, T k) ⊆ {x ∈ S2 | ∑ i, c i x > 0} := by
  sorry





theorem theorem_603515_problem
  (n : ℕ)
  (hn : n ≥ 2)
  (P : Polynomial (Polynomial ℝ))
  (h_deg : P.degree = n) :
  ∃ (y_param : ℝ → Polynomial ℝ),
    ∀ k : ℝ,
      let y := y_param k
      let P_sub := P.eval y
      ∃ (r : ℕ) (Q : Polynomial ℝ),
        P_sub = X ^ r * Q ∧ Q.degree = ↑(n - 1) := by
  sorry



theorem theorem_603987_problem (b x : ℝ) (h : b ≠ 0) :
  x^4 + 4 * b^4 = (x^2 + 2 * b^2 - 2 * b * x) * (x^2 + 2 * b^2 + 2 * b * x) := by
  sorry







theorem theorem_604155_problem (h : ℝ) (h_pos : 0 < h) :
  |Real.log (1 + h) - h| ≤ h ^ 2 / (2 + h) := by
  sorry









theorem theorem_604517_problem (x y z : ℝ)
  (h1 : x = 1)
  (h2 : y + z = 5)
  (h3 : y * z ≠ 0) :
  (x^3 + y^3 + z^3) / (x * y * z) = (126 - 15 * y * z) / (y * z) := by
  sorry













theorem theorem_604625_problem (z : ℂ) (p : ℝ) (h : z ≠ 0) :
  z ^ (p : ℂ) = (Complex.abs z : ℂ) ^ (p : ℂ) * Complex.exp (Complex.I * ↑p * ↑(Complex.arg z)) := by
  sorry







theorem theorem_604746_problem (E : Set ℝ) (hE : MeasurableSet E) :
  MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ∈ E} := by
  sorry

theorem theorem_604598_problem (n s : ℕ) (hn : n > 0) (g : ℤ) (r : Fin s → ℤ)
  (log_r : Fin s → ℕ)
  (h_log : ∀ i, g ^ (log_r i) ≡ r i [ZMOD (n^2)]) :
  ∀ i, r i ≡ g ^ (log_r i) [ZMOD (n^2)] := by
  sorry



theorem theorem_604962_problem (f : ℂ → ℂ) (hf : Continuous f)
  (h : ∀ z : ℂ, IsAlgebraic ℚ z → f z = 0) :
  ∀ z : ℂ, f z = 0 := by
  sorry





theorem theorem_604652_problem
  (n m : ℕ)
  (Xt : Matrix (Fin n) (Fin m) ℝ)
  (V D : Matrix (Fin m) (Fin m) ℝ)
  (hn : n ≠ 0)
  (hD_diag : ∀ i j, i ≠ j → D i j = 0)
  (hD_pos : ∀ i, 0 < D i i)
  (Gt : Matrix (Fin m) (Fin m) ℝ)
  (hGt : Gt = Xt.transpose * Xt)
  (h_eig : Gt * V = V * D)
  (Ct : Matrix (Fin n) (Fin n) ℝ)
  (hCt : Ct = (1 / (n : ℝ)) • (Xt * Xt.transpose))
  (U : Matrix (Fin n) (Fin m) ℝ)
  (hU : U = Xt * V * (Matrix.diagonal (fun i => 1 / Real.sqrt (D i i)))) :
  Ct * U = U * ((1 / (n : ℝ)) • D) := by
  sorry





theorem theorem_605198_problem
  {n : ℕ} {R : Type*} [CommSemiring R]
  (A : Matrix (Fin n) (Fin n) R)
  (k : ℕ) (hk : k > 0)
  (i j : Fin n) :
  (A ^ k) i j =
    ∑ p : Fin (k - 1) → Fin n,
      ∏ m : Fin k,
        A (if h : m.1 = 0 then i else p ⟨m.1 - 1, by omega⟩)
          (if h : m.1 = k - 1 then j else p ⟨m.1, by omega⟩) := by
  sorry

theorem theorem_605427_problem
  (a x : ℝ)
  (p : ℕ → ℤ)
  (k : ℕ → ℕ)
  (ha : 0 < a)
  (hx : Irrational x)
  (h_lim : Filter.Tendsto (fun n ↦ (p n : ℝ) / 2 ^ (k n)) Filter.atTop (nhds x)) :
  Filter.Tendsto (fun n ↦ a ^ ((p n : ℝ) / 2 ^ (k n))) Filter.atTop (nhds (a ^ x)) := by
  sorry











theorem theorem_605284_problem (K F : Type*) [Field K] [Field F] [Algebra F K]
  [FiniteDimensional F K] :
  IsGalois F K ↔ ∃ G : Subgroup (K ≃ₐ[F] K), IntermediateField.fixedField G = ⊥ := by
  sorry

theorem theorem_605838_problem :
  ¬ ∃ (f g : ℝ → ℝ), ∀ x y : ℝ, y ≠ 0 →
    y * (1 - Real.exp (-x / y)) = f x * g y := by
  sorry

theorem theorem_605628_problem
  {X : Type*} [MetricSpace X] [CompactSpace X]
  (f : X → ℝ) (hf : Continuous f) :
  UniformContinuous f := by
  sorry



theorem theorem_606015_problem
  (y : ℝ → ℝ)
  (h_diff : Differentiable ℝ y)
  (h_domain : ∀ t, y t / (y t + 2) > 0)
  (h_ode : ∀ t, deriv y t = (1 - (y t + 1)^2) / ((y t + 1)^2)) :
  ∃ c : ℝ, ∀ t, y t + (1 / 2 : ℝ) * Real.log (y t / (y t + 2)) = -t + c := by
  sorry



theorem theorem_605938_problem (n : ℕ) (x y : Fin n → ZMod 2) :
  (1 / (2 : ℝ) ^ n) * ∑ z : Fin n → ZMod 2, (-1 : ℝ) ^ (∑ i, z i * (x i + y i)).val =
  if x = y then 1 else 0 := by
  sorry



theorem theorem_606341_problem (n : ℕ) (g : ℕ → ℝ) :
  ∑ k in Finset.range (n + 1), g k * g (n - k) ≤ ∑ k in Finset.range (n + 1), (g k)^2 := by
  sorry

theorem theorem_605948_problem (h : ℝ → ℝ)
  (h_eq : ∀ x ∈ Set.Ioo 0 1, h x = x * Real.sin (1 / x)) :
  UniformContinuousOn h (Set.Ioo 0 1) := by
  sorry



