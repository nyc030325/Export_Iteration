import Mathlib
import Mathlib.Tactic



theorem theorem_650689_problem (X : Set (ℝ × ℝ))
  (A B : Set X)
  (h_union : A ∪ B = Set.univ)
  (h_disj : Disjoint A B)
  (h_A_nonempty : A.Nonempty)
  (h_B_nonempty : B.Nonempty)
  (h_A_open : IsOpen A)
  (h_B_open : IsOpen B) :
  ¬ IsConnected X := by
  sorry











theorem theorem_650260_problem
  (x y : lp (fun _ : ℕ => ℝ) 2)
  (a : Set.Icc (0 : ℝ) 1 → lp (fun _ : ℕ => ℝ) 2)
  -- The definition of a(t) at t = 1
  (h_end : a ⟨1, by norm_num⟩ = x)
  -- The definition of a(t) for t in each interval s_n
  (h_def : ∀ (n : ℕ) (t : Set.Icc (0 : ℝ) 1),
    t.val ∈ Set.Ico (1 - 1 / (2 : ℝ) ^ n) (1 - 1 / (2 : ℝ) ^ (n + 1)) →
    ∀ k : ℕ,
      (k < n → a t k = x k) ∧
      (k > n → a t k = y k) ∧
      (k = n → a t k = (2 : ℝ) ^ (n + 1) *
        ((t.val - (1 - 1 / (2 : ℝ) ^ n)) * x n +
         ((1 - 1 / (2 : ℝ) ^ (n + 1)) - t.val) * y n))) :
  -- Conclusion: a is a continuous path from y to x
  Continuous a ∧ a ⟨0, by norm_num⟩ = y := by
  sorry









theorem theorem_651431_problem :
  ∃ (g : ℝ × ℝ → ℝ) (f : ℝ → ℝ) (x₀ : ℝ × ℝ),
    DifferentiableAt ℝ g x₀ ∧
    DifferentiableAt ℝ (f ∘ g) x₀ ∧
    ¬ DifferentiableAt ℝ f (g x₀) := by
  sorry







theorem theorem_651173_problem (F : ℝ → ℝ)
  (h_diff : DifferentiableOn ℝ F (Set.Ioi 0))
  (h_ode : ∀ x ∈ Set.Ioi 0, x * deriv F x + 2 * F x - (F x)^2 = 0)
  (h_nz : ∀ x ∈ Set.Ioi 0, F x ≠ 0) :
  ∃ C : ℝ, ∀ x ∈ Set.Ioi 0, F x = 2 / (1 + C * x^2) := by
  sorry











theorem theorem_651693_problem {R S : Type*} [CommRing R] [CommRing S]
  (f : R →+* S) (M : Ideal S)
  (hf : Function.Surjective f) (hM : M.IsMaximal) :
  (M.comap f).IsMaximal := by
  sorry



theorem theorem_651460_problem (p q r : ℕ)
  (hp : p > 0) (hq : q > 0) (hr : r > 0)
  (h_ineq : (1 : ℚ) / p + (1 : ℚ) / q + (1 : ℚ) / r ≤ 1) :
  Set.Finite { t : ℕ × ℕ × ℕ |
    let ⟨x, y, z⟩ := t
    x > 0 ∧ y > 0 ∧ z > 0 ∧
    x^p + y^q = z^r ∧
    Nat.gcd x (Nat.gcd y z) = 1 } := by
  sorry





theorem theorem_652188_problem (P : Type) (V : P → Option Bool) :
  ∃ V_star : P → Bool, ∀ p : P, ∀ b : Bool, V p = some b → V_star p = b := by
  sorry

theorem theorem_652501_problem
  (I : Set ℝ)
  (hI : Convex ℝ I)
  (f g : ℝ → ℝ)
  (hf : DifferentiableOn ℝ f I)
  (hg : DifferentiableOn ℝ g I)
  (h_deriv : ∀ x ∈ I, deriv f x = deriv g x) :
  ∃ c : ℝ, ∀ x ∈ I, f x = g x + c := by
  sorry









theorem theorem_652403_problem (a b : ℝ) (f g : ℝ → ℝ)
  (h_ab : a < b)
  (hf : ContinuousOn f (Set.Icc a b))
  (hg : ContinuousOn g (Set.Icc a b))
  (h_lt : ∀ x ∈ Set.Icc a b, f x < g x) :
  ∫ x in a..b, f x < ∫ x in a..b, g x := by
  sorry











theorem theorem_652791_problem (z w : ℂ) (hz : z ≠ 0) :
  Complex.exp (Complex.log (z ^ w)) = Complex.exp (w * Complex.log z) := by
  sorry

theorem theorem_652576_problem (x₁ x₂ x₃ x₄ : ℝ) :
  IsGreatest {y : ℝ | y ≤ x₁ ∧ y ≤ x₂ ∧ y ≤ x₃ ∧ y ≤ x₄} (min x₁ (min x₂ (min x₃ x₄))) := by
  sorry





theorem theorem_652383_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
  let H := (1 / 2 : ℝ) • (A + A.transpose)
  ∃ S : Matrix (Fin n) (Fin n) ℝ,
    S.PosSemidef ∧ S ^ 2 = H ^ 2 ∧
    let X_star := (1 / 2 : ℝ) • (S - H)
    X_star.PosSemidef ∧
    ∀ X : Matrix (Fin n) (Fin n) ℝ, X.PosSemidef →
      Matrix.trace ((X_star + A).transpose * (X_star + A)) ≤ Matrix.trace ((X + A).transpose * (X + A)) ∧
      (Matrix.trace ((X_star + A).transpose * (X_star + A)) = Matrix.trace ((X + A).transpose * (X + A)) → X = X_star) := by
  sorry





theorem theorem_652960_problem (x : ℝ) (hx : x ≠ 0) :
  ∃ y z : ℝ, Irrational y ∧ Irrational z ∧ x = y * z := by
  sorry



theorem theorem_652952_problem
  (k : Type*) [Field k] [Infinite k]
  (n : ℕ)
  (f : MvPolynomial (Fin n) k)
  (h : ∀ x : Fin n → k, MvPolynomial.eval x f = 0) :
  f = 0 := by
  sorry

theorem theorem_653193_problem
  (u v : ℝ × ℝ → ℝ)
  (D : Set (ℝ × ℝ))
  (hD : IsOpen D)
  -- The condition "satisfying a system of PDEs with smooth coefficients" is represented
  -- by an abstract predicate P.
  (SystemOfPDEsWithSmoothCoeffs : ((ℝ × ℝ → ℝ) × (ℝ × ℝ → ℝ)) → Set (ℝ × ℝ) → Prop)
  (h_sol : SystemOfPDEsWithSmoothCoeffs (u, v) D) :
  ContDiffOn ℝ ⊤ u D ∧ ContDiffOn ℝ ⊤ v D := by
  sorry

theorem theorem_653876_problem (X : Type*) [TopologicalSpace X]
  (h_indiscrete : ∀ U : Set X, IsOpen U ↔ U = ∅ ∨ U = Set.univ)
  (x_seq : ℕ → X) (x : X) :
  Filter.Tendsto x_seq Filter.atTop (nhds x) := by
  sorry

theorem theorem_653822_problem (n : ℕ) (h : n ≥ 2) :
  Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  sorry



theorem theorem_653530_problem (i : ℕ → ℝ) (δ : ℝ)
  (h1 : Filter.Tendsto i Filter.atTop (nhds δ))
  (h2 : δ ≠ 0) :
  Filter.Tendsto (fun p ↦ 1 / i p) Filter.atTop (nhds (1 / δ)) := by
  sorry

theorem theorem_652419_problem :
  ∃ (G H : Type) (_ : Group G) (_ : Group H) (_ : Fintype G) (_ : Fintype H)
    (_ : DecidableEq G) (_ : DecidableEq H),
    (∀ k : ℕ, Fintype.card {x : G // orderOf x = k} = Fintype.card {y : H // orderOf y = k}) ∧
    ¬ Nonempty (G ≃* H) := by
  sorry

theorem theorem_653525_problem (X I : Type*) (U : I → Set X)
  [t : TopologicalSpace X]
  (h_gen : t = TopologicalSpace.generateFrom (Set.range U)) :
  SecondCountableTopology X ↔ Countable I := by
  sorry



theorem theorem_653850_problem (f : ℝ → ℝ)
  (h1 : ∀ x, DifferentiableAt ℝ f x)
  (h2 : Continuous (deriv f)) :
  ∀ x, DifferentiableAt ℝ f x := by
  sorry

theorem theorem_653558_problem
  (f G : ℝ → ℝ)
  (D : Set ℝ)
  (is_antiderivative : (ℝ → ℝ) → (ℝ → ℝ) → Set ℝ → Prop)
  (h_def : ∀ (F h : ℝ → ℝ) (S : Set ℝ), is_antiderivative F h S ↔ ∀ x ∈ S, deriv F x = h x) :
  is_antiderivative G f D ↔ ∀ x ∈ D, deriv G x = f x := by
  sorry



theorem theorem_653567_problem (a b c : ℕ)
  (h1 : a ≤ 30)
  (h2 : b ≤ 30)
  (h3 : c ≤ 30)
  (h4 : 1 + 2^a = 4 * 3^b + 5^c) :
  (a, b, c) = (2, 0, 0) ∨
  (a, b, c) = (3, 0, 1) ∨
  (a, b, c) = (4, 1, 1) ∨
  (a, b, c) = (7, 0, 3) ∨
  (a, b, c) = (12, 5, 5) := by
  sorry

theorem theorem_653799_problem (n : ℕ) (M : Type*) [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [SmoothManifoldWithCorners (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M] :
  ∀ x : M, FiniteDimensional.finrank ℝ (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x) = n := by
  sorry

theorem theorem_653562_problem (x y : ℕ)
  (h : x^3 - x^2 + x = 3 * y^3) :
  x = 0 ∧ y = 0 := by
  sorry





theorem theorem_653540_problem
  {α : Type*}
  (k : ℕ)
  (A : Fin k → Set α)
  (hk : k > 0)
  (hA : ∀ i, Nonempty (A i ≃ ℕ)) :
  Nonempty ((⋃ i, A i) ≃ ℕ) := by
  sorry

theorem theorem_654324_problem
  (K : Type*) [Field K]
  (E : Type*) [AddCommGroup E] [Module K E]
  (h_inf : ¬ Module.Finite K E) :
  ∃ (F G : Submodule K E), (Nonempty ((E ⧸ F) ≃ₗ[K] G)) ∧ ¬ (Nonempty ((E ⧸ G) ≃ₗ[K] F)) := by
  sorry











theorem theorem_654408_problem (a b c d x2 y2 u : ℝ)
  (hx : 0 < x2 ∧ x2 < c)
  (hy : 0 < y2 ∧ y2 < d)
  (h1 : ((c - x2) * x2) / ((d - y2) * y2) = a)
  (h2 : (c - x2) / (d - y2) + x2 / y2 = b)
  (hu : u = (d - y2) / (c - x2)) :
  a * u^2 - b * u + 1 = 0 := by
  sorry

theorem theorem_653668_problem 
  (a b : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) 
  (h_neq : a ≠ b) :
  let r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → Prop := 
    fun x y ↦ x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)
  let X := Quot r
  let x₀ : X := Quot.mk r a
  Nonempty (FundamentalGroup X x₀ ≃* Multiplicative ℤ) := by
  sorry

theorem theorem_652954_problem (n p : ℕ)
  (hp : Nat.Prime p)
  (hn : n ≥ 3)
  (h1 : 4 * n < 5 * p)
  (h2 : p ≤ n) :
  ¬ (p ∣ Nat.choose (4 * n) (3 * n)) := by
  sorry











theorem theorem_654434_problem (n : ℕ)
  (T : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2)
  (hT : ∀ (x : lp (fun _ : ℕ => ℝ) 2) (i : ℕ), T x i = if i < n then 0 else x i) :
  ‖T‖ = 1 := by
  sorry

theorem theorem_654215_problem
  (n k : ℕ)
  (α : Type*) [Fintype α] [DecidableEq α]
  (h_card : Fintype.card α = n)
  (hk_ge : 2 ≤ k)
  (hk_le : k ≤ n)
  (pat : List α)
  (h_pat_len : pat.length = k)
  (h_pat_nodup : pat.Nodup) :
  let all_perms := (Finset.univ : Finset α).toList.permutations
  let fav_perms := all_perms.filter (fun l ↦ pat <:+ l)
  (all_perms.length : ℚ) / fav_perms.length = (Nat.factorial n : ℚ) / Nat.factorial (n + 1 - k) := by
  sorry

theorem theorem_655012_problem (n beta : ℤ)
  (hn : n > 0)
  (hbeta_nz : beta ≠ 0)
  (hcoprime : Int.gcd beta n = 1) :
  ∃! x : ℤ, 0 ≤ x ∧ x < n ∧ beta * x ≡ 1 [ZMOD n] := by
  sorry

theorem theorem_654950_problem {S : Type*} (A B : Set S) :
  ∃! C : Set S, ∀ x, x ∈ C ↔ x ∈ A ∨ x ∈ B := by
  sorry





theorem theorem_653865_problem (n : ℕ) (X : Fin n → ℝ) (μ x_bar : ℝ)
  (hn : 0 < n)
  (h_x_bar : x_bar = (∑ i, X i) / n) :
  ∑ i, |X i - x_bar|^3 ≤ 2^3 * ((∑ i, |X i - μ|^3) + (n : ℝ) * |μ - x_bar|^3) := by
  sorry

theorem theorem_654829_problem (m : ℝ) (χ1 : ℝ → ℝ) 
  (α1 α2 γ1 γ2 : ℝ) 
  (h : α1 ^ 3 / γ1 + α2 ^ 3 / γ2 + 1 > 0) : 
  χ1 (m ^ (1 / 3 : ℝ)) > 0 := by
  sorry











theorem theorem_655177_problem 
  (Statement : Type)
  (provable : Statement → Prop)
  (is_true : Statement → Prop)
  (not : Statement → Statement)
  (iff : Statement → Statement → Statement)
  (bew : Statement → Statement)
  -- Condition: F is consistent
  (h_cons : ∀ s, ¬ (provable s ∧ provable (not s)))
  -- Condition: F expresses elementary arithmetic (Implies Derivability of Bew and Fixed Point Lemma)
  (h_deriv_bew : ∀ s, provable s → provable (bew s))
  (h_fixed_point : ∃ p, provable (iff p (not (bew p))))
  -- Logical properties of F needed for the proof
  (h_iff_elim : ∀ p q, provable (iff p q) → (provable p ↔ provable q))
  -- Condition: Truth in the standard model (Soundness and semantic definitions)
  (h_sound : ∀ s, provable s → is_true s)
  (h_truth_not : ∀ s, is_true (not s) ↔ ¬ is_true s)
  (h_truth_iff : ∀ p q, is_true (iff p q) ↔ (is_true p ↔ is_true q))
  (h_truth_bew : ∀ s, is_true (bew s) ↔ provable s) :
  ∃ p, is_true p ∧ ¬ provable p := by
  sorry







theorem theorem_654762_problem (p : ℕ) (n_n d_n : ℤ)
  (hp : p.Prime)
  (hp3 : p > 3)
  (h_coprime : Int.gcd n_n d_n = 1)
  (h_eq : (n_n : ℚ) / d_n = ∑ k in Finset.Ico 1 p, (1 / (k : ℚ))) :
  (p : ℤ)^2 ∣ n_n := by
  sorry

theorem theorem_654582_problem :
  ∃ (R : Type) (_ : CommRing R) (K I : Ideal R),
    I.IsPrincipal ∧ K ≤ I ∧ K ≠ ⊤ ∧ ¬ (I.map (Ideal.Quotient.mk K)).IsPrime := by
  sorry



