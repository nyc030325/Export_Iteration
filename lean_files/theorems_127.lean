import Mathlib
import Mathlib.Tactic

theorem theorem_690245_problem (c v : ℝ) (hc : c > 0) (hv : |v| < c)
  (x₁ y₁ z₁ t₁ x₂ y₂ z₂ t₂ : ℝ) :
  let γ := 1 / Real.sqrt (1 - v^2 / c^2)
  let x₁' := γ * (x₁ - v * t₁)
  let y₁' := y₁
  let z₁' := z₁
  let t₁' := γ * (t₁ - (v / c^2) * x₁)
  let x₂' := γ * (x₂ - v * t₂)
  let y₂' := y₂
  let z₂' := z₂
  let t₂' := γ * (t₂ - (v / c^2) * x₂)
  let s_sq := (x₂ - x₁)^2 + (y₂ - y₁)^2 + (z₂ - z₁)^2 - c^2 * (t₂ - t₁)^2
  let s_prime_sq := (x₂' - x₁')^2 + (y₂' - y₁')^2 + (z₂' - z₁')^2 - c^2 * (t₂' - t₁')^2
  s_sq = s_prime_sq := by
  sorry



theorem theorem_690483_problem (r : ℕ) (f : ℝ → ℝ)
  (h : ∀ x, f x = (∏ i in Finset.range r, (x - (i : ℝ))) / (r.factorial : ℝ)) :
  ConvexOn ℝ (Set.Ioi ((r : ℝ) - 1)) f := by
  sorry

theorem theorem_690441_problem (x y : ℝ) :
  |x * Real.sin y| ≤ (1 / 2) * |x|^2 + (1 / 2) * |y|^2 := by
  sorry









theorem theorem_689991_problem :
  ∃ (n : ℕ) (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ),
    Convex ℝ C ∧
    ¬ ConvexOn ℝ C f ∧
    x ∈ C ∧
    IsLocalMinOn f C x ∧
    ¬ (∀ y ∈ C, f x ≤ f y) := by
  sorry

theorem theorem_690636_problem (a : ℕ → ℝ)
  (h_pos : ∀ n, 0 < a n)
  (h_dec : ∀ n, a (n + 1) ≤ a n)
  (h_lim_ratio : Filter.Tendsto (fun n ↦ a (n + 1) / a n) Filter.atTop (nhds 0)) :
  Filter.Tendsto a Filter.atTop (nhds 0) := by
  sorry



theorem theorem_690683_problem
  {X : Type*} [TopologicalSpace X]
  (Y : Set X)
  (C : Set Y)
  (hC : IsClosed C) :
  closure C = C := by
  sorry

theorem theorem_691188_problem (k : ℝ) (z : ℝ → ℝ) (y : ℝ → ℝ)
  (hk : 0 < k) (hk_ne_1 : k ≠ 1)
  (hz : Continuous z)
  (hy : Differentiable ℝ y)
  (h1 : ∀ t, deriv y t + k ^ t * y t = k ^ Real.exp 1 * z t)
  (h2 : y 0 = 0) :
  ∀ t, y t = Real.exp (-(k ^ t) / Real.log k) * 
    ∫ s in (0)..t, Real.exp ((k ^ s) / Real.log k) * k ^ Real.exp 1 * z s := by
  sorry





theorem theorem_690467_problem
  {ι : Type*} [Fintype ι]
  (A : ι → Type*) [∀ i, Field (A i)]
  (I : Ideal ((i : ι) → A i))
  (hI : I.IsMaximal) :
  ∃ i : ι, I = RingHom.ker (Pi.evalRingHom (f := A) i) := by
  sorry

theorem theorem_690418_problem :
  ∫ x in (0 : ℝ)..Real.pi, (Real.cos x)^4 / (1 + (Real.sin x)^2) =
  (Real.pi / 2) * (4 * Real.sqrt 2 - 5) := by
  sorry

theorem theorem_691165_problem (k : ℕ) (n : Fin k → ℕ) (hn : ∀ j, 0 < n j) :
  Set.BijOn (fun (i : (j : Fin k) → Fin (n j)) ↦
    ∑ j : Fin k, (i j : ℕ) * ∏ p in Finset.Iio j, n p)
    Set.univ
    {x : ℕ | x < ∏ j : Fin k, n j} := by
  sorry

theorem theorem_690965_problem (k : ℕ) (Y : ℤ → ℤ → ℝ) (t : ℝ)
  (hk : k > 0)
  (hY : ∀ m n : ℤ, m < 1 ∨ m > k + 1 ∨ n < 1 ∨ n > k + 1 → Y m n = 0) :
  ∑ i in Finset.Icc 1 (2 * k + 1), (∑ m in Finset.Icc 1 (k + 1), ∑ n in Finset.Icc 1 (k + 1),
    if (n : ℤ) = (i : ℤ) + 1 - (m : ℤ) then Y m n * t ^ (i - 1) else 0) =
  ∑ m in Finset.Icc 1 (k + 1), ∑ n in Finset.Icc 1 (k + 1), ∑ i in Finset.Icc (m + n - 1) (2 * k + 1),
    if (n : ℤ) = (i : ℤ) + 1 - (m : ℤ) then Y m n * t ^ (i - 1) else 0 := by
  sorry

theorem theorem_691135_problem 
  (n : ℕ) (d : ℤ)
  (VectorBundle : Type*)
  (rank : VectorBundle → ℕ)
  (degree : VectorBundle → ℤ)
  (is_semistable : VectorBundle → Prop)
  (is_direct_sum_of_line_bundles : VectorBundle → Prop)
  (U_X : Set VectorBundle)
  (h_U_def : U_X = { E | is_semistable E ∧ rank E = n ∧ degree E = d })
  (h_nd : ¬ (n : ℤ) ∣ d) :
  ∀ E ∈ U_X, ¬ is_direct_sum_of_line_bundles E := by
  sorry









theorem theorem_691331_problem (A : ℕ → ℝ)
  (h_recurrence : ∀ n : ℕ, 1 ≤ n → A n = (3 * (n : ℝ) + 2) / (3 * (n : ℝ) - 2 + A (n + 1))) :
  ∀ n : ℕ, 1 ≤ n → A n = ((n : ℝ) + 1) / (n : ℝ) := by
  sorry

theorem theorem_691530_problem
  (m n : ℕ)
  (a b : ℤ → ℝ)
  (ha : ∀ i, i < -(m : ℤ) → a i = 0)
  (hb : ∀ j, j < -(n : ℤ) → b j = 0)
  (k : ℤ) :
  let S_k : Set (ℤ × ℤ) := {x | x.1 + x.2 = k ∧ -(m : ℤ) ≤ x.1 ∧ x.1 ≤ k + (n : ℤ) ∧ -(n : ℤ) ≤ x.2 ∧ x.2 ≤ k + (m : ℤ)}
  ∃ h : S_k.Finite, (∑' i, a i * b (k - i)) = ∑ x in h.toFinset, a x.1 * b x.2 := by
  sorry



theorem theorem_691603_problem (x : ℝ) (h : 3 < x ^ 3) :
  HasDerivAt (fun u => 2 / 27 * (1 - 3 / u ^ 3) ^ (3 / 2 : ℝ)) 
    (Real.sqrt ((x ^ 3 - 3) / x ^ 11)) x := by
  sorry

theorem theorem_691552_problem (X : Set ℂ) 
  (hX : X = Metric.ball 0 1 ∪ Metric.ball 3 1) :
  ∃ (f : ℂ → ℂ) (c : ℝ), (∀ z ∈ X, (f z).im = c) ∧ ¬ (∀ a b, a ∈ X → b ∈ X → f a = f b) := by
  sorry









theorem theorem_691988_problem (p n : ℕ) (hp : Nat.Prime p) (hn : n > 0) :
  Nonempty (
    ((Fin n → ℤ) ⧸ (AddSubgroup.pi Set.univ (fun _ ↦ AddSubgroup.zmultiples (p : ℤ)))) 
    ≃+ (Fin n → ZMod p)
  ) := by
  sorry



theorem theorem_691485_problem (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (a : L) :
  let P := LinearMap.charpoly (Algebra.lmul K L a)
  let E := P.SplittingField
  algebraMap K E (LinearMap.trace K L (Algebra.lmul K L a)) = (P.map (algebraMap K E)).roots.sum := by
  sorry



theorem theorem_692042_problem (n m a b : ℕ) :
  ∑ k in Finset.Icc ((b : ℤ) - m) ((n : ℤ) - a), 
    (Nat.choose ((n : ℤ) - k).toNat a) * (Nat.choose ((m : ℤ) + k).toNat b) = 
  Nat.choose (n + m + 1) (a + b + 1) := by
  sorry







theorem theorem_692048_problem
  {X : Type*} [MetricSpace X]
  (E : Set X) (S : Set X)
  (hE_compact : IsCompact E)
  (hS_subset : S ⊆ E)
  (hS_infinite : S.Infinite) :
  ∃ x ∈ E, ∀ U, IsOpen U → x ∈ U → (S ∩ U).Infinite := by
  sorry



theorem theorem_691815_problem
  (f g : ℝ → ℝ)
  (hf_supp : ∀ y < 0, f y = 0)
  (hf_cont : Continuous f)
  (hg_diff : ContDiff ℝ 1 g)
  (x : ℝ) :
  deriv (fun t => ∫ y in (0:ℝ)..t, f y * g (t - y)) x =
  (∫ y in (0:ℝ)..x, f y * (deriv g (x - y))) + f x * g 0 := by
  sorry









theorem theorem_692803_problem {α β : Type*}
  (U V : Set α) (A : Set β)
  (W Z : Set (α × β))
  (hU : U ≠ ∅)
  (hV : V ≠ ∅)
  (h_disj : U ∩ V = ∅)
  (hW : W = U ×ˢ A)
  (hZ : Z = V ×ˢ A) :
  W ∩ Z = ∅ := by
  sorry









theorem theorem_693214_problem (a b c : ℝ) (ha : 0 < a) :
  Filter.Tendsto (fun x ↦ (1 + 1 / x) ^ Real.sqrt (a * x^2 + b * x + c)) Filter.atTop (nhds (Real.exp (Real.sqrt a))) := by
  sorry

theorem theorem_693178_problem (B m k : ℕ)
  (hB : 1 < B) (hm : 0 < m)
  (n1 n2 : Fin k → ℕ)
  (h1 : ∀ i, n1 i < B ^ m)
  (h2 : ∀ i, n2 i < B ^ m)
  (h_eq : (∑ i : Fin k, n1 i * B ^ (m * (k - 1 - (i : ℕ)))) =
          (∑ i : Fin k, n2 i * B ^ (m * (k - 1 - (i : ℕ))))) :
  n1 = n2 := by
  sorry

theorem theorem_693061_problem
  {P₁ P₂ : Type*} [PartialOrder P₁] [PartialOrder P₂]
  (e : P₁) (f : P₂) :
  (∀ x : P₁ × P₂, x ≤ (e, f) → x = (e, f)) ↔
  ((∀ e' : P₁, e' ≤ e → e' = e) ∧ (∀ f' : P₂, f' ≤ f → f' = f)) := by
  sorry







theorem theorem_693120_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [CommRing R]
  (A B C : Matrix n n R)
  (hAB : A * B = B * A)
  (hBC : B * C = C * B)
  (hCA : C * A = A * C) :
  (A + B + C) ^ 3 = A ^ 3 + B ^ 3 + C ^ 3 +
    3 * A ^ 2 * B + 3 * A * B ^ 2 +
    3 * A ^ 2 * C + 3 * A * C ^ 2 +
    3 * B ^ 2 * C + 3 * B * C ^ 2 +
    6 * A * B * C := by
  sorry













theorem theorem_693982_problem
  (α : Type*)
  (a : ℕ → Set α)
  (h_pairwise_disjoint : Pairwise (fun i j => Disjoint (a i) (a j)))
  (h_nonempty : ∀ i, (a i).Nonempty)
  (F : Set (Set α))
  (h_F_def : F = { S | ∃ I : Set ℕ, S = ⋃ i ∈ I, a i }) :
  ¬ F.Countable := by
  sorry

theorem theorem_693435_problem (P Q : AffineSubspace ℝ (ℝ × ℝ))
  (hP : FiniteDimensional.finrank ℝ P.direction = 1)
  (hQ : FiniteDimensional.finrank ℝ Q.direction = 1)
  (h_distinct : P ≠ Q)
  (h_inter : ∃ x, x ∈ P ∧ x ∈ Q) :
  ∃! R, R ∈ P ∧ R ∈ Q := by
  sorry

theorem theorem_693659_problem
  (Obj : Type)
  (Elem : Obj → Obj → Prop)
  (IsSet : Obj → Prop)
  (IsUrelement : Obj → Prop)
  (Subset : Obj → Obj → Prop)
  (IsTransitive : Obj → Prop)
  -- Definition: An urelement is an object that is not a set.
  (h_urelement_def : ∀ x, IsUrelement x ↔ ¬ IsSet x)
  -- Definition: Subset relation (valid only for sets, per problem context)
  (h_subset_def : ∀ A B, Subset A B ↔ IsSet A ∧ ∀ x, Elem x A → Elem x B)
  -- Definition: A set S is transitive if x ∈ S implies x ⊆ S
  (h_transitive_def : ∀ S, IsTransitive S ↔ IsSet S ∧ ∀ x, Elem x S → Subset x S)
  (S u : Obj)
  (hS_set : IsSet S)
  (hu_in_S : Elem u S)
  (hu_urelement : IsUrelement u) :
  ¬ IsTransitive S := by
  sorry

theorem theorem_694075_problem (y : ℝ → ℝ) (hy : ContDiff ℝ ⊤ y) :
  (∀ x, iteratedDeriv 8 y x - 6 * iteratedDeriv 7 y x + 18 * iteratedDeriv 6 y x - 54 * iteratedDeriv 5 y x + 81 * iteratedDeriv 4 y x = 0) ↔
  (∃ c1 c2 c3 c4 c5 c6 c7 c8 : ℝ, ∀ x,
    y x = c1 + c2 * x + c3 * x^2 + c4 * x^3 + 
          c5 * Real.exp (3 * x) + c6 * x * Real.exp (3 * x) + 
          c7 * Real.cos (3 * x) + c8 * Real.sin (3 * x)) := by
  sorry

theorem theorem_693959_problem (y : ℝ → ℝ)
  (h_diff : ContDiff ℝ 2 y)
  (h_eq : ∀ x, y x * deriv (deriv y) x = 1 + (deriv y x) ^ 2) :
  deriv (fun x => y x / Real.sqrt (1 + (deriv y x) ^ 2)) = 0 := by
  sorry





theorem theorem_693648_problem (t : ℝ) (h : t > 2) :
  HasDerivAt result_function (1 / (t^2 * Real.sqrt (t - 2))) t := by
  sorry

theorem theorem_694168_problem
  {X : Type*}
  -- Assumptions for Commutative Banach Lattice Algebra
  [NormedCommRing X] [NormedAlgebra ℝ X] [CompleteSpace X] [Lattice X]
  -- f is defined on X, but we only care about its behavior and differentiability on strictly positive elements
  (f : X → ℝ)
  -- The condition "positivity is defined as strictly positive" implies the domain is {y | 0 < y}
  (hf : DifferentiableOn ℝ f {y : X | 0 < y})
  -- x is strictly positive
  (x : X) (hx : 0 < x) :
  -- The expression f'(x) * x⁻¹ is well-defined iff x is invertible (since f' exists by differentiability)
  IsUnit x := by
  sorry





theorem theorem_693968_problem :
  ∃ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ),
    A.IsSymm ∧ B.IsSymm ∧ B.PosDef ∧ ¬ A.PosDef := by
  sorry

theorem theorem_694286_problem (n : ℕ) (a : Fin (n + 1) → ℝ) (c : ℝ)
  (hc : c ≠ 0)
  (ha : a 0 ≠ 0) :
  c * a 0 ≠ 0 := by
  sorry







theorem theorem_694736_problem {X : Type*} [MetricSpace X] (A : Set X) (h : IsConnected A) :
  IsConnected (closure A) := by
  sorry

theorem theorem_694464_problem (G : Type*) [Group G] :
  let R : G → (G → ℂ) →ₗ[ℂ] (G → ℂ) := fun g ↦
    { toFun := fun f x ↦ f (x * g)
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun _ _ ↦ by ext; simp }
  LinearIndependent ℂ R := by
  sorry







theorem theorem_694579_problem (t n : ℕ) (ht : t > 0) (hn : n > 0) (h : t ∣ n) :
  (2^t - 1) ∣ (2^n - 1) := by
  sorry

theorem theorem_694791_problem : Complex.exp (Complex.I * ↑Real.pi) + 1 = 0 := by
  sorry

theorem theorem_693389_problem (n : ℕ) (x v : Fin n → ℝ) (r : ℝ)
  (n_ast n_dag : (Fin n → ℝ) → ℝ)
  (hr : r > 0)
  -- n_ast is a norm
  (h_ast_pos : ∀ w, 0 ≤ n_ast w)
  (h_ast_zero : ∀ w, n_ast w = 0 ↔ w = 0)
  (h_ast_smul : ∀ (c : ℝ) w, n_ast (c • w) = |c| * n_ast w)
  (h_ast_tri : ∀ w1 w2, n_ast (w1 + w2) ≤ n_ast w1 + n_ast w2)
  -- n_dag is a norm
  (h_dag_pos : ∀ w, 0 ≤ n_dag w)
  (h_dag_zero : ∀ w, n_dag w = 0 ↔ w = 0)
  (h_dag_smul : ∀ (c : ℝ) w, n_dag (c • w) = |c| * n_dag w)
  (h_dag_tri : ∀ w1 w2, n_dag (w1 + w2) ≤ n_dag w1 + n_dag w2)
  -- n_ast is strictly convex
  (h_ast_strict_cvx : ∀ w1 w2, n_ast w1 = 1 → n_ast w2 = 1 → w1 ≠ w2 → 
    ∀ t, 0 < t → t < 1 → n_ast (t • w1 + (1 - t) • w2) < 1)
  -- n_dag satisfies monotonicity with respect to components
  (h_dag_mono : ∀ w1 w2, (∀ i, |w1 i| ≤ |w2 i|) → n_dag w1 ≤ n_dag w2) :
  sInf ((fun w ↦ n_dag (w - x)) '' {w | n_ast (w - v) = r}) ≤ |n_dag (x - v) - r| := by
  sorry



theorem theorem_694557_problem
  {E : Type*} [NormedAddCommGroup E]
  (f₁ f₂ : E → ℝ)
  (L₁ L₂ : ℝ)
  (h₁ : ∀ x y, |f₁ x - f₁ y| ≤ L₁ * ‖x - y‖)
  (h₂ : ∀ x y, |f₂ x - f₂ y| ≤ L₂ * ‖x - y‖) :
  ∀ x y, |max (f₁ x) (f₂ x) - max (f₁ y) (f₂ y)| ≤ (L₁ + L₂) * ‖x - y‖ := by
  sorry







theorem theorem_694975_problem
  (m n : ℕ)
  (hn : 0 < n)
  (K_n : Set (Fin m → ℝ))
  (hK_n_finite : K_n.Finite)
  (h_sum : ∀ k ∈ K_n, ∑ i, k i = n)
  (h_nonneg : ∀ k ∈ K_n, ∀ i, 0 ≤ k i) :
  {y | ∃ k ∈ K_n, y = (n : ℝ)⁻¹ • k} ⊆ {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1} := by
  sorry

theorem theorem_695447_problem (s : ℕ → ℝ) (t : ℕ → ℝ) (α : ℝ)
  (h_def : ∀ N, 1 ≤ N → t N = sSup (s '' {n | n > N}))
  (h_cond : ∀ N, 1 ≤ N → sSup (s '' {n | n > N}) > α) :
  α ∈ lowerBounds (t '' {N | 1 ≤ N}) := by
  sorry

theorem theorem_694923_problem 
  (U : Type) 
  (mem : U → U → Prop) 
  (S : U) 
  (h_foundation : ∀ x : U, ¬ mem x x) : 
  ¬ ∃ R : U, ∀ x : U, mem x R ↔ ¬ mem x x := by
  sorry





