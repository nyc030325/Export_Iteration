import Mathlib
import Mathlib.Tactic

theorem theorem_803497_problem
  {A : Type*} [Ring A] [Algebra ℝ A] [Nontrivial A]
  (x : A) (hx : IsUnit x)
  (a : ℝ) (n : ℕ)
  (L : A →ₗ[ℝ] A)
  (hL_def : ∀ u, L u = x * u * Ring.inverse x)
  (h_cond : (L - a • LinearMap.id) ^ n = 0) :
  ∃ u : A, u ≠ 0 ∧ x * u * Ring.inverse x = a • u := by
  sorry







theorem theorem_804337_problem (n : ℕ) (x y : Fin n → ℝ)
  (ones : Fin n → ℝ) (h_ones : ones = fun _ ↦ 1)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (h_A : A = Matrix.vecMulVec x y + Matrix.vecMulVec ones ones - (1 : Matrix (Fin n) (Fin n) ℝ)) :
  A.det = (-1 : ℝ) ^ (n + 1) * (((n : ℝ) - 1) * (1 - Matrix.dotProduct y x) + (Matrix.dotProduct ones x) * (Matrix.dotProduct ones y)) := by
  sorry











theorem theorem_804873_problem
  (M : ℕ)
  (α : Fin (M + 1) → ℝ)
  (h_distinct : Function.Injective α)
  (h_range : ∀ i, α i ∈ Set.Icc (-1 : ℝ) 1) :
  LinearIndependent ℝ (fun (n : ℕ) => (fun (x : ℝ) => Real.sin x ^ n)) := by
  sorry

theorem theorem_804879_problem
  {Ω : Type*} [Fintype Ω]
  (π : Ω → ℝ)
  (hπ_ne_zero : ∀ x, π x ≠ 0)
  (H : Ω → Ω → ℝ)
  (h0 : Ω → ℝ)
  (H_adj : Ω → Ω → ℝ)
  (h_adj_def : ∀ x y, H_adj x y = (π y * H y x) / π x)
  (ht : Ω → ℝ)
  (h_ht_def : ∀ x, ht x = (∑ y : Ω, π y * H y x * h0 y) / π x) :
  ∀ x, ht x = ∑ y : Ω, H_adj x y * h0 y := by
  sorry



theorem theorem_804824_problem
  (A B C : Type*) [Group A] [Group B] [Group C]
  (f : A →* B) (g : B →* C)
  (h_inj : Function.Injective f)
  (h_surj : Function.Surjective g)
  (h_exact : MonoidHom.range f = MonoidHom.ker g) :
  Nonempty (C ≃* B ⧸ MonoidHom.ker g) := by
  sorry







theorem theorem_805572_problem (X : Type*) [TopologicalSpace X]
  (B : Set (Set X)) (h_base : TopologicalSpace.IsTopologicalBasis B) (h_count : Set.Countable B) :
  ∃ A : Set X, Set.Countable A ∧ Dense A := by
  sorry



theorem theorem_805717_problem
  (T : ℕ → ℕ → ℕ → ℕ)
  (G : ℕ → ℕ → ℕ)
  (hT_zero : ∀ b c, T b c 0 = 0)
  (hT_pos : ∀ b c n, 1 < b → 0 < n →
    T b c n = (n / b ^ (Nat.log b n)) * c ^ (T b c (Nat.log b n)) + T b c (n % b ^ (Nat.log b n)))
  (hG_zero : ∀ m, G m 0 = m)
  (hG_step : ∀ m n, G m (n + 1) = T (n + 2) (n + 3) (G m n) - 1)
  (m : ℕ) :
  ∃ n, G m n = 0 := by
  sorry



theorem theorem_804733_problem (i n : ℕ) (hi : i ≥ 1) (hn : n ≥ 1) :
  let V : Set (ℕ × ℕ) := {v | 1 ≤ v.1 ∧ v.2 ≤ v.1}
  let adj (v w : ℕ × ℕ) : Prop :=
    v ∈ V ∧ w ∈ V ∧
    ((v.1 = w.1 ∧ ((v.2 = 0 ∧ w.2 ≠ 0) ∨ (v.2 ≠ 0 ∧ w.2 = 0))) ∨
     (v.2 = 0 ∧ w.2 = 0 ∧ (v.1 = w.1 + 1 ∨ w.1 = v.1 + 1)))
  let is_path (p : List (ℕ × ℕ)) : Prop :=
    p ≠ [] ∧ p.Chain' adj ∧ p.Nodup ∧ ∀ v ∈ p, v ∈ V
  let stars_traversed (p : List (ℕ × ℕ)) : ℕ :=
    (p.map Prod.fst).toFinset.card
  let valid_paths := {p | is_path p ∧ p.head?.map Prod.fst = some i ∧ stars_traversed p = n}
  Set.Finite valid_paths ∧ Set.ncard valid_paths ≤ 2 * (i + n)^2 := by
  sorry





theorem theorem_805694_problem
  {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (F G J : E → U → ℝ)
  (h_def : ∀ x u, J x u = F x u + G x u)
  (h_not_free : ∀ u, ∀ x₁ x₂ : E, J x₁ u = J x₂ u) :
  ∀ x u, fderiv ℝ (fun y => J y u) x = 0 := by
  sorry







theorem theorem_806202_problem (n K : ℕ) (hn : n > 0) (hK : K > 0) :
  ∃ S : Finset (Fin n → ℕ),
    (∀ x, x ∈ S ↔ ∑ i, x i = K) ∧
    S.card = Nat.choose (n + K - 1) (n - 1) := by
  sorry

theorem theorem_805953_problem (r rv delta : ℝ)
  (hr : r ≠ 0) (hrv : rv ≠ 0) :
  (rv^2 + r^2 - 2 * r * rv * Real.cos delta) / (1 + (r * rv)^2 - 2 * r * rv * Real.cos delta) =
  Complex.abs ((r - rv * Complex.exp (Complex.I * delta)) / (r * rv - Complex.exp (Complex.I * delta))) ^ 2 := by
  sorry

theorem theorem_806523_problem (t : ℝ) (ht : t ≠ 0) (h : ℝ → ℝ)
  (h_diff : DifferentiableAt ℝ h (1 / t)) :
  deriv h (1 / t) = -t ^ 2 * deriv (fun s => h (1 / s)) t := by
  sorry



theorem theorem_806295_problem
  (a b : ℝ)
  (f p : ℝ → ℝ)
  (hf : IntervalIntegrable f volume a b)
  (hp : IntervalIntegrable p volume a b)
  (h_pdf : ∫ x in a..b, f x = 1)
  (F : ℝ → ℝ)
  (hF : ∀ y, F y = ∫ x in a..y, f x) :
  ∫ y in a..b, (1 - F y) * p y = ∫ y in a..b, ∫ x in y..b, f x * p y := by
  sorry











theorem theorem_806858_problem :
  IntermediateField.adjoin ℚ {Real.sqrt 2, Real.sqrt 3} =
  IntermediateField.adjoin ℚ {Real.sqrt 2, Real.sqrt 6} := by
  sorry



theorem theorem_806242_problem
  (Ω0 Ω1 Ω2 : Type*) -- Abstract types for 0-forms, 1-forms, and 2-forms
  (d : Ω1 → Ω2) -- Exterior derivative
  (wedge : Ω1 → Ω1 → Ω2) -- Wedge product
  (smul : Ω0 → Ω2 → Ω2) -- Scalar multiplication of a function on a 2-form
  (ω1 ω2 ω3 : Ω1) -- The forms
  (K : Ω0) -- Gaussian curvature function
  (Ω : Ω2) -- The curvature form
  -- Condition: ω3 is the Levi-Civita connection form implies first structure equations
  (h_struct1 : d ω1 = wedge ω2 ω3)
  (h_struct2 : d ω2 = wedge ω3 ω1)
  -- Condition: Cartan's second structure equation defines the curvature form Ω on a surface
  (h_struct3 : Ω = d ω3)
  -- Condition: The relationship between the curvature form and Gaussian curvature K
  (h_gauss_def : Ω = smul K (wedge ω1 ω2)) :
  -- Conclusion: The formula for Gaussian curvature
  d ω3 = smul K (wedge ω1 ω2) := by
  sorry



theorem theorem_807216_problem
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : E → ℝ) (g : E → F)
  (ρ : ℕ → ℝ) (x : ℕ → E) (x_dagger : E)
  (hf : Continuous f)
  (hg : Continuous g)
  (hρ_pos : ∀ n, 0 < ρ n)
  (hρ_inf : Filter.Tendsto ρ Filter.atTop Filter.atTop)
  (h_opt : ∀ n y, f (x n) + ρ n * ‖g (x n)‖ ≤ f y + ρ n * ‖g y‖)
  (h_lim : Filter.Tendsto x Filter.atTop (nhds x_dagger)) :
  g x_dagger = 0 ∧ ∀ y, g y = 0 → f x_dagger ≤ f y := by
  sorry

theorem theorem_807165_problem (A : Matrix (Fin 2) (Fin 2) ℝ) :
  (Matrix.charpoly A).degree = 2 := by
  sorry

theorem theorem_807157_problem
  {V : Type*}
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  (T : V →ₗ[ℝ] ℝ) :
  ∃! w : V, ∀ v : V, T v = inner w v := by
  sorry

theorem theorem_807181_problem :
  let G := ZMod 4 × ZMod 6
  let H : AddSubgroup G := AddSubgroup.closure {((0 : ZMod 4), (2 : ZMod 6))}
  Nonempty ((G ⧸ H) ≃+ (ZMod 4 × ZMod 2)) := by
  sorry



theorem theorem_807088_problem
  (a b : ℝ) (h_ab : a < b)
  (f : ℝ → ℝ) (h_diff : DifferentiableOn ℝ f (Set.Icc a b))
  (M : ℝ) (h_M : IsGreatest ((deriv f) '' (Set.Icc a b)) M) :
  ∃ m : ℝ, m > M ∧ ∃ c : ℝ, ∀ x ∈ Set.Icc a b, m * x + c > f x := by
  sorry



theorem theorem_807246_problem (t u x y : ℝ)
  (ht : t ≠ -1)
  (hx : x = (t^2 - 9) / 8)
  (hy : y = -(t^2 - 9) / (2 * (t + 1)))
  (hu : u = t + 1) :
  x = (u^2 - 2 * u - 8) / 8 ∧ y = (8 - u^2 + 2 * u) / (2 * u) := by
  sorry



theorem theorem_807032_problem (x : ℝ) :
  (∑' n : ℕ, if n = 0 then 0 else ((-1 : ℝ) ^ n * x ^ (4 * (n - 1))) / (Nat.factorial (2 * n) : ℝ)) =
  ∑' n : ℕ, ((-1 : ℝ) ^ (n + 1) * x ^ (4 * n)) / (Nat.factorial (2 * (n + 1)) : ℝ) := by
  sorry

theorem theorem_807477_problem : ¬ Summable (fun n : ℕ => Real.arctan (1 / ((n : ℝ) + 1))) := by
  sorry

theorem theorem_807745_problem {L : FirstOrder.Language} (S : Set (FirstOrder.Language.Sentence L))
  (h : ∀ (Sf : Set (FirstOrder.Language.Sentence L)), Sf ⊆ S → Sf.Finite → FirstOrder.Language.Theory.IsSatisfiable Sf) :
  FirstOrder.Language.Theory.IsSatisfiable S := by
  sorry





theorem theorem_807744_problem
  (f : ℕ → ℝ)
  (h : ∀ n, f n = Real.sin (((n : ℝ) ^ 3 - 9) ^ (1 / 3 : ℝ)) - Real.sin n) :
  Filter.Tendsto f Filter.atTop (nhds 0) := by
  sorry





theorem theorem_807747_problem : Irreducible (X ^ 3 - 2 : Polynomial ℚ) := by
  sorry

theorem theorem_807695_problem
  (a b M : ℝ)
  (f : ℝ → ℝ)
  (h_cont : ContinuousOn f (Set.Icc a b))
  (h_diff : DifferentiableOn ℝ f (Set.Ioo a b))
  (h_bound : ∀ y ∈ Set.Ioo a b, |deriv f y| ≤ M)
  (hM : M > 0)
  (c : ℝ)
  (hc : c ∈ Set.Icc a b)
  (h_min : IsLocalMinOn f (Set.Icc a b) c)
  (x : ℝ)
  (hx : x ∈ Set.Icc a b) :
  f x ≥ f c - M * |x - c| := by
  sorry



theorem theorem_808464_problem (x : ℤ) : ¬ (x ^ 7 ≡ 3 [ZMOD 9]) := by
  sorry

















theorem theorem_808525_problem :
  ¬ ∃ (P : Prop → Prop → Prop → Prop → Prop),
    ∀ (α : Type*) [Nonempty α] (φ ψ : α → Prop),
      P (∀ x, φ x) (∃ x, φ x) (∀ x, ψ x) (∃ x, ψ x) ↔ ∀ x, (φ x ∨ ψ x) := by
  sorry

theorem theorem_809059_problem
  (a b : ℝ) (hab : a < b)
  (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
  -- Sequence of partitions: k(n) intervals, points x(n, i)
  (k : ℕ → ℕ)
  (x : ℕ → ℕ → ℝ)
  (h_start : ∀ n, x n 0 = a)
  (h_end : ∀ n, x n (k n) = b)
  (h_incr : ∀ n, ∀ i, i < k n → x n i < x n (i + 1))
  -- Mesh approaches zero
  (h_mesh : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ i < k n, x n (i + 1) - x n i < ε)
  -- Definition of Piecewise Linear Interpolant L_n
  (L : ℕ → ℝ → ℝ)
  (hL : ∀ n, ∀ i, i < k n → ∀ t ∈ Set.Icc (x n i) (x n (i + 1)),
    L n t = ((x n (i + 1) - t) / (x n (i + 1) - x n i)) * f (x n i) +
            ((t - x n i) / (x n (i + 1) - x n i)) * f (x n (i + 1))) :
  -- Conclusion: Uniform Convergence
  TendstoUniformlyOn L f Filter.atTop (Set.Icc a b) := by
  sorry



theorem theorem_808930_problem
  (ϕ : ℝ → ℝ)
  (h_smooth : ContDiff ℝ 3 ϕ)
  (h_eq : ∀ t : ℝ, deriv ϕ t + ϕ t = ∫ ξ in (0)..t, Real.sin (t - ξ) * ϕ ξ) :
  ∀ t : ℝ, deriv (deriv (deriv ϕ)) t + deriv (deriv ϕ) t + deriv ϕ t = 0 := by
  sorry

theorem theorem_808919_problem 
  (VectorField Function OneForm Tensor : Type*)
  [AddCommGroup OneForm]
  (Ric : VectorField → OneForm)
  (Hess : Function → Tensor)
  (Lap : Function → Function)
  (div_tensor : Tensor → OneForm)
  (div_vec : VectorField → Function)
  (d : Function → OneForm)
  (grad : Function → VectorField)
  (nabla : VectorField → Tensor)
  (f : Function)
  (h_commutation : ∀ Z : VectorField, div_tensor (nabla Z) - d (div_vec Z) = Ric Z)
  (h_hess : Hess f = nabla (grad f))
  (h_lap : Lap f = div_vec (grad f)) :
  div_tensor (Hess f) - d (Lap f) = Ric (grad f) := by
  sorry





theorem theorem_809425_problem {X Y : Type*} (F : X → Y)
  (h : ∃ x1 x2 : X, x1 ≠ x2 ∧ F x1 = F x2) :
  ∃ y : Y, ¬ (∃! x : X, F x = y) := by
  sorry

theorem theorem_809898_problem (a b c n : ℕ)
  (hn : n > 2)
  (ha : a > 0) (hb : b > 0) (hc : c > 0) :
  a ^ n + b ^ n ≠ c ^ n := by
  sorry



theorem theorem_809433_problem
  (f g : ℝ → ℝ → ℝ)
  (h_smooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ ↦ (f p.1 p.2, g p.1 p.2)))
  (hf : ∀ y, 0 ≤ y → f 0 y = 0)
  (hg : ∀ x, 0 ≤ x → g x 0 = 0) :
  (∀ x y : ℝ → ℝ,
    (∀ t, HasDerivAt x (f (x t) (y t)) t) →
    (∀ t, HasDerivAt y (g (x t) (y t)) t) →
    x 0 = 0 → 0 ≤ y 0 →
    ∀ t, x t = 0) ∧
  (∀ x y : ℝ → ℝ,
    (∀ t, HasDerivAt x (f (x t) (y t)) t) →
    (∀ t, HasDerivAt y (g (x t) (y t)) t) →
    y 0 = 0 → 0 ≤ x 0 →
    ∀ t, y t = 0) := by
  sorry

theorem theorem_809250_problem
  (A : Type*) [CommRing A]
  (I : Ideal A)
  (M : Type*) [AddCommGroup M] [Module A M]
  (h_fg : Module.Finite A M)
  (h_eq : I • (⊤ : Submodule A M) = ⊤) :
  ∃ a ∈ I, ∀ m : M, a • m = m := by
  sorry



theorem theorem_809469_problem
  (f : ℝ → ℝ)
  (F : ℝ → ℝ → ℝ)
  (hf : ContDiff ℝ ⊤ f)
  (h_rot : ∀ x z : ℝ, ∃ t : ℝ, 0 ≤ t ∧ x^2 + z^2 = t^2 ∧ F x z = f t) :
  ∀ x z : ℝ, F x z = f (Real.sqrt (x^2 + z^2)) := by
  sorry





theorem theorem_809322_problem :
  ∃ C : Finset (Finset (ℕ × ℕ)), C ⊆ S ∧ C.biUnion id = B ∧
  ∀ C' : Finset (Finset (ℕ × ℕ)), C' ⊆ S → C'.biUnion id = B → C.card ≤ C'.card := by
  sorry











theorem theorem_810018_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
  (F : (x : M) → Module.Dual ℝ (TangentSpace I x))
  (v : (x : M) → TangentSpace I x)
  (P : M → ℝ)
  (h : ∀ x, P x = (F x) (v x))
  (p : M) :
  P p = (F p) (v p) := by
  sorry

theorem theorem_810037_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  -- R is the Riemann curvature tensor (multilinear map with symmetries)
  (R : MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
  (hR_sym1 : ∀ v : Fin 4 → E, R ![v 1, v 0, v 2, v 3] = - R v)
  (hR_sym2 : ∀ v : Fin 4 → E, R ![v 0, v 1, v 3, v 2] = - R v)
  (hR_sym3 : ∀ v : Fin 4 → E, R ![v 2, v 3, v 0, v 1] = R v)
  -- phi and theta are two-forms (antisymmetric bilinear forms)
  (phi theta : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
  (h_phi_anti : ∀ x y, phi x y = - phi y x)
  (h_theta_anti : ∀ x y, theta x y = - theta y x)
  -- The expression is evaluated in two different orthonormal bases
  (b1 b2 : OrthonormalBasis n ℝ E) :
  -- The contraction is invariant (basis independent)
  (∑ i : n, ∑ j : n, ∑ k : n, ∑ l : n, 
     R ![b1 i, b1 j, b1 k, b1 l] * phi (b1 i) (b1 j) * theta (b1 k) (b1 l)) =
  (∑ i : n, ∑ j : n, ∑ k : n, ∑ l : n, 
     R ![b2 i, b2 j, b2 k, b2 l] * phi (b2 i) (b2 j) * theta (b2 k) (b2 l)) := by
  sorry

theorem theorem_810415_problem (A B z : ℂ) 
  (hA : A ≠ 0) (hB : B ≠ 0)
  (hz : Complex.abs z = Complex.abs A * Complex.abs B) :
  ∃ α : ℂ, Complex.abs α = 1 ∧ z = α * (Complex.abs A * Complex.abs B : ℂ) := by
  sorry

theorem theorem_810248_problem
  (A : Type*) [Ring A]
  (P P' : Type*) [AddCommGroup P] [Module A P] [AddCommGroup P'] [Module A P']
  (h : ∀ (V : Type*) [AddCommGroup V] [Module A V],
    Nonempty ((P →ₗ[A] V) ≃+ (P' →ₗ[A] V))) :
  Nonempty (P ≃ₗ[A] P') := by
  sorry



theorem theorem_810394_problem (a : ℕ → ℕ → ℝ)
  (h : Summable (fun x : ℕ × ℕ => if x.2 ≤ x.1 then a x.1 x.2 else 0)) :
  (∑' n, ∑ r in Finset.range (n + 1), a n r) =
  (∑' r, ∑' n, if r ≤ n then a n r else 0) := by
  sorry



