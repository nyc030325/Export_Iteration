import Mathlib
import Mathlib.Tactic



theorem theorem_672996_problem
  (a : Fin 3 → ℝ)
  (v e : Fin 3 → Quaternion ℝ)
  (h_weights : ∀ k, 0 < a k)
  (h_v_pure : ∀ k, (v k).re = 0)
  (h_e_pure : ∀ k, (e k).re = 0)
  (h_v_orth : Pairwise (fun i j => inner (v i) (v j) = (0 : ℝ)))
  (h_e_orth : Pairwise (fun i j => inner (e i) (e j) = (0 : ℝ)))
  (h_v_norm : ∀ k, ‖v k‖ = 1)
  (h_e_norm : ∀ k, ‖e k‖ = 1) :
  ∀ q1 q2 : Quaternion ℝ, ‖q1‖ = 1 → ‖q2‖ = 1 →
  (∑ k, a k * ‖v k - q1 * e k * q1⁻¹‖ ^ 2 ≤ ∑ k, a k * ‖v k - q2 * e k * q2⁻¹‖ ^ 2) ↔
  (∑ k, a k * inner (v k) (q1 * e k * q1⁻¹) ≥ ∑ k, a k * inner (v k) (q2 * e k * q2⁻¹)) := by
  sorry

theorem theorem_672554_problem (z : ℂ) (h : Complex.cos z = 0) :
  ∃ n : ℤ, z = ↑n * ↑Real.pi + ↑Real.pi / 2 := by
  sorry

theorem theorem_672726_problem (x y z : ℝ) :
  (x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x^2 + y^2 ≤ 1 ∧ z ≤ 2 + x^2 + y^2 / 4) ↔
  (0 ≤ x ∧ x ≤ 1 ∧ 
   0 ≤ y ∧ y ≤ Real.sqrt (1 - x^2) ∧ 
   0 ≤ z ∧ z ≤ 2 + x^2 + y^2 / 4) := by
  sorry

theorem theorem_672503_problem (n : ℕ) (a : List (Fin n)) (α : Equiv.Perm (Fin n))
  (h_nodup : a.Nodup) (h_len : a.length = n) :
  α⁻¹ * a.formPerm * α = (a.map (⇑α⁻¹)).formPerm := by
  sorry

theorem theorem_673317_problem (n : ℕ) (σ : Equiv.Perm (Fin n)) (k m : ℕ)
  (l₁ l₂ : List (Equiv.Perm (Fin n)))
  (h_prod₁ : l₁.prod = σ)
  (h_prod₂ : l₂.prod = σ)
  (h_len₁ : l₁.length = k)
  (h_len₂ : l₂.length = m)
  (h_swap₁ : ∀ τ ∈ l₁, Equiv.Perm.IsSwap τ)
  (h_swap₂ : ∀ τ ∈ l₂, Equiv.Perm.IsSwap τ) :
  k % 2 = m % 2 := by
  sorry







theorem theorem_673284_problem :
  Filter.Tendsto (fun n : ℕ => Real.exp (-2 * n) * (1 + 2 / (n : ℝ)) ^ ((n : ℝ) ^ 2)) Filter.atTop (nhds (Real.exp (-2))) := by
  sorry





theorem theorem_673294_problem (G : Type*) [Group G] [Fintype G] (h : G) (ρ : G → ℂ) :
  ∑ g, ρ g = ∑ g, ρ (h * g) := by
  sorry

theorem theorem_673421_problem (s : ℕ → ℚ) (hs : Function.Bijective s) (x : ℝ) :
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (fun n => (s (φ n) : ℝ)) Filter.atTop (nhds x) := by
  sorry

theorem theorem_672911_problem (f : ℝ × ℝ → ℝ) (h_cont : Continuous f) :
  ¬ Function.Bijective f := by
  sorry



theorem theorem_673776_problem (A B : Type*) [Ring A] [Ring B]
  (phi : A → B)
  (h_add : ∀ x y, phi (x + y) = phi x + phi y)
  (h_mul : ∀ x y, phi (x * y) = phi x * phi y)
  (h_surj : Function.Surjective phi) :
  phi 1 = 1 := by
  sorry







theorem theorem_673420_problem 
  (p₁ p₂ p₃ : EuclideanSpace ℝ (Fin 3))
  (h₁ : p₁ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  (h₂ : p₂ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  (h₃ : p₃ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  (h_distinct : p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃) :
  let S2 := { x : EuclideanSpace ℝ (Fin 3) // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 }
  let P : Set (EuclideanSpace ℝ (Fin 3)) := {p₁, p₂, p₃}
  let R : Setoid S2 := Setoid.mk 
    (λ x y => x = y ∨ (x.val ∈ P ∧ y.val ∈ P)) 
    (by 
      refine ⟨?_, ?_, ?_⟩
      · intro x; left; rfl
      · intro x y h; rcases h with rfl | h; left; rfl; right; exact ⟨h.2, h.1⟩
      · intro x y z h1 h2
        rcases h1 with rfl | h1
        · exact h2
        · rcases h2 with rfl | h2
          · right; exact h1
          · right; exact ⟨h1.1, h2.2⟩)
  let X := Quotient R
  ∃ x : X, Nonempty (FundamentalGroup X x ≃* FreeGroup (Fin 2)) := by
  sorry





theorem theorem_673152_problem {α : Type*} [DecidableEq α] (H : Finset α) (k : ℕ) 
  (hk : k ≤ H.card) :
  H.powerset.filter (fun x => x.card ≤ H.card - k) = 
  (H.powerset.filter (fun t => t.card = k)).biUnion (fun t => (H \ t).powerset) := by
  sorry











theorem theorem_674010_problem (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) :
  (∀ x, u x * deriv (deriv u) x = 1 + (deriv u x) ^ 2) ↔
  (∃ b d : ℝ, d ≠ 0 ∧ ∀ x, u x = d * Real.cosh ((x - b) / d)) := by
  sorry

theorem theorem_674165_problem (G : Type*) [Group G] [TopologicalSpace G] [TopologicalGroup G]
  (ρ : G →* G)
  (h_surj : Function.Surjective ρ)
  (h_quot : QuotientMap ρ)
  (h_bij : Function.Bijective ρ) :
  IsOpenMap ρ := by
  sorry



theorem theorem_674494_problem
  (n k : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (C : Matrix (Fin k) (Fin k) ℝ)
  (U : Matrix (Fin n) (Fin k) ℝ)
  (V : Matrix (Fin k) (Fin n) ℝ)
  (hA : IsUnit A)
  (hC : IsUnit C)
  (h_inner : IsUnit (C⁻¹ + V * A⁻¹ * U)) :
  (A + U * C * V)⁻¹ = A⁻¹ - A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ := by
  sorry

theorem theorem_674770_problem
  [TopologicalSpace ℤ]
  (h : ∀ U : Set ℤ, IsOpen U → U.Nonempty → {p ∈ U | Prime p}.Infinite) :
  {p : ℤ | Prime p}.Infinite := by
  sorry

theorem theorem_674598_problem (n : ℕ)
  (G : (Fin n → ℝ) → (Fin n → ℝ))
  (S : Set (Fin n → ℝ))
  (hG : ContDiff ℝ 1 G)
  (hS : IsCompact S) :
  BddAbove (Set.image (fun y =>
    sSup (Set.range (fun (i : Fin n) =>
      ∑ j : Fin n, |(fderiv ℝ G y (Pi.single j 1)) i|))) S) := by
  sorry





theorem theorem_674601_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (x y : V)
  (h : ∀ φ : V →ₗ[ℝ] ℝ, φ x = φ y) :
  x = y := by
  sorry



theorem theorem_674657_problem
  {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  (f : X → Y) (hf : Continuous f)
  (V : Set Y) (hV : IsOpen V) :
  IsOpen (f ⁻¹' V) := by
  sorry



theorem theorem_675434_problem (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hb_ne_one : b ≠ 1) :
  a ^ (Real.logb b c) = c ^ (Real.logb b a) := by
  sorry







theorem theorem_675780_problem :
  ¬ Nonempty (ℝ ≃ₜ {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 1}) := by
  sorry

theorem theorem_675439_problem (S : ℕ → ℝ)
  (hS : ∀ n, S n = (1 / (n : ℝ)^6) * ∑ k in Finset.Icc 1 n, (k : ℝ)^5) :
  Filter.Tendsto S Filter.atTop (nhds ((1 : ℝ) / 6)) := by
  sorry





theorem theorem_675991_problem {A : Type*} (s : List A) :
  let N : List A → Set (ℕ → A) := fun t ↦ { x | ∀ i : Fin t.length, x i = t.get i }
  let basis : Set (Set (ℕ → A)) := { U | ∃ t, U = N t }
  let T : TopologicalSpace (ℕ → A) := TopologicalSpace.generateFrom basis
  @IsClopen (ℕ → A) T (N s) := by
  sorry









theorem theorem_676201_problem {I : Type*} (a : I → ℝ)
  (h : ∀ i, a i = 0) :
  sSup {x | ∃ F : Finset I, x = ∑ i in F, a i} = 0 := by
  sorry

theorem theorem_674634_problem
  {A : Type*} [CommRing A]
  (I : Ideal A)
  (h_compl : ∃ J : Ideal A, IsCompl I J)
  (x : A) (hx : x ∉ I) :
  ∃ y : A, IsUnit y ∧ y ∉ I ∧ Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := by
  sorry

theorem theorem_676237_problem (k E : Type*) [Field k] [Field E] [Algebra k E]
  (h : Algebra.FiniteType k E) : Module.Finite k E := by
  sorry

theorem theorem_676512_problem
  {𝕜 : Type*} [RCLike 𝕜]
  {B : Type*} [NormedAddCommGroup B] [NormedSpace 𝕜 B] [CompleteSpace B]
  (x : B) :
  ‖x‖ = sSup { y : ℝ | ∃ (T : B →L[𝕜] 𝕜), ‖T‖ ≤ 1 ∧ y = ‖T x‖ } := by
  sorry





theorem theorem_677012_problem
  {K E F : Type*}
  [Field K] [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  (r : ℕ)
  (a : Fin r → E)
  (b : Fin r → F)
  (h_indep : LinearIndependent K a)
  (h_sum : ∑ j : Fin r, a j ⊗ₜ[K] b j = 0) :
  ∀ j : Fin r, b j = 0 := by
  sorry



theorem theorem_676945_problem {G : Type*} [Group G] (a_i a_1 a_k : G)
  (h : a_i * a_1 ≠ a_i * a_k) :
  a_1 ≠ a_k := by
  sorry





theorem theorem_677535_problem (z : ℂ) (h : Complex.exp (6 * z) = 2 * Complex.I) :
  ∃ n : ℤ, z = ↑(Real.log 2 / 6) + ↑(Real.pi / 12 + ↑n * Real.pi / 3) * Complex.I := by
  sorry







theorem theorem_676460_problem
  (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
  (A B C : V)
  (n : ℝ) (hn : n > 0)
  (h_error : (1 / (4 * n^2)) * ‖(C - B) - (B - A)‖ = 1 / 2) :
  n = Real.sqrt ((1 / 2) * ‖(C - B) - (B - A)‖) := by
  sorry







theorem theorem_677661_problem
  {n : ℕ}
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (b : Basis (Fin n) ℝ V)
  (df : V →L[ℝ] ℝ)
  (G : Matrix (Fin n) (Fin n) ℝ)
  (hG : G = fun k l ↦ inner (b k) (b l))
  (g_inv : Matrix (Fin n) (Fin n) ℝ)
  (h_inv : G * g_inv = 1) :
  ‖df‖^2 = ∑ k : Fin n, ∑ l : Fin n, g_inv k l * (df (b k)) * (df (b l)) := by
  sorry

theorem theorem_677455_problem
  {ι : Type*}
  {V : Type*}
  [AddCommGroup V]
  [Module ℝ V]
  (e : Basis ι ℝ V)
  (F : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (x y : V) :
  F x y = Finset.sum (e.repr x).support (fun i =>
            Finset.sum (e.repr y).support (fun j =>
              (e.repr x i) * (e.repr y j) * F (e i) (e j))) := by
  sorry





theorem theorem_677698_problem {P : Type*} [PartialOrder P] (a b : P) :
  (∀ (r : P → P → Prop), IsLinearOrder P r → (∀ x y, x ≤ y → r x y) → r a b) ↔ a ≤ b := by
  sorry

theorem theorem_677947_problem (J : Type*) (X : J → Type*)
  [∀ j, TopologicalSpace (X j)] (h : ∀ j, T2Space (X j)) :
  T2Space (Π j, X j) := by
  sorry

theorem theorem_677573_problem
  (M K : ℕ)
  (d : Fin M → Fin K → ℝ)
  (τ : Fin K → ℝ)
  (w : Fin M → Fin K → ℝ) :
  ((∀ m, (∑ k, w m k) = 1) ∧
   (∀ m k, 0 ≤ w m k) ∧
   (∀ k, (∑ m, w m k) ≥ τ k)) ↔
  (∃ s : Fin K → ℝ,
   (∀ m, (∑ k, w m k) = 1) ∧
   (∀ m k, 0 ≤ w m k) ∧
   (∀ k, 0 ≤ s k) ∧
   (∀ k, (∑ m, w m k) - s k = τ k)) := by
  sorry

theorem theorem_677307_problem
  -- R represents the space of smooth functions C^∞(M).
  -- We assume a LieRing structure to capture the properties of the Poisson bracket ⁅,⁆ (specifically the Jacobi identity).
  (R : Type*) [LieRing R]
  -- Condition: M is equipped with a Riemannian metric g.
  -- We include it as a parameter to match the problem conditions, though it is not used in the algebraic proof.
  (g_metric : Type*)
  -- Condition: H is a function in C^∞(M) (the Hamiltonian).
  (H : R)
  -- Condition: f and g are functions in C^∞(M).
  (f g : R)
  -- Definition: The time derivative operator (d/dt), denoted here as dt.
  (dt : R → R)
  -- Condition: The flow is generated by X_H, meaning d/dt u = {H, u}.
  (h_dt : ∀ u, dt u = ⁅H, u⁆) :
  -- Question: Prove the product rule for the flow acting on the Poisson bracket.
  dt ⁅f, g⁆ = ⁅dt f, g⁆ + ⁅f, dt g⁆ := by
  sorry

theorem theorem_677811_problem (a b Q δ : ℝ)
  (h1 : 0 < a)
  (h2 : a < b)
  (h3 : 0 < Q)
  (h4 : 1 / Q < a)
  (h5 : b - a < δ) :
  |Real.log b - Real.log a| < δ * Q := by
  sorry





theorem theorem_677897_problem
  (g h y : ℝ → ℝ)
  (H G : ℝ → ℝ)
  (hy : Differentiable ℝ y)
  (hh_ne_zero : ∀ z, h z ≠ 0)
  (h_ode : ∀ x, deriv y x = g x * h (y x))
  (h_H : ∀ z, HasDerivAt H (1 / h z) z)
  (h_G : ∀ x, HasDerivAt G (g x) x) :
  ∃ C : ℝ, ∀ x, H (y x) = G x + C := by
  sorry







theorem theorem_678459_problem (n : ℕ)
  (p : Fin n → Polynomial ℂ)
  (a : Fin n → ℂ)
  (h_distinct : Function.Injective a)
  (h_p_nonzero : ∀ i, p i ≠ 0) :
  LinearIndependent ℂ (fun i x => (p i).eval x * Complex.exp (a i * x)) := by
  sorry





theorem theorem_678649_problem (D : Set ℂ) (hD : D.Nonempty) (f : ℂ → ℂ) :
  {z ∈ D | Summable (fun k : ℕ => (f z) ^ k)} = {z ∈ D | Complex.abs (f z) < 1} := by
  sorry





theorem theorem_678798_problem
  (X : Type*) [TopologicalSpace X]
  (x : X)
  (C : Set X) (hC : C = connectedComponent x)
  (V : Set X) (hV_open : IsOpen V) (hV_conn : IsConnected V) (hV_mem : x ∈ V) :
  C ∪ V = C := by
  sorry



theorem theorem_678227_problem (n : ℕ)
  (u : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hu : ContDiff ℝ 2 u)
  (h_grad_ne : gradient u x ≠ 0) :
  ∑ i : Fin n, ∑ j : Fin n, (iteratedFDeriv ℝ 2 u x ![PiLp.basisFun 2 ℝ (Fin n) i, PiLp.basisFun 2 ℝ (Fin n) j]) ^ 2 ≥
  ‖gradient (fun y => ‖gradient u y‖) x‖ ^ 2 := by
  sorry



theorem theorem_678106_problem {F : Type*} [Field F] {σ : Type*}
  (f : Polynomial (MvPolynomial σ F))
  (h_domain : IsDomain (Polynomial (MvPolynomial σ F) ⧸ Ideal.span {f})) :
  Nonempty (FractionRing (Polynomial (MvPolynomial σ F) ⧸ Ideal.span {f}) ≃+*
    (Polynomial (FractionRing (MvPolynomial σ F)) ⧸
      Ideal.span {Polynomial.map (algebraMap (MvPolynomial σ F) (FractionRing (MvPolynomial σ F))) f})) := by
  sorry



