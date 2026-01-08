import Mathlib
import Mathlib.Tactic







theorem theorem_473650_problem
  (n : ℕ)
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA : A.PosDef)
  (hB : B.PosDef) :
  (B⁻¹ - (A + B)⁻¹).PosDef := by
  sorry



theorem theorem_473219_problem
  (A B C : ℕ)
  (hA : A > 0) (hB : B > 0) (hC : C > 0)
  (hC_def : C = Nat.gcd A B)
  (R : Type*) [CommMonoid R]
  (σ : ℕ → R)
  (h_sigma_mult : ∀ m n : ℕ, σ (m * n) = σ m * σ n) :
  σ ((A * B) / (C ^ 2)) = σ (A / C) * σ (B / C) := by
  sorry

theorem theorem_473205_problem
  (q : ℕ → ℚ) (hq : Function.Bijective q)
  (a b : ℕ → ℝ)
  (h_lt : ∀ n, a n < b n)
  (h_disj : ∀ n m, n ≠ m → Disjoint (Set.Ioo (a n) (b n)) (Set.Ioo (a m) (b m)))
  (h_ends : ∀ n m, n ≠ m → Disjoint ({a n, b n} : Set ℝ) {a m, b m}) :
  ∃ f : ℚ → ℝ, ∀ n, f (q n) ∈ Set.Ioo (a n) (b n) := by
  sorry

theorem theorem_473777_problem
  {𝔽 V W U : Type*} [Field 𝔽]
  [AddCommGroup V] [Module 𝔽 V]
  [AddCommGroup W] [Module 𝔽 W]
  [AddCommGroup U] [Module 𝔽 U]
  (φ : W →ₗ[𝔽] U)
  (T : (V →ₗ[𝔽] W) → (V →ₗ[𝔽] U))
  (hT : ∀ (u : V →ₗ[𝔽] W) (v : V), T u v = φ (u v)) :
  IsLinearMap 𝔽 T := by
  sorry





theorem theorem_474033_problem (u : ℝ → ℝ → ℝ)
  (h_diff : ∀ x y, x ≠ -1 → DifferentiableAt ℝ (Function.uncurry u) (x, y))
  (h_pde : ∀ x y, x ≠ -1 → deriv (fun t ↦ u t y) x + u x y * deriv (fun t ↦ u x t) y = 0)
  (h_ic : ∀ y, u 0 y = y) :
  ∀ x y, x ≠ -1 → u x y = y / (x + 1) := by
  sorry











theorem theorem_474423_problem (A₀ A₁ ε : ℝ)
  (y₀ y₁ y : ℝ → ℝ)
  (h₀ : ∀ t, y₀ t = A₀ * Real.exp t)
  (h₁ : ∀ t, y₁ t = A₁ * Real.exp t - 1)
  (hy : ∀ t, y t = y₀ t + ε * y₁ t) :
  ∀ t, HasDerivAt y (y t + ε) t := by
  sorry





theorem theorem_473827_problem
  {I : Type*} [Fintype I] [DecidableEq I]
  (children : I → Finset I)
  (dL : I → ℝ)
  (partial_x : I → I → ℝ)
  (h_struct : ∀ (i j : I), j ∉ children i → partial_x j i = 0)
  (h_chain : ∀ (i : I), dL i = ∑ j : I, (partial_x j i) * (dL j)) :
  ∀ (i : I), dL i = ∑ j in children i, (partial_x j i) * (dL j) := by
  sorry

theorem theorem_474508_problem
  {A : Type*} [MetricSpace A] [CompleteSpace A] [Nonempty A]
  (G : Set (Set A))
  (hG_count : G.Countable)
  (hG_nd : ∀ g ∈ G, IsNowhereDense g) :
  ⋃₀ G ≠ Set.univ := by
  sorry



theorem theorem_474223_problem (n : ℕ) (a b : ℝ) (hn_odd : Odd n) (hn_ge_3 : n ≥ 3) :
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    if i = j then a
    else if (i : ℕ) / 2 = (j : ℕ) / 2 then 0
    else b
  A.det = ((((n : ℝ) - 3) * b + a) * a - ((n : ℝ) - 1) * b ^ 2) *
          a ^ ((n - 1) / 2) * (a - 2 * b) ^ ((n - 3) / 2) := by
  sorry

theorem theorem_474332_problem
  (n : ℕ)
  (M : Fin n → ℕ)
  (v : (i : Fin n) → Fin (M i) → ℕ)
  (h_bin : ∀ (i : Fin n) (j : Fin (M i)), v i j = 0 ∨ v i j = 1)
  (h_structure : ∀ (i : Fin n), ∑ j : Fin (M i), v i j = 1) :
  ∑ i : Fin n, ∑ j : Fin (M i), v i j = n := by
  sorry

theorem theorem_474209_problem :
  let S := MvPolynomial (Fin 2) ℤ
  let I : Ideal S := Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
  let R := S ⧸ I
  ∀ a : R, IsNilpotent a → a = 0 := by
  sorry





theorem theorem_475083_problem (n : ℕ) (x : ℝ) (hn : 0 < n) (hx : |x| < 1) :
  (x ^ n) / ((1 - x) ^ n) = ∑' m : ℕ, if m < n then 0 else (Nat.choose (m - 1) (n - 1) : ℝ) * x ^ m := by
  sorry







theorem theorem_475119_problem
  (A : Type*) [CommRing A]
  (B : Type*) [CommRing B] [Algebra A B]
  (b : B)
  (n : ℕ)
  (a : ℕ → A)
  (h_eq : b^n + (Finset.range n).sum (fun i => algebraMap A B (a i) * b^i) = 0) :
  ∀ m : ℕ, n ≤ m → b^m ∈ Submodule.span A {x | ∃ i : ℕ, i < n ∧ x = b^i} := by
  sorry

theorem theorem_475528_problem
  (A : Type*) [Group A]
  (B A' B' : Subgroup A)
  (hB'_sub_B : B' ≤ B)
  (hB'_sub_A' : B' ≤ A')
  [hB_normal : B.Normal]
  [hB'_normal_A' : (B'.subgroupOf A').Normal]
  (h_iso : Nonempty ((A' ⧸ (B'.subgroupOf A')) ≃* (A ⧸ B))) :
  Nonempty ((A ⧸ B) ≃* (A' ⧸ (B'.subgroupOf A'))) := by
  sorry

theorem theorem_475142_problem
  {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [TopologicalAddGroup X] [ContinuousSMul ℝ X]
  (V : Set X) (hV : IsOpen V)
  (x x_star : X) (hx : x ∈ V) :
  ∃ δ > 0, ∀ r : ℝ, r ∈ Set.Ioo (-δ) δ → x + r • x_star ∈ V := by
  sorry



theorem theorem_475715_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  {n k : ℕ}
  (a : Basis (Fin n) F V)
  (I : Fin k → Fin n) :
  ∃! (ϕ : MultilinearMap F (fun _ : Fin k ↦ V) F),
    ∀ (J : Fin k → Fin n), ϕ (a ∘ J) = if J = I then (1 : F) else 0 := by
  sorry







theorem theorem_475379_problem (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
  (hcoprime : Nat.Coprime a b) (r1 r2 : ℤ) :
  let b_inv := Int.gcdB a b
  let a_inv := Int.gcdA a b
  let x := r1 * (b : ℤ) * b_inv + r2 * (a : ℤ) * a_inv
  ∀ y : ℤ, (y ≡ r1 [ZMOD a] ∧ y ≡ r2 [ZMOD b]) ↔ y ≡ x [ZMOD a * b] := by
  sorry

theorem theorem_475673_problem (y : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (x : ℝ)
  (hy : DifferentiableAt ℝ y x)
  (hy' : DifferentiableAt ℝ (deriv y) x)
  (hf : DifferentiableAt ℝ (Function.uncurry f) (y x, deriv y x)) :
  deriv (fun t => f (y t) (deriv y t)) x =
  deriv (fun u => f u (deriv y x)) (y x) * deriv y x +
  deriv (fun v => f (y x) v) (deriv y x) * deriv (deriv y) x := by
  sorry





theorem theorem_475954_problem (x : ℝ) (hx : x > 0)
  (A : Set ℝ) (hA : A = {y | ∃ n : ℕ, 0 < n ∧ y = (n : ℝ) * x}) :
  A.Nonempty := by
  sorry





theorem theorem_476167_problem
  (m n : ℕ)
  (T : ℕ → ℝ)
  (c_f c_a : ℝ)
  (hm : m > 0)
  (hn : n ≥ m)
  (h_calc : ∀ k, k ≥ n → T k = c_f + m * c_a) :
  ∃ C : ℝ, ∀ k, k ≥ n → T k ≤ C := by
  sorry



theorem theorem_476211_problem (n k : ℕ) (h : k ≤ n) :
  ∫ x in (0 : ℝ)..(1 : ℝ), (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k) = 1 / (n + 1 : ℝ) := by
  sorry

theorem theorem_475387_problem (N : ℤ) (Δx : ℝ) (k : ℤ)
  (hN_pos : 0 < N) (hN_even : Even N) (hdx_pos : 0 < Δx)
  (hk_range : -N / 2 ≤ k ∧ k < N / 2) :
  let f_k := (k : ℝ) / (N * Δx)
  let L := (N : ℝ) * Δx
  Complex.exp (2 * Real.pi * Complex.I * f_k * L) = 1 := by
  sorry







theorem theorem_476490_problem (A : Type*) (a : ℕ → A) (h : Function.Bijective a) :
  ∃ f : A → ℕ, Function.Bijective f ∧ ∀ n, f (a n) = n := by
  sorry

theorem theorem_476234_problem (m n : ℤ) (hn : n > 0) :
  let x : ℂ := (m : ℂ) / (n : ℂ)
  let ζ : ℂ := Complex.exp (Complex.I * Real.pi / (n : ℂ))
  Complex.sin (Real.pi * x) = 1 / (2 * Complex.I) * (ζ ^ m - ζ ^ (-m)) := by
  sorry



theorem theorem_476276_problem
  {n p : ℕ}
  (X Z : Matrix (Fin n) (Fin p) ℝ)
  (h : ∃ σ : Equiv.Perm (Fin n), Z = Matrix.submatrix X σ id) :
  Matrix.transpose Z * Z = Matrix.transpose X * X := by
  sorry

theorem theorem_476148_problem (a : ℝ) (ha : a > 0) :
  ∫ x in (0 : ℝ)..1, a * Real.sqrt (1 + x ^ 2) =
  a * (Real.sqrt 2 / 2 + (1 / 2 : ℝ) * Real.log (1 + Real.sqrt 2)) := by
  sorry

theorem theorem_476026_problem (n k : ℕ) (h : k ≤ n) :
  Nat.choose n k = Nat.factorial n / (Nat.factorial k * Nat.factorial (n - k)) := by
  sorry









theorem theorem_476585_problem (D : Set (ℝ × ℝ))
  (hD : D = {p | ∃ q₁ q₂ : ℚ, p = ((q₁ : ℝ), (q₂ : ℝ))}) :
  Set.Countable D ∧ Dense D := by
  sorry







theorem theorem_476672_problem (P : Type*) (H N C : P → Prop) (f : P)
  (h1 : (∀ p, H p ∨ N p) → ¬ (∃ q, C q))
  (h2 : C f) :
  ∃ p, ¬ N p := by
  sorry

theorem theorem_476834_problem
  {k : Type*} [Field k]
  {n : ℕ}
  (A B : Matrix (Fin n) (Fin n) k)
  [Invertible B] :
  {X | (B * A * ⅟B) * X = X * (B * A * ⅟B)} =
  (fun X => B * X * ⅟B) '' {X | A * X = X * A} := by
  sorry



theorem theorem_477060_problem (ω t : ℝ) (hω : ω ≠ 0) :
  (Real.sin (2 * ω * t - ω * t) / (4 * ω)) - (Real.sin (2 * ω * 0 - ω * t) / (4 * ω)) = 
  Real.sin (ω * t) / (2 * ω) := by
  sorry





theorem theorem_477175_problem
  {X : Type*} [NormedAddCommGroup X]
  (B : Set X) (hB : B = Metric.closedBall (0 : X) 1)
  (h_compact : IsCompact B)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ s : Finset X, (s : Set X) ⊆ B ∧ ∀ y ∈ B, ∃ x ∈ s, dist y x < ε := by
  sorry

theorem theorem_477295_problem
  {D : Type*}
  (f g : D → ℝ)
  (W : D → ℝ)
  (h1 : ∀ x, W x = f x * Real.exp (g x))
  (h2 : ∀ x, Real.exp (g x) ≠ 0)
  (h3 : ∀ x y, f x = f y)
  (x₀ : D)
  (h4 : W x₀ = 0) :
  ∀ x, W x = 0 := by
  sorry

theorem theorem_477542_problem
  {X : Type*} [MetricSpace X]
  (x y z : ℕ → X)
  (h : ∀ ε > 0, ∃ m : ℕ, ∀ k ≥ m, dist (x k) (y k) < ε / 2 ∧ dist (y k) (z k) < ε / 2) :
  ∀ ε > 0, ∃ m : ℕ, ∀ k ≥ m, dist (x k) (z k) < ε := by
  sorry



theorem theorem_477428_problem (n : ℕ) (T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
  let t := LinearMap.toMatrix' T
  let norm1 := fun (x : Fin n → ℝ) ↦ ∑ i, |x i|
  let op_norm := sSup { k | ∃ x, x ≠ 0 ∧ k = norm1 (T x) / norm1 x }
  op_norm = ⨆ j, ∑ i, |t i j| := by
  sorry







theorem theorem_477088_problem
  (x y : ℝ)
  (φ Φ : ℝ → ℝ)
  (hΦ : ∀ z, HasDerivAt Φ (φ z) z)
  (θ : ℝ)
  (h_denom_0 : Φ (x * θ) ≠ 0)
  (h_denom_1 : Φ (x * θ) ≠ 1)
  (A : ℝ → ℝ)
  (hA : ∀ t, A t = (φ (x * t) * x) / (Φ (x * t) * (1 - Φ (x * t))))
  (L : ℝ)
  (hL : HasDerivAt A L θ) :
  HasDerivAt (fun t => A t * (y - Φ (x * t)))
    (- (φ (x * θ) ^ 2 * x ^ 2) / (Φ (x * θ) * (1 - Φ (x * θ))) + L * (y - Φ (x * θ)))
    θ := by
  sorry













theorem theorem_477649_problem (R : Type*) [CommRing R] [IsArtinianRing R] [Nontrivial R]
  (h : Ideal.IsPrime (⊥ : Ideal R)) : IsField R := by
  sorry

theorem theorem_477322_problem (S : Type*) (op : S → S → S)
  (h_left_cancel : ∀ a b c : S, op a b = op a c → b = c)
  (h_right_cancel : ∀ a b c : S, op b a = op c a → b = c) :
  ∀ e : S, op e e = e → ∀ x : S, op x e = x := by
  sorry





theorem theorem_478131_problem
  (phi : ℝ → ℝ)
  (psi : ℝ → ℝ)
  (L : ℝ)
  (h_cont : ContinuousOn phi (Set.Ici 0))
  (h_phi_nonneg : ∀ t, 0 ≤ t → 0 ≤ phi t)
  (hL : L > 0)
  (h_psi_def : ∀ t, psi t = Real.exp (-L * t) * ∫ s in (0)..t, phi s)
  (h_psi_le : ∀ t, 0 ≤ t → psi t ≤ 0) :
  ∀ t, 0 ≤ t → phi t = 0 := by
  sorry



theorem theorem_478117_problem (a : ℕ → ℕ → ℝ)
  (h : ∀ i, Bornology.IsBounded (Set.range (a i))) :
  ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ i, ∃ l, Filter.Tendsto (fun n ↦ a i (k n)) Filter.atTop (nhds l) := by
  sorry



theorem theorem_478291_problem
  (a b : ℝ) (ha : a ≠ 0)
  (h v r u f : ℝ → ℝ → ℝ)
  -- Condition 1: Conservation of mass h_t + (hv)_x = r
  (h_cons : ∀ x t, deriv (fun t' => h x t') t + deriv (fun x' => h x' t * v x' t) x = r x t)
  -- Condition 2: Force balance av = bh
  (h_bal : ∀ x t, a * v x t = b * h x t)
  -- Condition 3: Definition of u
  (h_u_def : ∀ x t, u x t = 2 * v x t)
  -- Condition 4: Definition of f
  (h_f_def : ∀ x t, f x t = 2 * (b / a) * r x t) :
  -- Conclusion: u_t + u * u_x = f
  ∀ x t, deriv (fun t' => u x t') t + (u x t) * deriv (fun x' => u x' t) x = f x t := by
  sorry





theorem theorem_478508_problem (a r : ℝ) (ha : a ≠ 0) (hr : |r| < 1) :
  ∑' n : ℕ, a * r ^ n = a / (1 - r) := by
  sorry

