import Mathlib
import Mathlib.Tactic

theorem theorem_771491_problem (p : ℝ) (h1 : 0 < p) (h2 : p < 1) :
  ∑' k : ℕ, (k : ℝ) * p * (1 - p) ^ (k - 1) = 1 / p := by
  sorry









theorem theorem_771706_problem (k c_i Y_i : ℝ)
  (hk : k > 0)
  (hc : c_i > 0)
  (hY : |Y_i| ≤ c_i) :
  Real.exp (k * Y_i) ≤ (1 / 2 : ℝ) * (1 - Y_i / c_i) * Real.exp (-k * c_i) +
                       (1 / 2 : ℝ) * (1 + Y_i / c_i) * Real.exp (k * c_i) := by
  sorry



theorem theorem_772151_problem (n : ℕ) (R : Fin n → Type*) [∀ i, CommRing (R i)] :
  Nonempty (Polynomial ((i : Fin n) → R i) ≃+* ((i : Fin n) → Polynomial (R i))) := by
  sorry

theorem theorem_771788_problem (z₁ z₂ : ℂ) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) (h_neq : z₁ ≠ z₂)
  (f : ℂ → ℂ) (hf : ∀ z, z ≠ 0 → f z = star z) :
  (Complex.arg (f z₂) : Real.Angle) - (Complex.arg (f z₁) : Real.Angle) =
  (Complex.arg z₁ : Real.Angle) - (Complex.arg z₂ : Real.Angle) := by
  sorry

theorem theorem_762358_problem (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) :
  (∃ x : ZMod p, x^2 + 1 = 0) ↔ p % 4 = 1 := by
  sorry





theorem theorem_772461_problem (t x : ℝ) (h : t > 0) :
  deriv (fun x => t ^ x) x = t ^ x * Real.log t := by
  sorry

theorem theorem_772308_problem
  (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
  [LocallyCompactSpace X] [T2Space X]
  [LocallyCompactSpace Y] [T2Space Y]
  (f : X → Y)
  (h_cont : Continuous f)
  (h_proper : ∀ K : Set Y, IsCompact K → IsCompact (f ⁻¹' K)) :
  ∀ C : Set X, IsClosed C → IsClosed (f '' C) := by
  sorry



theorem theorem_772059_problem (f : SchwartzMap ℝ ℂ) :
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ (ω : ℝ), Real.fourierIntegral f ω = f 0 := by
  sorry





theorem theorem_772406_problem (x : ℝ) (h1 : x > 0) (h2 : Real.log x + 1 / x ≠ 0) :
  HasDerivAt (fun t => Real.log (abs (Real.log t + 1 / t))) ((x - 1) / (x^2 * Real.log x + x)) x := by
  sorry





theorem theorem_772393_problem
  (K : Type*) [Field K]
  (V : Type*) [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  (m : ℕ) (hm : FiniteDimensional.finrank K V = m)
  (r : ℕ) (hr : m < r) :
  Subsingleton (AlternatingMap K V K (Fin r)) := by
  sorry











theorem theorem_773013_problem (f : ℝ → ℝ) (h x : ℝ) (hne0 : h ≠ 0) :
  f x + h * ((f (x + h) - f x) / h) = f (x + h) := by
  sorry









theorem theorem_772649_problem (f g : ℕ → ℝ)
  (h1 : ∃ C > 0, ∃ N : ℕ, ∀ n > N, |f n - n| ≤ C * (n : ℝ) ^ (1 / 2 : ℝ))
  (h2 : ∃ δ : ℕ → ℝ, (∀ n, g n = (n + δ n) ^ 2) ∧ 
    (∃ C > 0, ∃ N : ℕ, ∀ n > N, |δ n| ≤ C * Real.log (n : ℝ))) :
  ∃ C > 0, ∃ N : ℕ, ∀ n > N, |f n * g n - (n : ℝ) ^ 3| ≤ C * (n : ℝ) ^ (5 / 2 : ℝ) := by
  sorry

theorem theorem_773539_problem
  (a b T : ℝ)
  (f : ℝ → ℝ → ℝ)
  (hT : 0 < T)
  (hab : a ≤ b)
  (h1 : ∀ t ≥ T, IntervalIntegrable (fun x ↦ f x t) volume a b)
  (h2 : ∀ ε > 0, ∃ T₀ > T, ∀ t > T₀, ∀ x ∈ Set.Icc a b, |f x t| < ε) :
  Filter.Tendsto (fun t ↦ ∫ x in a..b, f x t) Filter.atTop (nhds 0) := by
  sorry



theorem theorem_773546_problem {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] :
  ∀ (A : Set X) (p : X), p ∈ closure A →
  ∃ B : Set X, B ⊆ A ∧ B.Countable ∧ p ∈ closure B := by
  sorry

theorem theorem_773901_problem
  {I G H : Type*} [Group G] [Group H]
  (g : I → G)
  (phi : I → H)
  (h_gen : Subgroup.closure (Set.range g) = ⊤)
  (h_rel : ∀ (w : FreeGroup I), FreeGroup.lift g w = 1 → FreeGroup.lift phi w = 1) :
  ∃! (f : G →* H), ∀ i, f (g i) = phi i := by
  sorry

theorem theorem_773219_problem
  (a : ℕ → ℝ)
  (g h : ℝ → ℕ → ℝ)
  (h_denom : ∀ n, h (a n) n ≠ 0)
  (h_rec : ∀ n, a (n + 1) = g (a n) n / h (a n) n)
  (h_indep : ∃ C, ∀ n, g (a n) n / h (a n) n = C) :
  ∀ n, a n = a 0 := by
  sorry

theorem theorem_773832_problem (M : Type*) [AddCommGroup M] [Module ℚ M] 
  (m : M) (n : ℤ) (hn : n ≠ 0) : 
  ∃ m' : M, n • m' = m := by
  sorry

theorem theorem_773428_problem (x : ℝ) (h : x ≠ -1) :
  x^3 / (1 + x^5) =
  -1 / 5 * (x + 1)⁻¹ +
  1 / 5 * (x^3 + 3 * x^2 - 2 * x + 1) / (x^4 - x^3 + x^2 - x + 1) := by
  sorry

theorem theorem_773807_problem
  -- We abstract the function spaces H^1(Ω), L^2(Ω), and L^2(∂Ω) as Hilbert spaces H, L, B.
  {H L B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup L] [InnerProductSpace ℝ L] [CompleteSpace L]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
  -- Parameters
  (α : ℝ) (hα : 0 < α)
  -- Operators corresponding to the problem geometry (Trace and Gradient)
  (trace : H →L[ℝ] B)
  (grad : H →L[ℝ] L)
  -- The functional J
  (J : H → ℝ)
  (hJ : ∀ u, J u = α * ‖trace u‖^2 + ‖grad u‖^2) :
  -- The conclusion: Existence of a minimizer for the problem over non-zero functions
  ∃ u : H, J u = sInf (J '' {v : H | v ≠ 0}) := by
  sorry

theorem theorem_773652_problem
  {S : Type*} [Fintype S] [DecidableEq S]
  (n : ℕ) (h_n : Fintype.card S = n)
  (p : S → ℕ)
  (hp_prime : ∀ s, Nat.Prime (p s))
  (hp_inj : Function.Injective p)
  (a : (w : List S) → Fin w.length → ℕ)
  (ha_pos : ∀ w i, a w i > 0)
  (phi : List S → ℕ)
  (h_phi : ∀ w, phi w = ((List.finRange w.length).map (λ i => (p (w.get i)) ^ (a w i))).prod)
  (h_unique : ∀ w1 w2 : List S,
    (∀ s : S, (phi w1).factorization (p s) = (phi w2).factorization (p s)) → w1 = w2) :
  Function.Injective phi := by
  sorry

















theorem theorem_774610_problem (n : ℕ)
  (S : Set (EuclideanSpace ℝ (Fin (n + 1))))
  (D : Set (EuclideanSpace ℝ (Fin (n + 1))))
  (hS : S = {x | ‖x‖ = 1})
  (hD : D = {x | ‖x‖ ≤ 1}) :
  frontier D = S := by
  sorry



theorem theorem_774717_problem
  {α : Type*}
  (P T R : Equiv.Perm α)
  (hR : ∀ x, R x ≠ x)
  (hP : P * P = 1)
  (E : Equiv.Perm α)
  (hE : E = P * T⁻¹ * R * T * P) :
  ∀ x, E x ≠ x := by
  sorry

theorem theorem_774492_problem
  (a b c : ℝ)
  (y theta phi : ℝ → ℝ)
  (x : ℝ)
  (h_b_ne_c : b ≠ c)
  (h_a_pos : 0 < a)
  (h_y_denom : y x ≠ 0)
  (h_ode : deriv y x = Real.sqrt (a * (y x - b) * (y x - c) / (y x) ^ 2) ∨
           deriv y x = -Real.sqrt (a * (y x - b) * (y x - c) / (y x) ^ 2))
  (k : ℝ)
  (h_k : k = (c - b) / (c + b))
  (h_subst1 : y x = (b + c) / 2 + (c - b) / 2 * Real.cos (theta x))
  (h_subst2 : Real.sin (theta x) = k * Real.tan (phi x)) :
  ∃ C : ℝ,
    let LHS := (1 / Real.sqrt a) * (1 / 2 * Real.log (abs (1 + k^2 * (Real.tan (phi x))^2)) + Real.arctan (k * Real.tan (phi x))) + C
    LHS = x ∨ LHS = -x := by
  sorry

theorem theorem_773970_problem :
  let R₁ := Polynomial ℤ ⧸ Ideal.span {(X : Polynomial ℤ) ^ 3}
  let R₂ := Polynomial ℤ ⧸ Ideal.span {(X : Polynomial ℤ) ^ 3 + (X : Polynomial ℤ) ^ 2}
  ¬ Nonempty (R₁ ≃+* R₂) := by
  sorry



theorem theorem_774851_problem (z : ℂ) (h : Complex.abs z > 1) :
  1 / (z + 1) ^ 2 = ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * (n : ℂ) / z ^ (n + 1) := by
  sorry



theorem theorem_775047_problem (c d x : ℝ) (P : ℕ → ℝ)
  (h_ne : x + d ≠ 0)
  (h_rec : ∀ n, P (n + 1) = c * x ^ n - d * P n) :
  ∀ n, P n = (P 0 * x + P 0 * d - c) / (x + d) * ((-1) ^ n * d ^ n) + c / (x + d) * x ^ n := by
  sorry





theorem theorem_774986_problem
  (G H : Type*) [Group G] [Group H]
  (G₁ : Subgroup G) (H₁ : Subgroup H)
  (f : G ≃* H)
  (h_map : G₁.map f.toMonoidHom = H₁) :
  ∃ φ : G ⧸ G₁ ≃ H ⧸ H₁, ∀ g : G, φ (QuotientGroup.mk g) = QuotientGroup.mk (f g) := by
  sorry





theorem theorem_775396_problem {F : Type*} [Field F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F)
  (h : ∀ k : Fin n, (A.submatrix (Fin.castLE (Nat.succ_le_of_lt k.is_lt)) 
                                 (Fin.castLE (Nat.succ_le_of_lt k.is_lt))).det ≠ 0) :
  ∃ (L U : Matrix (Fin n) (Fin n) F),
    (∀ i j, i < j → L i j = 0) ∧ 
    (∀ i, L i i = 1) ∧ 
    (∀ i j, j < i → U i j = 0) ∧ 
    A = L * U := by
  sorry



theorem theorem_775390_problem
  {V : Type*}
  (E : Set (V × V))
  (p : V → ℤ)
  (d : V → V → ℤ)
  (hp : ∀ i, p i = 0 ∨ p i = 1)
  (hd : ∀ i j, (i, j) ∈ E → d i j = 0 ∨ d i j = 1)
  (h_constr : ∀ i j, (i, j) ∈ E → d i j ≥ p i - p j) :
  ∀ i j, (i, j) ∈ E → p i = 1 → p j = 0 → d i j = 1 := by
  sorry





theorem theorem_774579_problem
  (p : ℝ → ℝ)
  (s : ℝ)
  (h_diff : Differentiable ℝ p)
  (h_eq : ∀ t dt, p (t + dt) = (p t ^ 2 + p t * (1 - p t) * (1 - s)) / (1 - 2 * p t * (1 - p t) * s))
  (h_equil : ∀ t dt, p (t + dt) = p t) :
  deriv p = 0 := by
  sorry









theorem theorem_775732_problem (S : Set ℝ) (F : Set (Set ℝ))
  (h_cover : S ⊆ ⋃₀ F)
  (h_open : ∀ U ∈ F, IsOpen U)
  (h_cond : ∃ B : Set ℝ, (∀ x : ℝ, ∃ y ∈ B, x < y) ∧
    ∀ y ∈ B, ∃ F' : Finset (Set ℝ), (F' : Set (Set ℝ)) ⊆ F ∧ S ∩ Set.Iic y ⊆ ⋃₀ (F' : Set (Set ℝ))) :
  IsCompact S := by
  sorry

theorem theorem_775533_problem
  {k : Type*} [Field k]
  {n : ℕ}
  (lam : Fin n → k)
  (hlam : ∀ i, lam i ≠ 0)
  (S : Matrix (Fin n) (Fin n) k)
  (hS : S = Matrix.diagonal lam)
  (dσ : Matrix (Fin n) (Fin n) k → Matrix (Fin n) (Fin n) k)
  (hdσ : ∀ A, dσ A = S * A * S⁻¹) :
  ∀ (A : Matrix (Fin n) (Fin n) k) (i j : Fin n),
    dσ A i j = lam i * (lam j)⁻¹ * A i j := by
  sorry

theorem theorem_776279_problem
  (n : ℕ)
  (D : Set ℝ)
  (b : Fin n → Fin n → ℝ → ℝ)
  (c : Fin n → ℝ → ℝ)
  (d : ℝ → ℝ)
  (g : ℝ → ℝ)
  (hb : ∀ i j, ContDiffOn ℝ ⊤ (b i j) D)
  (hc : ∀ i, ContDiffOn ℝ ⊤ (c i) D)
  (hd : ContDiffOn ℝ ⊤ d D)
  (hg : ∀ x ∈ D, g x = (∑ i : Fin n, ∑ j : Fin n, b i j x) + (∑ i : Fin n, c i x) + d x) :
  ContDiffOn ℝ ⊤ g D := by
  sorry





theorem theorem_776192_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (n : ℕ)
  (v : Fin n → V)
  (hv : LinearIndependent ℝ v)
  (u : Fin n → V)
  (hu_ortho : Orthonormal ℝ u)
  (h_span : Submodule.span ℝ (Set.range v) = Submodule.span ℝ (Set.range u))
  (w : V) :
  ‖orthogonalProjection (Submodule.span ℝ (Set.range v)) w‖ =
    Real.sqrt (∑ i, (inner w (u i)) ^ 2) := by
  sorry

theorem theorem_775903_problem
  (n : ℕ) (hn : n ≥ 1)
  (x : ℕ → ℝ)
  (c : ℕ → ℝ)
  (z : ℕ → ℝ)
  (f : (ℕ → ℝ) → ℝ)
  (h_f : ∀ x, f x = ∑ k in Finset.Icc 1 n, c k * (∏ i in Finset.Icc 1 k, x i))
  (h_z1 : z 1 = x 1)
  (h_zk : ∀ k ∈ Finset.Icc 2 n, z k = z (k - 1) * x k) :
  f x = ∑ k in Finset.Icc 1 n, c k * z k := by
  sorry











theorem theorem_776807_problem (n k : ℕ) (hk : k ≥ 8)
  (h_factors : ∀ p : ℕ, Nat.Prime p → p ∣ Nat.choose n k → p ≤ k) :
  (Nat.choose n k : ℝ) ≤ (n : ℝ) ^ ((k : ℝ) / 2) := by
  sorry

theorem theorem_774949_problem
  (A : ℝ)
  (V : ℝ → ℝ)
  (I : Set ℝ)
  (h_open : IsOpen I)
  (h_conn : IsConnected I)
  (h_domain : ∀ θ ∈ I, 0 < Real.tan (θ / 2))
  (h_diff : DifferentiableOn ℝ V I)
  (h_ode : ∀ θ ∈ I, Real.sin θ * deriv V θ = A) :
  ∃ B : ℝ, ∀ θ ∈ I, V θ = A * Real.log (Real.tan (θ / 2)) + B := by
  sorry



theorem theorem_776454_problem (a b : ℕ → ℝ)
  (h_mono_a : StrictMono a)
  (h_mono_b : StrictMono b)
  (h_eq : ∀ k : ℕ, ∀ t : ℝ, 0 < t →
    (∑' j, if k ≤ j then Real.exp (-(a j) * t) else 0) =
    (∑' j, if k ≤ j then Real.exp (-(b j) * t) else 0)) :
  ∀ n, a n = b n := by
  sorry

theorem theorem_776943_problem
  (f : ℂ → ℂ)
  (u v : ℝ → ℝ → ℝ)
  (h : ∀ x y : ℝ, f (x + y * Complex.I) = (u x y : ℂ) + (v x y : ℂ) * Complex.I)
  (α β x y : ℝ) :
  f ((x + y * Complex.I) + (α + β * Complex.I)) =
  (u (x + α) (y + β) : ℂ) + (v (x + α) (y + β) : ℂ) * Complex.I := by
  sorry

theorem theorem_776133_problem (I : ℝ) 
  (hI : I = ∫ x in Set.Ici 0, Real.exp (-x) * |Real.sin x|) : 
  I = (1 / 2) * (1 / Real.tanh (Real.pi / 2)) := by
  sorry







theorem theorem_776877_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  {P : Type*} [AddTorsor V P]
  (A₁ B₁ C₁ A₂ B₂ C₂ O G H J : P)
  (h_persp_A : Collinear ℝ ({A₁, A₂, O} : Set P))
  (h_persp_B : Collinear ℝ ({B₁, B₂, O} : Set P))
  (h_persp_C : Collinear ℝ ({C₁, C₂, O} : Set P))
  (h_G_line1 : Collinear ℝ ({A₁, B₁, G} : Set P))
  (h_G_line2 : Collinear ℝ ({A₂, B₂, G} : Set P))
  (h_H_line1 : Collinear ℝ ({B₁, C₁, H} : Set P))
  (h_H_line2 : Collinear ℝ ({B₂, C₂, H} : Set P))
  (h_J_line1 : Collinear ℝ ({C₁, A₁, J} : Set P))
  (h_J_line2 : Collinear ℝ ({C₂, A₂, J} : Set P)) :
  Collinear ℝ ({G, H, J} : Set P) := by
  sorry



theorem theorem_777159_problem
  (δ : Fin 3 → Fin 3 → ℤ)
  (ε : Fin 3 → Fin 3 → Fin 3 → ℤ)
  (hδ : ∀ i j, δ i j = if i = j then 1 else 0)
  (hε : ∀ i j k, ε i j k = Matrix.det ![(fun x : Fin 3 => if x = i then (1 : ℤ) else 0),
                                       (fun x => if x = j then 1 else 0),
                                       (fun x => if x = k then 1 else 0)]) :
  ∀ j k l m : Fin 3,
    ∑ i : Fin 3, ε i j k * ε i l m = δ j l * δ k m - δ j m * δ k l := by
  sorry



theorem theorem_777199_problem
  {W : Type*}
  (R : W → W → Prop)
  (phi : W → Prop)
  (h_refl : Reflexive R)
  (h_det : ∀ x y z, R x y → R x z → y = z)
  (w : W)
  (h_dia : ∃ v, R w v ∧ phi v) :
  phi w := by
  sorry

