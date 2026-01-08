import Mathlib
import Mathlib.Tactic

theorem theorem_716298_problem
  {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
  (R : E → ℝ) (g : X → E) (U : Set E) (u : X → E)
  (hR_cont : Continuous R)
  (hR_sc : StrictConvexOn ℝ U R)
  (hg_cont : Continuous g)
  (hU_compact : IsCompact U)
  (hU_nonempty : U.Nonempty)
  (hU_convex : Convex ℝ U)
  (h_u_min : ∀ x, u x ∈ U ∧ ∀ v ∈ U, R (u x) + inner (g x) (u x) ≤ R v + inner (g x) v) :
  Continuous u := by
  sorry







theorem theorem_715900_problem
  (R : Type*) [CommRing R]
  (M : Type*) [AddCommGroup M] [Module R M]
  (h_acc : IsNoetherian R M)
  (chain : ℕ → Submodule R M)
  (h_chain : Monotone chain) :
  ∃ n, ∀ k, n ≤ k → chain k = chain n := by
  sorry









theorem theorem_715840_problem 
  (R h alpha : ℝ) 
  (hR : 0 < R) 
  (hh : 0 < h) 
  (halpha : 0 < alpha ∧ alpha < Real.pi / 2)
  (b : ℝ) (hb : b = h * Real.cot alpha)
  (hb_bound : b ≤ 2 * R)
  (a : ℝ) (ha : a = Real.sqrt (b * (2 * R - b)))
  (phi : ℝ) (hphi : phi = Real.arccos (1 - b / R)) :
  MeasureTheory.volume { p : ℝ × ℝ × ℝ | p.1^2 + p.2.1^2 ≤ R^2 ∧ R - b ≤ p.1 ∧ 
    0 ≤ p.2.2 ∧ p.2.2 ≤ (p.1 - (R - b)) * Real.tan alpha } = 
  ENNReal.ofReal (1 / 3 * Real.tan alpha * (a * (3 * R^2 - a^2) + 3 * R^2 * (b - R) * phi)) := by
  sorry



theorem theorem_716540_problem (f F : ℝ → ℝ) (a b y : ℝ)
  (ha : a ≠ 0)
  (hf : Continuous f)
  (hF : ∀ x, HasDerivAt F (f x) x) :
  deriv (fun y => F ((y - b) / a)) y = (1 / a) * f ((y - b) / a) := by
  sorry







theorem theorem_716582_problem (x : ℝ) :
  Real.sin x = 3 * Real.sin (x / 3) - 4 * (Real.sin (x / 3)) ^ 3 := by
  sorry

theorem theorem_716723_problem (p : ℕ) :
  let Ep := Matrix (Fin 2) (Fin 2) (ZMod p)
  (Subring.center Ep : Set Ep) = { A | ∃ x : ZMod p, A = Matrix.diagonal (fun _ => x) } := by
  sorry





theorem theorem_716718_problem (S : Type*) [TopologicalSpace S]
  (K L : Set S)
  (hK_nonempty : K.Nonempty)
  (hL_nonempty : L.Nonempty)
  (h_disjoint : Disjoint K L)
  (hK_closed : IsClosed K)
  (hL_closed : IsClosed L)
  (h_union : K ∪ L = Set.univ) :
  ¬ConnectedSpace S := by
  sorry



theorem theorem_716394_problem (R : Type*) [CommRing R] (I J : Ideal R)
  (h_sum : I + J = ⊤)
  (h_reg : ∀ x : R, x ≠ 0 → x - 1 ≠ 0 → IsRegular x ∧ IsRegular (x - 1)) :
  ¬ ∃ i j : R, i ∈ I ∧ j ∈ J ∧ i ≠ 0 ∧ j ≠ 0 ∧ i + j = 1 := by
  sorry

theorem theorem_717445_problem :
  ∫ x : ℝ, x^2 * ((1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(x^2) / 2)) = 1 := by
  sorry

theorem theorem_717024_problem (A : Type*) [BooleanAlgebra A] :
  ∃ (I : Type*) (f : A → I → Bool),
    Function.Injective f ∧
    (∀ a b, f (a ⊓ b) = f a ⊓ f b) ∧
    (∀ a b, f (a ⊔ b) = f a ⊔ f b) ∧
    (∀ a, f (aᶜ) = (f a)ᶜ) ∧
    f ⊥ = ⊥ ∧
    f ⊤ = ⊤ := by
  sorry

theorem theorem_717244_problem
  (U : Set ℂ) (hU : IsOpen U)
  (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
  (γ : ℝ → ℂ)
  (hγ_diff : ContDiffOn ℝ 1 γ (Set.Icc 0 1))
  (hγ_closed : γ 0 = γ 1)
  (hγ_in_U : Set.MapsTo γ (Set.Icc 0 1) U)
  (h_homotopy : ∃ H : ℝ → ℝ → ℂ,
    ContinuousOn (fun p : ℝ × ℝ ↦ H p.1 p.2) (Set.Icc 0 1 ×ˢ Set.Icc 0 1) ∧
    Set.MapsTo (fun p ↦ H p.1 p.2) (Set.Icc 0 1 ×ˢ Set.Icc 0 1) U ∧
    (∀ t ∈ Set.Icc 0 1, H 0 t = γ t) ∧
    (∃ z₀, ∀ t ∈ Set.Icc 0 1, H 1 t = z₀) ∧
    (∀ s ∈ Set.Icc 0 1, H s 0 = H s 1)) :
  ∫ t in (0:ℝ)..1, f (γ t) * deriv γ t = 0 := by
  sorry

theorem theorem_717221_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (k r : ℝ) (r_hat : V) (q : ℝ)
  (h_r : r ≠ 0)
  (h_unit : ‖r_hat‖ = 1)
  (E : ℝ → V)
  (h_E : ∀ x, E x = (k * x / (r ^ 2)) • r_hat) :
  deriv E q = (k / (r ^ 2)) • r_hat := by
  sorry









theorem theorem_717412_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
  (h : A = (2 : ℝ) • A.transpose) : A = 0 := by
  sorry



theorem theorem_717336_problem {X : Type*} [TopologicalSpace X]
  (h_def : ∀ U : Set X, IsOpen U ↔ (Uᶜ).Countable)
  (A : ℕ → Set X)
  (h_open : ∀ n, IsOpen (A n)) :
  IsOpen (⋂ n, A n) := by
  sorry







theorem theorem_717564_problem (v a t : ℝ) (h : a ≠ 0) :
  (-2 * v^2 / a^2) * ((v * t / a) / Real.sqrt (1 + (v * t / a)^2)) * 
  (1 / Real.sqrt (1 + (v * t / a)^2))^3 = 
  (-2 * v^3 * a * t) / (a^2 + v^2 * t^2)^2 := by
  sorry

theorem theorem_717586_problem (P : Type*) [PartialOrder P]
  (h : ∀ C : Set P, (∀ x ∈ C, ∀ y ∈ C, x ≤ y ∨ y ≤ x) → ∃ u : P, ∀ z ∈ C, z ≤ u) :
  ∃ m : P, ∀ x : P, m ≤ x → m = x := by
  sorry









theorem theorem_717820_problem :
  (¬ (∀ m : ℕ, ∃ n : ℕ, m^2 < Nat.nth Nat.Prime n ∧ Nat.nth Nat.Prime n < (m + 1)^2)) ↔
  (∃ m : ℕ, ∀ n : ℕ, Nat.nth Nat.Prime n ≤ m^2 ∨ Nat.nth Nat.Prime n ≥ (m + 1)^2) := by
  sorry











theorem theorem_717967_problem (k : ℕ) (n : ℕ) (h_n : n = 2 * k + 2)
  (C : Matrix (Fin n) (Fin n) (ZMod 2))
  (h_C : ∀ i j, C i j = if (j - i).val = k then 0 else 1) :
  C.det = 1 := by
  sorry



theorem theorem_718673_problem {R : Type*} [CommRing R] (n : ℕ) (a : Fin n → R)
  (V : Matrix (Fin n) (Fin n) R)
  (h_distinct : Function.Injective a)
  (hV : ∀ i j, V i j = a i ^ (j : ℕ)) :
  V.det = ∏ j : Fin n, ∏ i in Finset.Iio j, (a j - a i) := by
  sorry

theorem theorem_718792_problem (a t : ℝ)
  (x y u v : ℝ)
  (hx : x = 3 * a * Real.cos (2 * t) - 2 * a * Real.cos t)
  (hy : y = a * Real.cos (2 * t) - a * Real.cos t)
  (hu : u = x - 2 * y)
  (hv : v = x - 3 * y) :
  u = a * Real.cos (2 * t) ∧ v = a * Real.cos t := by
  sorry



theorem theorem_718732_problem (n : ℕ) :
  ∑ q in Finset.range (n / 2 + 1), (Nat.choose n (2 * q)) * (Nat.choose (2 * q) q) * 2 ^ (n - 2 * q) = Nat.choose (2 * n) n := by
  sorry

theorem theorem_718377_problem
  (ImageSpace FeatureSpace Y : Type*)
  (FeatureExtract : ImageSpace → FeatureSpace)
  (g : FeatureSpace → Y)
  (f : ImageSpace → Y)
  (h_def : f = g ∘ FeatureExtract) :
  ∀ x : ImageSpace, f x = g (FeatureExtract x) := by
  sorry

theorem theorem_718427_problem (G : Type*) [Group G] [Fintype G]
  (n : ℕ) (hn : Fintype.card G = n)
  (rho : G →* ℂˣ) :
  ∀ ζ ∈ MonoidHom.range rho, ζ ^ n = 1 := by
  sorry



theorem theorem_718469_problem (a b n m s : ℤ) (x : ℕ)
  (h1 : Int.gcd a n = 1)
  (h2 : Int.gcd b m = 1)
  (h3 : a ^ x ≡ s [ZMOD n])
  (h4 : b ^ x ≡ s [ZMOD m])
  (h5 : Int.gcd (a * b) (n * m) = 1) :
  (a * b) ^ x ≡ s * (a ^ x + b ^ x - s) [ZMOD n * m] := by
  sorry







theorem theorem_718988_problem (n : ℕ) (d : Fin (n + 1) → ℕ)
  (h_n : n > 0)
  (h_sum : ∑ i, d i = n) :
  Nat.multinomial Finset.univ d = n.factorial / ∏ i, (d i).factorial := by
  sorry



theorem theorem_718754_problem (n : ℕ) (h : 0 < n) :
  let N := n / 2 + 1
  let P := (n.choose N : ℝ) * (2 : ℝ) ^ (-(n : ℤ))
  let gain := (N : ℝ) / 2
  let E_total_gain := gain * P
  E_total_gain = 1 / 2 * (N : ℝ) * (2 : ℝ) ^ (-(n : ℤ)) * (n.choose N : ℝ) := by
  sorry



theorem theorem_719290_problem
  (f : ℝ × ℝ → ℝ)
  (hf : ContDiff ℝ 1 f)
  (h0 : f (0, 0) = 0)
  (hx : deriv (fun x ↦ f (x, 0)) 0 ≠ -1)
  (hy : deriv (fun y ↦ f (0, y)) 0 ≠ 0) :
  ∃ U : Set ℝ, IsOpen U ∧ 0 ∈ U ∧
  ∃ y : ℝ → ℝ, ContDiffOn ℝ 1 y U ∧ y 0 = 0 ∧
  ∀ x ∈ U, f (f (x, y x), y x) = 0 := by
  sorry

theorem theorem_719209_problem (f_Y : ℝ → ℝ) (x : ℝ) (hx : 0 < x) :
  let g := fun (t : ℝ) ↦ -2 * Real.log t
  f_Y (g x) * |deriv g x| = f_Y (g x) * (2 / x) := by
  sorry



theorem theorem_719740_problem
  (G V : ℝ → ℝ) -- G is Gibbs free energy, V is molar volume (functions of Pressure)
  (P₁ P₂ : ℝ) -- Initial and final pressures
  (h_deriv : ∀ P, HasDerivAt G (V P) P) -- Condition: V = (∂G/∂P)_T
  (h_cont : Continuous V) -- Assumption for integrability
  : G P₂ - G P₁ = ∫ P in P₁..P₂, V P := by
  sorry

theorem theorem_719467_problem (L : Type*) [Lattice L] :
  let T : TopologicalSpace L := TopologicalSpace.generateFrom
    (Set.range (Set.Iio : L → Set L) ∪ Set.range (Set.Ioi : L → Set L))
  @CompactSpace L T ↔ (∀ s : Set L, ∃ x, IsLUB s x) ∧ (∀ s : Set L, ∃ x, IsGLB s x) := by
  sorry





theorem theorem_719815_problem (x : ℕ → ℝ)
  (h_init : 0 < x 0 ∧ x 0 < Real.pi)
  (h_rec : ∀ n, x (n + 1) = x n + Real.sin (x n)) :
  Filter.Tendsto x Filter.atTop (nhds Real.pi) := by
  sorry







theorem theorem_720063_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
  (h : A * B = B * A) :
  spectralRadius ℂ (A * B) ≤ spectralRadius ℂ A * spectralRadius ℂ B := by
  sorry

theorem theorem_720188_problem :
  ⋂₀ {A : Set ℝ | (1 : ℝ) ∈ A ∧ ∀ x ∈ A, x + 1 ∈ A} = {x : ℝ | ∃ n : ℕ, 0 < n ∧ x = n} := by
  sorry

theorem theorem_719317_problem :
  ¬ ∃ a : ℕ → ℝ, ∀ x : ℝ, Real.exp x = a 0 + ∑' k : ℕ, if k = 0 then 0 else a k * (1 + x / (k : ℝ)) ^ k := by
  sorry



theorem theorem_719910_problem (n m : ℕ) (X : Set (Fin n → ℝ))
  (P : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (h : m < n) :
  (∃ x1 ∈ X, ∃ x2 ∈ X, x1 ≠ x2 ∧ P x1 = P x2) ↔
  (0 < FiniteDimensional.finrank ℝ (LinearMap.ker P)) := by
  sorry



theorem theorem_720293_problem (y : ℝ → ℝ)
  (h_diff : DifferentiableOn ℝ y (Set.Icc 0 1))
  (h_diff' : DifferentiableOn ℝ (deriv y) (Set.Ioo 0 1))
  (h_ode : ∀ x ∈ Set.Ioo 0 1, deriv (deriv y) x + (1 / x) * deriv y x = -1)
  (h_bc1 : y 1 = 0)
  (h_bc2 : deriv y 0 = 0) :
  ∀ x ∈ Set.Icc 0 1, y x = (1 - x ^ 2) / 4 := by
  sorry

theorem theorem_720573_problem {α : Type*} (A B : Set α) :
  A = B ↔ ∀ X, X ∈ A ↔ X ∈ B := by
  sorry



theorem theorem_720339_problem
  {F : Type*} [AddCommGroup F] [Mul F] [One F]
  -- Distributive property (Left)
  (h_dist : ∀ a b c : F, a * (b + c) = a * b + a * c)
  -- Conditions derived from (F \ {0}, *) being an abelian group with identity 1
  (h_one_ne_zero : (1 : F) ≠ 0)
  (h_mul_closure : ∀ a b : F, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
  (h_mul_assoc_ne_zero : ∀ a b c : F, a ≠ 0 → b ≠ 0 → c ≠ 0 → a * b * c = a * (b * c))
  (h_mul_comm_ne_zero : ∀ a b : F, a ≠ 0 → b ≠ 0 → a * b = b * a)
  (h_mul_one_ne_zero : ∀ a : F, a ≠ 0 → a * 1 = a)
  (h_mul_inv_ne_zero : ∀ a : F, a ≠ 0 → ∃ b : F, b ≠ 0 ∧ a * b = 1) :
  -- Conclusion: F satisfies the remaining axioms required to be a Field
  (∀ a b c : F, a * b * c = a * (b * c)) ∧
  (∀ a b : F, a * b = b * a) ∧
  (∀ a : F, a * 1 = a) ∧
  (∀ a : F, 1 * a = a) ∧
  (∀ a b c : F, (a + b) * c = a * c + b * c) := by
  sorry





theorem theorem_720399_problem (R : Type*) [CommRing R] (h : IsArtinianRing R) :
  IsNoetherianRing R := by
  sorry





theorem theorem_720985_problem (A : ZFSet) (h : A ≠ ∅) : ∃ x ∈ A, x ∩ A = ∅ := by
  sorry

theorem theorem_720192_problem (R : Type*) [CommRing R]
  (h : ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0) :
  ∃ p : Polynomial R, p ≠ 0 ∧
  ∃ (S : Finset R), (∀ x ∈ S, Polynomial.eval x p = 0) ∧ S.card > p.natDegree := by
  sorry

theorem theorem_720949_problem {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  (x y : V) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  sorry





theorem theorem_720809_problem
  (p q F δ : ℝ → ℝ)
  (p_cond : ℝ → ℝ → ℝ)
  (h_delta : ∀ x, δ x ≠ 0 → x = 0)
  (h_cond_def : ∀ x y, p_cond x y = (p x * δ (y - F x)) / q y) :
  ∀ x y, p_cond x y = (p x * δ (y - F x)) / q (F x) := by
  sorry







