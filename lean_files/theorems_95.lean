import Mathlib
import Mathlib.Tactic

theorem theorem_511163_problem {R : Type*} [Ring R] (a b : R) :
  (b + a) + ((-a) + (-b)) = 0 := by
  sorry

theorem theorem_510980_problem
  (f : ℝ → ℝ)
  (h_f : ∀ x, f x = Int.fract (2 * x))
  (b : ℕ → ℕ)
  (h_b_bin : ∀ n, b n = 0 ∨ b n = 1)
  (x : ℝ)
  (h_x_mem : x ∈ Set.Ico 0 1)
  (h_x_eq : x = ∑' n, (b n : ℝ) / 2 ^ (n + 1)) :
  ∀ n : ℕ, f^[n] x = ∑' k, (b (n + k) : ℝ) / 2 ^ (k + 1) := by
  sorry



theorem theorem_511185_problem
  (M : Type*)
  (T_star_M : Type*)
  (π : T_star_M → M)
  (CotangentSpace : M → Set T_star_M)
  (h_fiber : ∀ p : M, CotangentSpace p = π ⁻¹' {p})
  (s : M → T_star_M)
  (h_section : π ∘ s = id) :
  ∀ p : M, s p ∈ CotangentSpace p := by
  sorry

theorem theorem_511237_problem (L : Set ℝ)
  (hL : L = {0} ∪ {x | ∃ n : ℕ, n ≠ 0 ∧ x = 1 / (n : ℝ)}) :
  IsCompact L := by
  sorry









theorem theorem_511149_problem (k : ℕ) (hk : 0 < k) :
  Set.Finite {i : ℕ | 0 < i ∧ Nat.totient i = k} := by
  sorry

theorem theorem_511681_problem (a K : ℝ) (f : ℝ → ℝ)
  (hK : 0 < K)
  (hf_cont : ContinuousOn f (Set.Ici a))
  (hf_nonneg : ∀ t, a ≤ t → 0 ≤ f t)
  (h_deriv : ∀ t, a ≤ t → deriv (fun x => Real.exp (-K * (x - a)) * ∫ s in a..x, f s) t ≤ 0) :
  ∀ t, a ≤ t → f t = 0 := by
  sorry

theorem theorem_511486_problem (a b : ℕ) 
  (ha : a > 0) (hb : b > 0) 
  (h_gcd : Nat.gcd a b = 1) : 
  (Nat.factors (a * b)).length = (Nat.factors a).length + (Nat.factors b).length := by
  sorry



theorem theorem_510572_problem
  (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
  (m : ℕ) (hm : m > 0)
  (k_minus k_plus : ℕ)
  (h_k_minus_range : k_minus ∈ Finset.Icc 1 m)
  (h_k_minus_prop : a ^ k_minus * b ^ (m - k_minus) < b ^ m)
  (h_k_minus_max : ∀ i ∈ Finset.Icc 1 m, a ^ i * b ^ (m - i) < b ^ m → a ^ i * b ^ (m - i) ≤ a ^ k_minus * b ^ (m - k_minus))
  (h_k_plus_range : k_plus ∈ Finset.Icc 1 m)
  (h_k_plus_prop : a ^ k_plus * b ^ (m - k_plus) > b ^ m)
  (h_k_plus_min : ∀ i ∈ Finset.Icc 1 m, a ^ i * b ^ (m - i) > b ^ m → a ^ k_plus * b ^ (m - k_plus) ≤ a ^ i * b ^ (m - i)) :
  a ^ k_minus * b ^ (m - k_minus) < b ^ m ∧ b ^ m < a ^ k_plus * b ^ (m - k_plus) := by
  sorry







theorem theorem_511920_problem
  (f : ℝ → ℝ) (p : ℝ)
  (h_diff : ContDiff ℝ 1 f)
  (h_conv : ∃ δ > 0, ∀ x₀, dist x₀ p < δ →
    Filter.Tendsto (fun n ↦ f^[n] x₀) Filter.atTop (nhds p)) :
  f p = p := by
  sorry

theorem theorem_511923_problem {α I : Type*} (hI : Nonempty I) (X : I → Set α) :
  Set.pi Set.univ X = {f : I → α | ∀ i, f i ∈ X i} := by
  sorry

theorem theorem_512186_problem :
  Filter.Tendsto (fun x : ℝ => Real.log x / (x^2 + x - 2)) (nhdsWithin 1 {1}ᶜ) (nhds ((1 : ℝ) / 3)) := by
  sorry

theorem theorem_512079_problem (a b : ℝ) (h_ab : a < b) (f : ℝ → ℝ)
  (hf : UniformContinuousOn f (Set.Icc a b)) :
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
    |x - y| < δ → |f x - f y| < ε / (b - a) := by
  sorry

theorem theorem_512003_problem (n : ℕ) (β : Equiv.Perm (Fin n)) :
  let count (i : Fin n) := (Finset.univ.filter (λ x : Fin n => x < β i ∧ ∀ j : Fin n, j < i → β j ≠ x)).card
  let lex_lt (p1 p2 : Equiv.Perm (Fin n)) := ∃ i : Fin n, p1 i < p2 i ∧ ∀ j : Fin n, j < i → p1 j = p2 j
  let index := (Finset.univ.filter (λ p => lex_lt p β)).card + 1
  index = 1 + ∑ i : Fin n, (count i) * (n - 1 - i).factorial := by
  sorry







theorem theorem_510047_problem :
  ∃ ε > 0, ∀ x : ℝ, 0 < x ∧ x < ε →
  Real.log (1 + x) ≥ (2 * x) / (x + 2) - x^2 / (3 * (x + 2)^2) := by
  sorry





theorem theorem_513202_problem (f g : ℝ → ℝ)
  (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
  deriv (fun x => f x * Real.exp (g x)) = fun x => Real.exp (g x) * (deriv f x + deriv g x * f x) := by
  sorry



theorem theorem_513419_problem (ε : ℝ) (hε : 0 < ε) :
  Summable (fun n : ℕ => if n ≥ 2 then 1 / ((n : ℝ) * (Real.log n) ^ (2 + ε)) else 0) := by
  sorry





theorem theorem_513118_problem 
  -- Setup: Indices for the multi-sorted structure
  (I J : Type)
  -- L: First-order language (represented as a type of Formulas)
  (Formula : Type)
  -- M: The class of Multi-sorted structures
  (Structure : Type)
  -- Components of M: Domains D_i (Type allows empty) and Relations R_j
  (D : Structure → I → Type)
  (R : Structure → J → Type)
  -- Semantics: M ⊨ φ
  (satisfies : Structure → Formula → Prop)
  -- Definition: φ is a tautology iff it is satisfied in all structures M
  (is_tautology : Formula → Prop)
  (h_tautology_def : ∀ φ, is_tautology φ ↔ ∀ (M : Structure), satisfies M φ)
  -- Syntax: T is the set of derivable formulas (Valby's axiomatization)
  (is_derivable : Formula → Prop) :
  -- Conclusion: φ is a tautology iff φ is derivable (T ⊨ φ)
  ∀ φ : Formula, is_tautology φ ↔ is_derivable φ := by
  sorry







theorem theorem_513356_problem
  (n p : ℕ)
  (X : Matrix (Fin n) (Fin p) ℝ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (H : Matrix (Fin p) (Fin p) ℝ)
  (hA_diag : ∀ i j, i ≠ j → A i j = 0)
  (hA_pos : ∀ i, 0 < A i i)
  (hH : H = X.transpose * A * X) :
  H.PosDef ↔ X.rank = p := by
  sorry

theorem theorem_513220_problem (p : ℕ) (a : ℤ)
  (hp : Nat.Prime p)
  (h : ¬ (p : ℤ) ∣ a) :
  a ^ (p - 1) ≡ 1 [ZMOD p] := by
  sorry





theorem theorem_512380_problem (a b m n p x : ℝ)
  (h_neq : a ≠ b)
  (h_np : n > p)
  (h_sum : m / n + p / n = 2)
  (hx_a : x + a > 0)
  (hx_b : x + b > 0) :
  deriv (fun x => (n / ((n - p) * (a - b))) * ((x + b) / (x + a)) ^ ((n - p) / n)) x =
  1 / ((x + a) ^ (m / n) * (x + b) ^ (p / n)) := by
  sorry

theorem theorem_513439_problem
  {M V : Type*}
  -- P is the abstract position vector field (geometric object)
  (P : M → V)
  -- phi is the unprimed coordinate map Z
  (phi : M → V)
  -- phi' is the primed coordinate map Z'
  (phi' : M → V)
  -- Z is the coordinate transformation function mapping primed to unprimed coordinates
  (Z : V → V)
  -- The relationship between the coordinate systems via the transformation
  (h_trans : ∀ p : M, phi p = Z (phi' p))
  -- R is the representation of the position vector in unprimed coordinates
  (R : V → V)
  (h_R : ∀ p : M, R (phi p) = P p)
  -- R_prime is the representation of the position vector in primed coordinates
  (R_prime : V → V)
  (h_R_prime : ∀ p : M, R_prime (phi' p) = P p)
  -- Assumption that the primed coordinates cover the vector space
  (h_surj : Function.Surjective phi') :
  -- The identity to be proved: R(Z') = R(Z(Z'))
  ∀ z_prime : V, R_prime z_prime = R (Z z_prime) := by
  sorry

theorem theorem_513501_problem :
  Summable (fun k : ℕ => if 3 ≤ k then (-1 : ℝ) ^ k / ((k : ℝ) + Real.sqrt k) else 0) := by
  sorry



theorem theorem_513586_problem (n m : ℕ) (bounds : Fin n → ℕ)
  (h_bounds : ∀ i, bounds i ≤ m)
  (d1 d2 : Fin n → ℕ)
  (h_d1 : ∀ i, d1 i ≤ bounds i)
  (h_d2 : ∀ i, d2 i ≤ bounds i)
  (h_eq : ∑ i : Fin n, d1 i * (m + 1) ^ (i : ℕ) = ∑ i : Fin n, d2 i * (m + 1) ^ (i : ℕ)) :
  d1 = d2 := by
  sorry





theorem theorem_513670_problem (a b : ℝ) (f : ℕ → ℝ → ℝ)
  (h_pointwise : ∀ x ∈ Set.Icc a b, Filter.Tendsto (fun n ↦ f n x) Filter.atTop (nhds 0))
  (h_sup : Filter.Tendsto (fun n ↦ ⨆ x ∈ Set.Icc a b, |f n x|) Filter.atTop (nhds 0)) :
  TendstoUniformlyOn f 0 Filter.atTop (Set.Icc a b) := by
  sorry

theorem theorem_513909_problem
  -- Context: X is a smooth projective variety (abstracted to Type with geometric structures)
  (X : Type*) (Divisor : Type*) (PicX : Type*) 
  (PicXX : Type*) (PicXXn : Type*)
  [AddCommGroup Divisor] [CommGroup PicX] [CommGroup PicXXn]
  (n : ℕ)
  
  -- Maps relating Divisors and Line Bundles
  (L : Divisor → PicX)
  (toDiv : X → Divisor) -- Points regarded as divisors
  
  -- The Diagonal Bundle on X × X
  (L_Delta : PicXX)
  
  -- Pullback maps for p and q_{0i} on Picard groups
  -- p : X × X^n → X
  (p_star : PicX → PicXXn)
  -- q_{0i} : X × X^n → X × X, indexed by Fin n
  (q_star : Fin n → PicXX → PicXXn)
  
  -- Restriction map to the slice X × {(P_1, ..., P_n)}
  -- The slice is isomorphic to X, so the codomain is PicX.
  -- The map depends on the choice of points P_1, ..., P_n.
  (slice_restrict : (Fin n → X) → PicXXn → PicX)
  
  -- Hypotheses encoding the geometric definitions of p, q, and the slice
  
  -- 1. Restriction is a group homomorphism
  (h_restrict_mul : ∀ (pts : Fin n → X) (A B : PicXXn), 
    slice_restrict pts (A * B) = slice_restrict pts A * slice_restrict pts B)
    
  -- 2. Geometric property of the diagonal pullback:
  -- The map x ↦ (x, P_i) pulls back the diagonal to P_i.
  (h_restrict_q : ∀ (pts : Fin n → X) (i : Fin n), 
    slice_restrict pts (q_star i L_Delta) = L (toDiv (pts i)))
    
  -- 3. Geometric property of the projection p:
  -- The map x ↦ x pulls back any bundle F on X to F itself.
  (h_restrict_p : ∀ (pts : Fin n → X) (F : PicX), 
    slice_restrict pts (p_star F) = F)
    
  -- 4. Linearity properties of L
  (h_L_add : ∀ (D1 D2 : Divisor), L (D1 + D2) = L D1 * L D2)
  (h_L_zsmul : ∀ (k : ℤ) (D : Divisor), L (k • D) = (L D) ^ k)
  
  -- Given points P_0 and P_1, ..., P_n
  (P0 : X)
  (Ps : Fin n → X) :
  -- Define M as in the problem
  let M := (∏ i : Fin n, q_star i L_Delta) * (p_star (L (toDiv P0))) ^ (-(n : ℤ))
  -- Conclusion: Restriction of M is L(Sum P_i - n P_0)
  slice_restrict Ps M = L ((∑ i : Fin n, toDiv (Ps i)) - n • toDiv P0) := by
  sorry

theorem theorem_513343_problem (n : ℕ) (hn : n > 0) (C : Set (Fin n → ℝ))
  (h_convex : Convex ℝ C)
  (h_compact : IsCompact C)
  (h_interior : (interior C).Nonempty) :
  ¬ Convex ℝ (frontier C) := by
  sorry



theorem theorem_514491_problem
  -- Let R be a commutative ring with unity.
  (R : Type*) [CommRing R]
  -- We abstract the homological setting.
  -- HM_Z and HN_Z represent H_n(M; ℤ) and H_n(N; ℤ).
  (HM_Z HN_Z : Type*) [AddCommGroup HM_Z] [AddCommGroup HN_Z]
  -- HM_R and HN_R represent H_n(M; R) and H_n(N; R).
  (HM_R HN_R : Type*) [AddCommGroup HM_R] [Module R HM_R] [AddCommGroup HN_R] [Module R HN_R]
  -- f_star_Z represents the induced homomorphism f_*: H_n(M; ℤ) → H_n(N; ℤ).
  (f_star_Z : HM_Z →+ HN_Z)
  -- f_star_R represents the induced homomorphism f_*: H_n(M; R) → H_n(N; R).
  (f_star_R : HM_R →ₗ[R] HN_R)
  -- [M] and [N] are generators in integer homology.
  (genM_Z : HM_Z) (genN_Z : HN_Z)
  -- 1_R are generators in homology with coefficients in R.
  (genM_R : HM_R) (genN_R : HN_R)
  -- There exist natural change-of-coefficient maps ρ: H_n(-; ℤ) → H_n(-; R).
  (rhoM : HM_Z →+ HM_R) (rhoN : HN_Z →+ HN_R)
  -- The induced map commutes with the change of coefficients (naturality).
  (h_naturality : ∀ x, f_star_R (rhoM x) = rhoN (f_star_Z x))
  -- The generator 1_R corresponds to the image of the integer generator under ρ.
  (h_genM_R : rhoM genM_Z = genM_R)
  (h_genN_R : rhoN genN_Z = genN_R)
  -- The integer degree d(f) is defined by f_*([M]) = d(f) · [N].
  (d : ℤ)
  (h_d : f_star_Z genM_Z = d • genN_Z)
  -- The degree d_R(f) is defined as the image of the generator 1_R under f_*.
  (dR : HN_R)
  (h_dR : dR = f_star_R genM_R) :
  -- Prove that d_R(f) = d(f) · 1_R.
  dR = d • genN_R := by
  sorry

theorem theorem_513575_problem
  {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  (f : X → Y)
  (h_iso : Isometry f)
  (h_surj : Function.Surjective f)
  (h_comp_X : CompleteSpace X) :
  CompleteSpace Y := by
  sorry







theorem theorem_514296_problem (h a θ : ℝ) (ha : a ≠ 0) :
  Filter.Tendsto (fun ε => (ε * h * Real.sin θ) / (1 + ε * a⁻¹ * h * Real.cos θ) / ε) 
    (nhds 0) (nhds (h * Real.sin θ)) := by
  sorry

theorem theorem_514091_problem (a b : ℝ) (f : ℝ → ℝ) (hab : a ≤ b)
  (h_dec : AntitoneOn f (Set.Icc a b))
  (h_ivp : ∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x < y →
    ∀ k, f y < k → k < f x → ∃ c ∈ Set.Ioo x y, f c = k) :
  ContinuousOn f (Set.Icc a b) := by
  sorry

theorem theorem_514061_problem
  (T : ℝ) (hT : T > 0)
  (f : ℝ → ℝ → ℝ)
  (L : ℝ) (hL : L > 0)
  (hf_lip : ∀ t ∈ Set.Icc 0 T, ∀ u v : ℝ, |f t u - f t v| ≤ L * |u - v|)
  (g : ℝ → ℝ)
  (M : ℝ)
  (hg_bound : ∀ t ∈ Set.Icc 0 T, |g t| ≤ M)
  (x y : ℝ → ℝ)
  (hx_diff : Differentiable ℝ x)
  (hy_diff : Differentiable ℝ y)
  (hx_ode : ∀ t ∈ Set.Icc 0 T, deriv x t = f t (x t))
  (hy_ode : ∀ t ∈ Set.Icc 0 T, deriv y t = f t (y t) + g t)
  (d₀ : ℝ)
  (h_init : |x 0 - y 0| = d₀) :
  ∀ t ∈ Set.Icc 0 T, |x t - y t| ≤ d₀ * Real.exp (L * t) + (M / L) * (Real.exp (L * t) - 1) := by
  sorry



theorem theorem_514140_problem (K : Type*) [Field K] :
  ¬ Algebra.FiniteType K (RatFunc K) := by
  sorry



theorem theorem_514085_problem (N : ℕ)
  (chi : (Fin N → ℤ) → ℤ)
  (phi : (Fin N → ℤ) → (Fin N → ℤ))
  (h_phi_sorted : ∀ v, Monotone (phi v))
  (h_phi_perm : ∀ v, ∃ σ : Equiv.Perm (Fin N), phi v = v ∘ σ) :
  let h := fun v => chi (phi v)
  ∀ (v : Fin N → ℤ) (σ : Equiv.Perm (Fin N)), h v = h (v ∘ σ) := by
  sorry









theorem theorem_514031_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]
  (t : V →ₗ[F] V)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (k : ι → ℕ)
  (v : ι → V)
  -- The properties of the t-strings
  (h_end : ∀ i, (t ^ (k i + 1)) (v i) = 0)
  (h_last_ne_zero : ∀ i, (t ^ (k i)) (v i) ≠ 0)
  -- The collection constitutes a basis.
  -- We represent the basis indexed by the dependent pair (i, j)
  (b : Basis (Σ i, Fin (k i + 1)) F V)
  (hb : ∀ i j, b ⟨i, j⟩ = (t ^ (j : ℕ)) (v i)) :
  -- Define V_i as the span of the i-th string
  let V_i := fun i => Submodule.span F (Set.range (fun (j : Fin (k i + 1)) => (t ^ (j : ℕ)) (v i)))
  -- Conclusions:
  (∀ i, Submodule.map t (V_i i) ≤ V_i i) ∧
  DirectSum.IsInternal V_i := by
  sorry

theorem theorem_514570_problem (n : ℕ)
  (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
  (hf : ContinuousOn f (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
  ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, f x = f (-x) := by
  sorry

theorem theorem_514721_problem {α : Type} (P : α → Prop)
  (h : ∃ x, ¬ P x) :
  ¬ (∀ x, P x) := by
  sorry







theorem theorem_514940_problem (x : ℝ) (hx : x ≠ 0) :
  HasDerivAt (fun t => t * Real.exp (t + 1 / t)) 
    ((1 + x - 1 / x) * Real.exp (x + 1 / x)) x := by
  sorry

theorem theorem_514829_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (R : V → V → V → V → ℝ)
  (c : ℝ)
  -- Linearity of the tensor (implied by definition of Riemann curvature tensor)
  (h_lin : ∀ x1 x2 y z w, R (x1 + x2) y z w = R x1 y z w + R x2 y z w)
  (h_smul : ∀ (a : ℝ) x y z w, R (a • x) y z w = a * R x y z w)
  -- Symmetries of the Riemann curvature tensor
  (h_anti1 : ∀ x y z w, R x y z w = - R y x z w)
  (h_anti2 : ∀ x y z w, R x y z w = - R x y w z)
  (h_pair : ∀ x y z w, R x y z w = R z w x y)
  (h_bianchi : ∀ x y z w, R x y z w + R y z x w + R z x y w = 0)
  -- Condition: Constant sectional curvature K(P) = c
  -- Rewritten as R(x,y,y,x) = c * |x ∧ y|² to avoid division and cover dependent vectors trivially
  (h_const : ∀ x y : V, R x y y x = c * (inner x x * inner y y - (inner x y)^2)) :
  -- Conclusion: The specific form of the curvature tensor
  ∀ x y z w, R x y z w = c * (inner x z * inner y w - inner x w * inner y z) := by
  sorry

theorem theorem_514456_problem :
  ∫ x in Set.Ici 0, |Real.sin x| * Real.exp (-x) = (1 / 2 : ℝ) * ((Real.exp Real.pi + 1) / (Real.exp Real.pi - 1)) := by
  sorry



theorem theorem_514931_problem
  (P Q : Fin 3 → Projectivization (ZMod 2) (Fin 3 → ZMod 2))
  (hP : Projectivization.Independent P)
  (hQ : Projectivization.Independent Q) :
  ∃ g : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2),
    ∀ i, Submodule.map (g : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) (P i).submodule = (Q i).submodule := by
  sorry

theorem theorem_515125_problem (u : ℝ → ℝ) (hu : Differentiable ℝ u)
  (h : ∀ x, deriv u x = Real.sqrt (2 * (1 - Real.cos (u x)))) :
  ∀ x, -(1 / 2) * (deriv u x)^2 + (1 - Real.cos (u x)) = 0 := by
  sorry

theorem theorem_514178_problem
  (S : Set ℝ) (hS : S = Set.Ioo (-1 : ℝ) 1 ∪ {2})
  (A_real : Set ℝ) (hA : A_real = Set.Ioo (-1 : ℝ) 1)
  (x_real : ℝ) (hx : x_real = 2)
  (h_sub : A_real ⊆ S)
  (h_mem : x_real ∈ S) :
  let X := { s // s ∈ S }
  let x : X := ⟨x_real, h_mem⟩
  let A : Set X := { a : X | a.val ∈ A_real }
  ¬ ∃ v ∈ closure A, dist x v = Metric.infDist x A := by
  sorry



theorem theorem_515181_problem (a b c d : ℝ)
  (G : Matrix (Fin 2) (Fin 2) ℝ)
  (hG : G = !![a, b; c, d])
  (X : Matrix (Fin 2) (Fin 2) ℝ)
  (h : (8 : ℝ) • (G * X) = X * X.transpose) :
  X.det = 0 ∨ X.det = 64 * (a * d - b * c) := by
  sorry



theorem theorem_515626_problem (S : ℕ → ℝ)
  (hS : ∀ n : ℕ, S n = (1 / (n : ℝ)) * ∑ i in Finset.Icc 1 n, Real.sin ((i : ℝ) * Real.pi / (n : ℝ))) :
  Filter.Tendsto S Filter.atTop (nhds (2 / Real.pi)) := by
  sorry

theorem theorem_514847_problem
  (a : ℕ → Fin 10)
  (r : ℝ)
  (h_r_def : r = ∑' n, (a (n + 1) : ℝ) / 10 ^ (n + 1))
  (h_irr_r : Irrational r)
  (b : ℕ → Fin 10)
  (h_b_def : ∀ n : ℕ, 0 < n →
    ∀ k : ℕ, (n * (n - 1)) / 2 < k ∧ k ≤ (n * (n + 1)) / 2 → b k = a n)
  (g : ℝ)
  (h_g_def : g = ∑' k, (b (k + 1) : ℝ) / 10 ^ (k + 1)) :
  Irrational g := by
  sorry

theorem theorem_515606_problem (b : ℝ) (h1 : 0 < b) (h2 : b ≤ 1 / 3) :
  Real.log ((2 * b^6 - 5 * b^5 - 2 * b^4 + 15 * b^3 - 19 * b^2 + 8 * b + 3) / 
  (-b^4 + 2 * b^3 - b^2 + 2)) + 2 * b * Real.log b ≥ 0 := by
  sorry

theorem theorem_515515_problem 
  {ΓM ΓM' : Type*} [AddCommGroup ΓM] [AddCommGroup ΓM']
  -- D and D' are connections, modeled as maps taking two sections to a section
  (D : ΓM → ΓM → ΓM)
  (D' : ΓM' → ΓM' → ΓM')
  -- f^*D' is the pullback connection on M
  (f_star_D' : ΓM → ΓM → ΓM)
  -- Maps induced by f and the bundle isomorphism
  -- pull_Y represents Y ↦ f^*Y (from M' to M via identification)
  (pull_Y : ΓM' → ΓM)
  -- push_X represents X ↦ f_*X (from M to M')
  (push_X : ΓM → ΓM')
  -- iso_back represents the identification of the result D'_{f_*X}Y (in f^*TM') with a section in TM
  (iso_back : ΓM' → ΓM)
  -- Condition: The identification of bundles implies surjectivity of section pullback
  (h_iso_surj : Function.Surjective pull_Y)
  -- Condition: Definition of the pullback connection f^*D' given in the problem
  -- (f^*D')_X (f^*Y) = D'_{f_*X} Y
  (h_pullback_def : ∀ (X : ΓM) (Y : ΓM'), f_star_D' X (pull_Y Y) = iso_back (D' (push_X X) Y))
  -- Condition: Definition of connection-preserving
  -- f is connection-preserving iff D respects the structure of D' under f
  (is_connection_preserving : Prop)
  (h_preserving_def : is_connection_preserving ↔ ∀ (X : ΓM) (Y : ΓM'), D X (pull_Y Y) = iso_back (D' (push_X X) Y)) :
  -- Question: Prove equivalence
  is_connection_preserving ↔ f_star_D' = D := by
  sorry



theorem theorem_515413_problem
  {D : Type*}
  (S : Set D)
  (f : D → ℝ)
  (x_star : D)
  (h_x : x_star ∈ S) :
  (∀ x ∈ S, f x ≤ f x_star) ↔ (∀ x ∈ S, -f x_star ≤ -f x) := by
  sorry

theorem theorem_515453_problem (E : Type*) [Field E] [Algebra ℚ E]
  [FiniteDimensional ℚ E] [IsGalois ℚ E] :
  Fintype.card (E ≃ₐ[ℚ] E) = FiniteDimensional.finrank ℚ E := by
  sorry

theorem theorem_515291_problem (k : ℕ) (a : Fin k → ℤ) (n : Fin k → ℕ)
  (h_cover_nat : ∀ m : ℕ, ∃ i : Fin k, (m : ℤ) ≡ a i [ZMOD n i]) :
  ∀ z : ℤ, ∃ i : Fin k, z ≡ a i [ZMOD n i] := by
  sorry



theorem theorem_515388_problem {R : Type*} [CommRing R] (p : PowerSeries R) :
  IsUnit p ↔ IsUnit (PowerSeries.coeff R 0 p) := by
  sorry

theorem theorem_515657_problem (n : ℕ) (X A : Matrix (Fin n) (Fin n) ℝ) :
  ∀ i j : Fin n, (X.transpose * A * X) i j = ∑ k : Fin n, ∑ l : Fin n, X k i * A k l * X l j := by
  sorry

theorem theorem_516167_problem :
  sSup ((fun y => sInf ((fun x => Real.sin (x + y)) '' Set.Icc 0 (2 * Real.pi))) '' Set.Icc 0 (2 * Real.pi)) = -1 := by
  sorry



theorem theorem_516209_problem (x : ℝ) (hx : 0 < x)
  (α β : ℕ → ℝ) (F : ℝ → ℝ) :
  ∑ n in Finset.Icc 1 (Nat.floor x), α n * (∑ m in Finset.Icc 1 (Nat.floor (x / n)), β m * F (x / (n * m))) =
  ∑ k in Finset.Icc 1 (Nat.floor x), (∑ n in Nat.divisors k, α n * β (k / n)) * F (x / k) := by
  sorry





