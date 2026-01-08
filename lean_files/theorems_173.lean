import Mathlib
import Mathlib.Tactic

















theorem theorem_947708_problem
  {α K : Type*} [AddCommGroup K] [DecidableEq α]
  (x : List α) (f : α → K)
  (h_distinct : x.Nodup) :
  (x.map f).sum = Finset.sum x.toFinset f := by
  sorry

theorem theorem_947467_problem 
  (S : Type) 
  (A bot : S) 
  (imp : S → S → S) 
  (not : S → S) 
  (derives : S → S → Prop) 
  (provable : S → Prop) 
  (h_sys_intro : ∀ φ, provable φ → provable (not (imp φ bot))) 
  (h_sys_elim : ∀ φ, provable (not φ) → derives φ bot) 
  (h1 : ¬ derives A bot) 
  (h2 : ¬ provable (not (imp A bot))) : 
  ¬ provable A ∧ ¬ provable (not A) := by
  sorry

theorem theorem_947384_problem (lam : ℝ) (w : ℝ) (hlam : 0 < lam) :
  (∑' (x : ℕ), ∑' (y : ℕ), 
    if ((x : ℝ) - (y : ℝ)) / Real.sqrt ((x : ℝ) + (y : ℝ)) = w 
    then (Real.exp (-lam) * lam ^ x / (x.factorial : ℝ)) * (Real.exp (-lam) * lam ^ y / (y.factorial : ℝ)) 
    else 0) = 
  Real.exp (-2 * lam) * ∑' (x : ℕ), ∑' (y : ℕ), 
    (lam ^ (x + y) / ((x.factorial * y.factorial) : ℝ)) * 
    (if ((x : ℝ) - (y : ℝ)) / Real.sqrt ((x : ℝ) + (y : ℝ)) = w then 1 else 0) := by
  sorry

theorem theorem_947438_problem (v : ℝ → ℝ) (n : ℕ) (x : ℝ)
  (hv : Differentiable ℝ v) (hn : 1 ≤ n)
  (h_nonzero : ∀ k ∈ Finset.Icc 1 n, v ((k : ℝ) * x ^ k) ≠ 0) :
  deriv (fun y => ∏ k in Finset.Icc 1 n, v ((k : ℝ) * y ^ k)) x =
  (∏ k in Finset.Icc 1 n, v ((k : ℝ) * x ^ k)) *
  ∑ j in Finset.Icc 1 n, ((j : ℝ) ^ 2 * x ^ (j - 1) / v ((j : ℝ) * x ^ j)) * deriv v ((j : ℝ) * x ^ j) := by
  sorry



theorem theorem_947410_problem (V : Type*) (mem : V → V → Prop)
  (w : V) (ψ : V → Prop)
  (h_replacement : ∀ (u : V) (φ : V → V → Prop),
    (∀ x y z, φ x y → φ x z → y = z) →
    ∃ v, ∀ y, mem y v ↔ ∃ x, mem x u ∧ φ x y) :
  ∃ b, ∀ x, mem x b ↔ mem x w ∧ ψ x := by
  sorry



theorem theorem_948385_problem (x y : ℝ → ℝ)
  (hx : Differentiable ℝ x)
  (hy : Differentiable ℝ y)
  (hy_ne_zero : ∀ t, y t ≠ 0)
  (hx_deriv_ne_zero : ∀ t, deriv x t ≠ 0)
  (h : ∀ t, deriv y t / deriv x t = (x t)^2 / (y t)^2) :
  ∃ C : ℝ, ∀ t, (y t)^3 = (x t)^3 + C := by
  sorry

theorem theorem_948428_problem {Ω : Type*} (f : ℕ → Ω → ℝ) (x : Ω) :
  CauchySeq (fun n => f n x) ↔
  ∀ r : ℕ, r > 0 → ∃ k : ℕ, ∀ n m : ℕ, k ≤ n → k ≤ m → |f n x - f m x| < 1 / (r : ℝ) := by
  sorry







theorem theorem_948560_problem
  (n : ℕ)
  (A Q Λ : Matrix (Fin n) (Fin n) ℝ)
  (v : Fin n → ℝ)
  (hΛ : Λ = Matrix.diagonal v)
  (hv : ∀ i, v i ≠ 0)
  (hQ : Q * Q.transpose = 1 ∧ Q.transpose * Q = 1)
  (hA : A = Q * Λ * Q⁻¹) :
  A⁻¹ = Q * Λ⁻¹ * Q.transpose := by
  sorry



theorem theorem_948591_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [SmoothManifoldWithCorners I' N]
  (f : M → N) (g : N → ℝ) (p : M) (X : TangentSpace I p)
  (hf : Smooth I I' f)
  (hg : Smooth I' (modelWithCornersSelf ℝ ℝ) g) :
  mfderiv I' (modelWithCornersSelf ℝ ℝ) g (f p) (mfderiv I I' f p X) =
  mfderiv I (modelWithCornersSelf ℝ ℝ) (g ∘ f) p X := by
  sorry

theorem theorem_948821_problem
  (d : ℕ)
  (k : ℕ)
  (Θ : Type)
  (t : ℝ → Fin k → ℝ)
  (η : Θ → Fin k → ℝ)
  (hd : d > 1)
  -- The condition that the exponent is a polynomial of degree d implies the family
  -- can represent any polynomial of the form ∑ c_j y^j (ignoring constant term).
  -- We model this by saying for any coefficients c, there exists a parameter θ
  -- such that the dot product equals the polynomial.
  (h_poly : ∀ (c : Fin d → ℝ), ∃ (θ : Θ), ∀ (y : ℝ),
    ∑ i : Fin k, η θ i * t y i = ∑ j : Fin d, c j * y ^ (j.val + 1)) :
  k > 1 := by
  sorry

theorem theorem_948223_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (P₁ P₂ : V)
  (h_neq : P₁ ≠ P₂)
  (R : V →ₗᵢ[ℝ] V)
  (L : Submodule ℝ V)
  (h_map : R P₁ = P₂)
  (h_axis : ∀ x ∈ L, R x = x) :
  ∀ x ∈ L, inner (P₂ - P₁) x = (0 : ℝ) := by
  sorry

theorem theorem_947935_problem (k : ℕ) (hk : k > 0) :
  let H : ℕ → ℝ := fun n => ∑ j in Finset.Icc 1 n, 1 / (j : ℝ)
  let H2 : ℕ → ℝ := fun n => ∑ j in Finset.Icc 1 n, 1 / ((j : ℝ) ^ 2)
  (∑' n : ℕ, if n = 0 then 0 else H n * (1 / (n : ℝ) - 1 / ((n : ℝ) + k))) =
    π ^ 2 / 6 + (H (k - 1) ^ 2 + H2 (k - 1)) / 2 := by
  sorry



theorem theorem_948908_problem {K : Type*} [Field K]
  (HasCM : EllipticCurve K → Prop)
  (E : EllipticCurve K)
  (h1 : IsIntegral ℤ E.j)
  (h2 : E.j ∉ {x | ∃ (E' : EllipticCurve K), HasCM E' ∧ E'.j = x}) :
  ¬ HasCM E := by
  sorry

theorem theorem_948685_problem (n : ℕ) (a b : Fin n → ℝ) :
  ConvexOn ℝ Set.univ (fun x => Real.log (1 + Real.exp (Matrix.dotProduct b x)) - Matrix.dotProduct a x) := by
  sorry







theorem theorem_948586_problem
  {α ι : Type*} [PartialOrder α] [Nonempty ι]
  (L : ι → LinearOrder α)
  (h_ext : ∀ i, ∀ x y, x < y → (L i).lt x y)
  (h_realizer : ∀ x y, ¬ (x ≤ y) ∧ ¬ (y ≤ x) → ∃ i j, (L i).lt x y ∧ (L j).lt y x) :
  ∀ x y, x < y ↔ ∀ i, (L i).lt x y := by
  sorry

theorem theorem_949184_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  {n : ℕ}
  (b : Basis (Fin n) K V)
  (A : V →ₗ[K] V)
  (a : Fin n → Fin n → K)
  (h : ∀ v : Fin n → K, ∑ j : Fin n, v j • (A (b j) - ∑ i : Fin n, a i j • b i) = 0) :
  ∀ k : Fin n, A (b k) = ∑ i : Fin n, a i k • b i := by
  sorry

theorem theorem_948617_problem (n m : ℕ) (hm : m > 0) :
  (∃ f : ℕ → ℝ, ∀ p : ℝ, p ∈ Set.Icc 0 1 →
    ∑ k in Finset.range (n + 1), f k * ((n.choose k) : ℝ) * p ^ k * (1 - p) ^ (n - k) = p ^ m) ↔
  m ≤ n := by
  sorry











theorem theorem_949577_problem
  {E X : Type*}
  [TopologicalSpace E] [TopologicalSpace X]
  (q : E → X)
  (h_cover : IsCoveringMap q)
  (h_compact : CompactSpace E)
  (h_closed_singletons : ∀ x : X, IsClosed ({x} : Set X)) :
  ∀ x : X, (q ⁻¹' {x}).Finite := by
  sorry







theorem theorem_948498_problem
  (A : Type*) [CommRing A]
  (S : Set A)
  (hS_one : 1 ∈ S)
  (hS_mul : ∀ x y, x ∈ S → y ∈ S → x * y ∈ S)
  (hS_zero : (0 : A) ∉ S) :
  let R : A × S → A × S → Prop :=
    fun p q ↦ ∃ u ∈ S, u * (p.1 * (q.2 : A) - q.1 * (p.2 : A)) = 0
  Equivalence R := by
  sorry

theorem theorem_949110_problem {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (W U₁ U₂ : Submodule F V)
  (h₁ : IsCompl W U₁)
  (h₂ : IsCompl W U₂) :
  Nonempty (U₁ ≃ₗ[F] U₂) := by
  sorry



theorem theorem_950229_problem (p : ℕ) [Fact p.Prime] :
  ∑' n : ℕ, ((p : ℤ_[p]) - 1) * (p : ℤ_[p]) ^ n = -1 := by
  sorry

theorem theorem_950144_problem
  (a b c : ℝ)
  (x : ℕ → ℝ)
  (h_b : b ≠ 1)
  (h_c : c ≠ 0)
  (c' : ℝ)
  (h_c' : c' = 1 - 1 / c)
  (h_rec : ∀ n : ℕ, n ≥ 1 → (x (n + 1) - 1) / (x n - 1) = a * (1 - b) * ((1 - c' * (1 - b) ^ n) / (1 - c' * (1 - b) ^ (n + 1)))) :
  ∀ n : ℕ, n ≥ 1 → x (n + 1) = 1 + (x 1 - 1) * a ^ n * (1 - b) ^ n * ((1 - c' * (1 - b)) / (1 - c' * (1 - b) ^ (n + 1))) := by
  sorry



theorem theorem_949893_problem (f : ℝ × ℝ → ℝ)
  (h : ∀ x y : ℝ, f (x, y) = if y ≠ 0 then Real.sin (x * y) / y else 0) :
  ContinuousAt f (0, 0) := by
  sorry

theorem theorem_950098_problem (p1 p2 p3 u e x1_h x2_h x3_h : ℝ)
  (h_p3 : p3 ≠ 0)
  (h_budget : p1 * x1_h + p2 * x2_h + p3 * x3_h = e) :
  x3_h = (1 / p3) * (e - p1 * x1_h - p2 * x2_h) := by
  sorry



theorem theorem_950447_problem
  {K Q : Type*} [Field K]
  (z : Fin 5 → Q → K)
  (G : Fin 5 → Fin 5 → Q → Matrix (Fin 3) (Fin 3) K)
  (h_trans : ∀ (i j : Fin 5) (q : Q) (v : Fin 3 → K),
    z i q ≠ 0 → z j q ≠ 0 →
    Matrix.mulVec (G i j q) v = (z j q / z i q) • v) :
  ∀ (i j : Fin 5) (q : Q),
    z i q ≠ 0 → z j q ≠ 0 →
    G i j q = Matrix.diagonal (fun _ ↦ z j q / z i q) := by
  sorry







theorem theorem_950701_problem (f : ℕ → ℝ) (h : f 0 = 0) :
  (∑' n, f (n + 1)) = ∑' n, f n := by
  sorry

theorem theorem_950526_problem
  (F : ℝ × ℝ → ℝ)
  (a b c : ℝ)
  (hF_smooth : ContDiff ℝ ⊤ F)
  (G : ℝ × ℝ × ℝ → ℝ := fun x ↦ F (x.1 - x.2.1, x.2.1 - x.2.2))
  (hG_zero : G (a, b, c) = 0)
  (h_deriv : - deriv (fun y ↦ F (a - b, y)) (b - c) ≠ 0) :
  ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (a, b) ∈ U ∧
  ∃ h : ℝ × ℝ → ℝ, ContDiffOn ℝ ⊤ h U ∧
  ∀ x ∈ U, G (x.1, x.2, h x) = 0 := by
  sorry



theorem theorem_950628_problem {α : Type*} (f g : α → α) (h : α ≃ α) :
  g = h.symm ∘ f ∘ h ↔ ∀ x, f (h x) = h (g x) := by
  sorry







theorem theorem_951707_problem
  (a b : ℕ → ℕ → ℝ)
  (h : ∀ n m, (∀ i j, i ≤ n → j ≤ m → (i ≠ n ∨ j ≠ m) → a i j = b i j) → a n m = b n m) :
  ∀ n m, a n m = b n m := by
  sorry



theorem theorem_951648_problem (P : Polynomial ℚ)
  (h_deg : P.degree ≠ 0)
  (h_no_roots : ∀ x : ℚ, ¬ P.IsRoot x)
  (h_no_factor : ¬ ∃ (A B : Polynomial ℚ), P = A * B ∧ A.degree < P.degree ∧ B.degree < P.degree) :
  Irreducible P := by
  sorry















theorem theorem_951928_problem (x : ℝ) (h1 : 0 ≤ x) (h2 : x ≠ 0) :
  (∑' n : ℕ, if n = 0 then 0 else ((-1 : ℝ) ^ n * x ^ (n - 1)) / (2 * (n : ℝ) - 1)) =
  -Real.arctan (Real.sqrt x) / Real.sqrt x := by
  sorry





theorem theorem_953022_problem
  {G A : Type*} [Group G] [MulAction G A] (a : A)
  (h : ∃ g : G, g • a ≠ a) :
  (MulAction.stabilizer G a).index > 1 := by
  sorry



theorem theorem_952837_problem
  (n : ℕ)
  (f : ℝ → ℝ)
  (I : Set ℝ)
  (h_convex : Convex ℝ I)
  (a x : ℝ)
  (ha : a ∈ I)
  (hx : x ∈ I)
  (h_neq : a ≠ x)
  (h_diff : ContDiffOn ℝ (n + 1) f I) :
  ∃ c ∈ Set.Ioo (min a x) (max a x),
    f x - (∑ k in Finset.range (n + 1), (iteratedDeriv k f a) / (k.factorial : ℝ) * (x - a) ^ k) =
    (iteratedDeriv (n + 1) f c) / ((n + 1).factorial : ℝ) * (x - a) ^ (n + 1) := by
  sorry





theorem theorem_952776_problem (n k : ℕ) (hkn : k ≤ n) :
  ∑ i in Finset.range (k + 1), (-1 : ℤ)^i * (i : ℤ) * (Nat.choose n i) * (Nat.choose n (k - i)) =
  if k = 0 then 0
  else (-1 : ℤ)^(1 + (k - 1) / 2) * (n : ℤ) * (Nat.choose (n - 1) ((k - 1) / 2)) := by
  sorry



theorem theorem_953220_problem
  (G : Type*) [Group G] [Finite G]
  (A : Subgroup G)
  (phi : A ≃* A) :
  ∃ (X : Type*) (_ : Group X) (_ : Finite X),
    ∃ (i : G →* X) (g : X),
      Function.Injective i ∧ ∀ (a : A), g⁻¹ * i a * g = i (phi a) := by
  sorry

theorem theorem_953401_problem 
  -- Abstract types representing the function spaces
  (U F : Type*) [Norm U] [Norm F]
  -- Parameter T for the time interval (0, T)
  (T : ℝ) (hT : T > 0)
  -- Abstract representation of the specific norms used in the inequality
  (norm_L2_u : U → ℝ) -- Represents ||u||_{L^2(Ω × (0,T))}
  (norm_Holder : U → ℝ → ℝ → ℝ) -- Represents ||u||_{C^α(Ω × [σ,T])} taking u, α, σ
  -- Abstract predicate for "u is a solution to the PDE with forcing f"
  (is_pde_solution : U → F → Prop)
  -- The variables given in the problem
  (u : U) (f : F)
  (h_sol : is_pde_solution u f) :
  -- The conclusion to be proved
  ∃ C > 0, ∃ α, 0 < α ∧ α < 1 ∧ 
    ∀ σ, 0 < σ → σ < T → 
      norm_Holder u α σ ≤ C * (‖f‖ + norm_L2_u u) := by
  sorry







theorem theorem_953312_problem (a b c : ℝ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hsum : a + b + c = 3)
  (hprod : a * b * c = 1) :
  a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1)) ≤ 3 / 4 := by
  sorry





theorem theorem_954142_problem (B : ℕ → Set ℝ)
  (h_finite : ∀ n, (B n).Finite) :
  ¬ (∀ x : ℝ, Filter.Tendsto (fun n ↦ Set.indicator (B n) (fun _ ↦ (1 : ℝ)) x) Filter.atTop (nhds 1)) := by
  sorry

theorem theorem_953906_problem (d : List ℕ) (n : ℕ)
  (h_distinct : d.Nodup)
  (h_digits : ∀ x ∈ d, x < 10)
  (h_n : n = d.length) :
  (d.permutations.map (fun l => l.foldl (fun acc x => 10 * acc + x) 0)).sum = 
  d.sum * Nat.factorial (n - 1) * (∑ k in Finset.range n, 10^k) := by
  sorry



theorem theorem_954212_problem (n : ℕ) (A : Set (Fin n → ℝ))
  (h_open : IsOpen A) (h_connected : IsConnected A) :
  IsPathConnected A := by
  sorry

theorem theorem_954095_problem (x y : ℝ) (h : x^2 + y^2 > 0) :
  ∫ z : ℝ, 1 / Real.sqrt ((x^2 + y^2 + z^2) ^ 3) = 2 / (x^2 + y^2) := by
  sorry







