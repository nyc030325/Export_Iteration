import Mathlib
import Mathlib.Tactic







theorem theorem_981625_problem (X : Type*) [TopologicalSpace X]
  [CompactSpace X] [T2Space X]
  (S : Set X) (hS_open : IsOpen S) (hS_ne : S.Nonempty) :
  ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ U ⊆ S ∧ IsCompact (closure U) ∧ closure U ⊆ S := by
  sorry









theorem theorem_982185_problem (f : ℝ → ℝ → ℝ) (x b k : ℝ) 
  (hk : k > 0)
  (h_diff : DifferentiableOn ℝ (fun t => deriv (fun u => f u t) x) (Set.Icc b (b + k))) :
  ∃ y ∈ Set.Ioo b (b + k), 
    deriv (fun u => f u (b + k)) x - deriv (fun u => f u b) x = 
    k * deriv (fun t => deriv (fun u => f u t) x) y := by
  sorry



theorem theorem_981890_problem (x y z : Prop)
  (h1 : x → y)
  (h2 : x → (y → z))
  (hx : x) :
  z := by
  sorry



theorem theorem_982367_problem (f : ℝ → ℝ → ℝ)
  (h : ∀ x y : ℝ, (x, y) ≠ (0, 0) → f x y = Real.log (x^2 + (2 : ℝ)^(y^2)) / Real.sqrt (x^2 + 4 * y^2)) :
  Filter.Tendsto (fun p : ℝ × ℝ ↦ f p.1 p.2) (nhdsWithin 0 {p | p ≠ 0}) (nhds 0) := by
  sorry

theorem theorem_982501_problem
  (p : ℕ) [Fact p.Prime]
  (f : Polynomial (ZMod p))
  (hf : Irreducible f)
  (A : Polynomial (ZMod p))
  (hA : ¬ f ∣ A) :
  ∃! B : Polynomial (ZMod p) ⧸ Ideal.span {f},
    Ideal.Quotient.mk (Ideal.span {f}) A * B = 1 := by
  sorry

theorem theorem_982077_problem
  {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (l : V → ℕ) :
  Set.Nonempty { k : ℕ | (∃ v, l v = k ∧ G.degree v = 1) ∨ (∀ v, l v ≠ k) } := by
  sorry





theorem theorem_982570_problem (p q : Polynomial ℝ)
  (hp : p = 2 * (X - 1) * (X^2 - 2 * X + 2))
  (hq : q = X^2 - 1) :
  ¬ ∃ (R t : Polynomial ℝ), p * R + q * t = X + 1 := by
  sorry

theorem theorem_982940_problem (f g : ℝ → ℝ) (a : ℝ)
  (hg : DifferentiableAt ℝ g a)
  (hf : DifferentiableAt ℝ f (g a)) :
  deriv (f ∘ g) a = deriv f (g a) * deriv g a := by
  sorry





theorem theorem_982564_problem
  (t : ℕ → ℝ)
  (t0 : ℝ)
  (h_init : t 0 = t0)
  (h_rec : ∀ n : ℕ, (2 : ℝ) ^ n * t (n + 1) = (2 : ℝ) ^ n + ∑ i in Finset.range (n + 1), (Nat.choose n i : ℝ) * t i)
  (T : ℝ → ℝ)
  (h_T : ∀ z : ℝ, T z = ∑' n : ℕ, t n * z ^ n / (Nat.factorial n : ℝ)) :
  ∀ z : ℝ, deriv T (2 * z) = Real.exp (2 * z) + Real.exp z * T z := by
  sorry

theorem theorem_983418_problem (x y : ℝ) (hxy : x < y) (f : ℝ → ℝ)
  (hc : ContinuousOn f (Set.Icc x y))
  (hint : ∀ a b, a ∈ Set.Icc x y → b ∈ Set.Icc x y → a ≤ b → ∫ t in a..b, f t = 0) :
  ∀ t ∈ Set.Icc x y, f t = 0 := by
  sorry

theorem theorem_983423_problem
  (a : EuclideanSpace ℝ (Fin 3))
  (κ : ℝ)
  (hκ : 0 < κ)
  (S : Set (EuclideanSpace ℝ (Fin 3)))
  (hS : S = {γ | ‖γ - a‖ = 1 / κ}) :
  S = Metric.sphere a (1 / κ) := by
  sorry









theorem theorem_983975_problem {m : Type*} [DecidableEq m] [Fintype m]
  {R : Type*} [CommRing R] (A B : Matrix m m R) (n : ℕ)
  (h : A * B = B * A) :
  (A + B) ^ n = ∑ k in Finset.range (n + 1), (n.choose k) • (A ^ k * B ^ (n - k)) := by
  sorry

theorem theorem_983441_problem (p q n : ℕ)
  (hp : p.Prime)
  (hq : q.Prime)
  (hn : n > 2)
  (hn_even : Even n)
  (h_eq : ∑ k in Finset.range (n + 1), p^k = q^2 + q + 1) :
  p = 2 ∧ q = 5 ∧ n = 4 := by
  sorry

theorem theorem_983539_problem
  {C : Type*} [LinearOrder C]
  (is_conforming : Set C → Prop)
  (A B : Set C)
  (hA : is_conforming A)
  (hB : is_conforming B) :
  A ⊆ B ∨ B ⊆ A := by
  sorry





theorem theorem_983542_problem (a b x : ℝ)
  (h1 : a = 19)
  (h2 : b = Real.sqrt 297)
  (h3 : x = 8 / ((a - b) ^ (1 / 3 : ℝ))) :
  x = 2 * ((a + b) ^ (1 / 3 : ℝ)) := by
  sorry



theorem theorem_983742_problem :
  Filter.Tendsto (fun p : ℝ × ℝ => Real.sin p.2 / p.1) (Filter.prod Filter.atTop Filter.atTop) (nhds 0) := by
  sorry





theorem theorem_983736_problem (l : ℝ)
  (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
  (V : Submodule ℝ H) (hV : IsClosed (V : Set H))
  (v : V) :
  ‖v‖ = ‖v.1‖ := by
  sorry



theorem theorem_983900_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : E → ℝ) (R M : ℝ)
  (hR : 0 ≤ R)
  (h_conv : ConvexOn ℝ (Metric.closedBall 0 (R + 1)) f)
  (h_bound : ∀ x ∈ Metric.closedBall 0 (R + 1), |f x| ≤ M) :
  ∀ x ∈ Metric.closedBall 0 R, ∀ y ∈ Metric.closedBall 0 R,
    |f x - f y| ≤ 2 * M * ‖x - y‖ := by
  sorry

theorem theorem_984558_problem (f : ℝ → ℝ) :
  IsOpen {x | (∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ ConvexOn ℝ U f) ∨
              (∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ ConcaveOn ℝ U f)} := by
  sorry

theorem theorem_983490_problem
  (D : Type*) [LinearOrder D] [Fintype D] [SuccOrder D] [Inhabited D]
  (min_D max_D : D)
  (h_min : ∀ d, min_D ≤ d)
  (h_max : ∀ d, d ≤ max_D)
  (S : List D → List D)
  (hS_zero : S [] = [min_D])
  (hS_succ : ∀ (a : List D) (d : D), d ≠ max_D → S (a ++ [d]) = a ++ [Order.succ d])
  (hS_max : ∀ (a : List D), S (a ++ [max_D]) = (S a) ++ [min_D]) :
  (Function.Injective S) ∧
  (∀ l, S l ≠ []) ∧
  (∀ (P : List D → Prop), P [] → (∀ l, P l → P (S l)) → ∀ l, P l) := by
  sorry



theorem theorem_985239_problem (u : ℝ → ℝ)
  (h_diff_1 : Differentiable ℝ u)
  (h_diff_2 : Differentiable ℝ (deriv u))
  (h_zero : ∀ x, deriv (deriv u) x = 0) :
  ∃ a b : ℝ, ∀ x, u x = a * x + b := by
  sorry

theorem theorem_984972_problem (n : ℕ) (C : Set (Fin n → ℝ)) (h : Convex ℝ C) :
  IsPreconnected C := by
  sorry



theorem theorem_983879_problem
  (a b : ℕ → ℝ) (c d R₁ R₂ : ℝ)
  (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
  (h_conv_a : ∀ x, Summable (fun n ↦ a n * (x - c) ^ n) ↔ |x - c| < R₁)
  (h_conv_b : ∀ x, Summable (fun n ↦ b n * (x - d) ^ n) ↔ |x - d| < R₂) :
  {x | Summable (fun n ↦ a n * (x - c) ^ n)} = Set.Ioo (c - R₁) (c + R₁) ∧
  {x | Summable (fun n ↦ b n * (x - d) ^ n)} = Set.Ioo (d - R₂) (d + R₂) := by
  sorry



theorem theorem_984680_problem
  (f g : ℝ → ℝ)
  (beta c : ℝ)
  (hbc : beta < c)
  (hf : DifferentiableOn ℝ f (Set.Ioo beta c))
  (hg : DifferentiableOn ℝ g (Set.Ioo beta c))
  (hg_ne_zero : ∀ x ∈ Set.Ioo beta c, deriv g x ≠ 0)
  (h_lim_cond : (Filter.Tendsto f (nhdsWithin beta (Set.Ioi beta)) (nhds 0) ∧
                 Filter.Tendsto g (nhdsWithin beta (Set.Ioi beta)) (nhds 0)) ∨
                Filter.Tendsto (fun x ↦ f x / g x) (nhdsWithin beta (Set.Ioi beta)) (nhds 0))
  (L : ℝ)
  (h_lim_deriv : Filter.Tendsto (fun x ↦ deriv f x / deriv g x) (nhdsWithin beta (Set.Ioi beta)) (nhds L)) :
  Filter.Tendsto (fun x ↦ f x / g x) (nhdsWithin beta (Set.Ioi beta)) (nhds L) := by
  sorry

theorem theorem_985308_problem
  {K V : Type*}
  [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousSMul K V]
  (W : Submodule K V) :
  ∃ U : Submodule K V, (U : Set V) = closure (W : Set V) := by
  sorry

theorem theorem_985155_problem (x : ℝ) (h : x ∈ Set.Ioo (-1 : ℝ) 1) :
  HasDerivAt (fun y => y * Real.arcsin y + Real.sqrt (1 - y^2)) (Real.arcsin x) x := by
  sorry



theorem theorem_984868_problem (g : ℕ → ℕ) (A B : ℝ)
  (hA : 0 < A) (hB : 0 < B)
  (hg_inc : StrictMono g)
  (hg_pos : ∀ k, 0 < g k)
  (hg_growth : ∀ k, A * (g k : ℝ) ≤ (g (k + 1) : ℝ) - (g k : ℝ) ∧
                    (g (k + 1) : ℝ) - (g k : ℝ) ≤ B * (g (k + 1) : ℝ))
  (a : ℕ → ℝ)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  (ha_mono : Antitone a) :
  Summable a ↔ Summable (fun k ↦ (g k : ℝ) * a (g k)) := by
  sorry











theorem theorem_985027_problem (n : ℕ) (hn : n ≠ 0) :
  (∃ a b : ℤ, (n : ℤ) = a^2 + b^2) ↔
  (∀ p : ℕ, p.Prime → p % 4 = 3 → Even (n.factorization p)) := by
  sorry

theorem theorem_985009_problem (A : Prop) (h : ¬A → False) : A := by
  sorry

theorem theorem_985294_problem (n k : ℕ)
  (hn : n ≥ 3)
  (hk : k ≥ 3)
  (h_angle_sum : (k : ℝ) * ((n - 2 : ℝ) * Real.pi / n) < 2 * Real.pi) :
  (n = 3 ∧ k = 3) ∨
  (n = 4 ∧ k = 3) ∨
  (n = 3 ∧ k = 4) ∨
  (n = 5 ∧ k = 3) ∨
  (n = 3 ∧ k = 5) := by
  sorry











theorem theorem_983916_problem (a e d : ℝ) 
  (h_a_pos : a > 0)
  (h_geom : ∃ R > 0, 
    let s1 := 2 * R * Real.sin (Real.pi / 7)
    let s2 := 2 * R * Real.sin (2 * Real.pi / 7)
    let s3 := 2 * R * Real.sin (3 * Real.pi / 7)
    -- a is the side length (shortest chord)
    a = s1 ∧
    -- e and d are the base and equal leg respectively of an isosceles triangle
    -- formed by the vertices of the heptagon.
    -- The possible triples of sides for such triangles are {s1, s1, s2}, {s2, s2, s3}, {s3, s3, s1}.
    ( (d = s1 ∧ e = s2) ∨ 
      (d = s2 ∧ e = s3) ∨ 
      (d = s3 ∧ e = s1) )
  )
  (h_order : e < d) : 
  7 * a^2 + e^2 = 4 * d^2 := by
  sorry

theorem theorem_985228_problem (K N n : ℕ)
  (varX varY : ℝ)
  (hN : 1 < N)
  (h_varY : varY = (n : ℝ) * ((K : ℝ) / N) * (1 - (K : ℝ) / N))
  (h_varX : varX = (n : ℝ) * ((K : ℝ) / N) * (1 - (K : ℝ) / N) * (((N : ℝ) - n) / ((N : ℝ) - 1)))
  (h_nonzero : varY ≠ 0) :
  varX / varY = ((N : ℝ) - n) / ((N : ℝ) - 1) := by
  sorry





theorem theorem_985660_problem (X : Type*) [TopologicalSpace X]
  (Y Z K : Set X) (hZY : Z ⊆ Y) (hKZ : K ⊆ Z) :
  IsCompact { k : Z | k.val ∈ K } ↔ IsCompact { k : Y | k.val ∈ K } := by
  sorry



theorem theorem_985612_problem 
  (u v : ℝ × ℝ → ℝ)
  (f : ℂ → ℂ)
  (h_f : ∀ (a b : ℝ), f (Complex.mk a b) = Complex.mk (u (a, b)) (v (a, b))) :
  ∀ (c d : ℝ), (∃ z : ℂ, f z = Complex.mk c d) ↔ 
    (∃ a b : ℝ, u (a, b) = c ∧ v (a, b) = d) := by
  sorry





theorem theorem_985704_problem
  (n m : ℕ)
  (f : (Fin n → ℝ) → ℝ)
  (g : (Fin m → ℝ) → (Fin n → ℝ))
  (x : Fin m → ℝ)
  (hf : Differentiable ℝ f)
  (hg : Differentiable ℝ g) :
  fderiv ℝ (f ∘ g) x = ∑ i : Fin n, (fderiv ℝ f (g x) (Pi.single i 1)) • (fderiv ℝ (fun z => g z i) x) := by
  sorry

theorem theorem_985739_problem {R : Type*} [Ring R]
  (h : ∀ c : R, ¬ IsUnit c → ∀ a b : Rˣ, a ≠ b →
    ¬ IsUnit ((a : R) * c) ∧ ¬ IsUnit ((b : R) * c) ∧ (a : R) * c ≠ (b : R) * c) :
  ∃ x y : R, ∀ z : R, ¬ IsUnit z → z = x ∨ z = y := by
  sorry





theorem theorem_986613_problem
  (n : ℕ)
  (a b c : EuclideanSpace ℝ (Fin n))
  (t : ℝ)
  (h1 : c = a + t • (b - a))
  (h2 : t ≥ 1) :
  dist a c = dist a b + dist b c := by
  sorry

theorem theorem_986270_problem (a b : ℝ) (h1 : 0 < b) (h2 : b < a) :
  ∫ x in (0)..Real.pi, 1 / (a - b * Real.cos x) = Real.pi / Real.sqrt (a^2 - b^2) := by
  sorry







theorem theorem_986419_problem (n : ℕ) (x a_bar : Fin n → ℝ) (β : ℝ) :
  (∀ v : Fin n → ℝ, (∑ i, |v i|) ≤ 1 → (∑ i, v i * x i) ≤ β - (∑ i, a_bar i * x i)) ↔
  ((Finset.univ.sup (fun i => ‖x i‖₊)).toReal ≤ β - (∑ i, a_bar i * x i)) := by
  sorry

theorem theorem_986744_problem
  (f G : ℝ → ℝ)
  (μ R : ℝ → ℝ)
  (z z₀ : ℝ)
  (hf_diff : Differentiable ℝ f)
  (hG_cont : Continuous G)
  (hz : z₀ ≤ z)
  (hf_nonneg : ∀ x, 0 ≤ f x)
  (hG_nonneg : ∀ x, 0 ≤ G x)
  (hf_growth : f (z - z₀) - f 0 ≥ 0)
  (hR_nonneg : 0 ≤ R z)
  (h_deriv_eq : deriv μ z = (f (z - z₀) - f 0) * (∫ t in z₀..z, f (t - z₀) * G (z - t)) + R z) :
  deriv μ z ≥ 0 := by
  sorry





theorem theorem_987117_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (X : Set E) (h_compact : IsCompact X) (h_convex : Convex ℝ X) (h_nonempty : X.Nonempty)
  (f : X → X) (h_cont : Continuous f) :
  ∃ x : X, f x = x := by
  sorry



theorem theorem_986110_problem (a b c : ℝ) :
  Matrix.det !![((b + c)^2 : ℝ), a^2, a^2;
                b^2, ((c + a)^2 : ℝ), b^2;
                c^2, c^2, ((a + b)^2 : ℝ)] =
  2 * a * b * c * (a + b + c)^3 := by
  sorry

theorem theorem_986911_problem (n : ℕ) (f : Fin n → ℂ)
  (hn : 0 < n) (hf : ∀ i, f i ≠ 0) :
  (Complex.exp ((1 / (n : ℂ)) * ∑ i, Complex.log (f i))) ^ n = ∏ i, f i := by
  sorry

theorem theorem_986533_problem (a b h k : ℤ)
  (A B H K : ℤ)
  (hA : A = a / (Int.gcd a b : ℤ))
  (hB : B = b / (Int.gcd a b : ℤ))
  (hH : H = h / (Int.gcd h k : ℤ))
  (hK : K = k / (Int.gcd h k : ℤ))
  (hAB : Int.gcd A B = 1)
  (hHK : Int.gcd H K = 1) :
  Int.gcd (A * H) (B * K) = Int.gcd A K * Int.gcd B H := by
  sorry













