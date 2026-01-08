import Mathlib
import Mathlib.Tactic





theorem theorem_6488_problem (a₁ a₂ : ℝ) :
  sSup {y | ∃ x₁ x₂ : ℝ, |x₁| + |x₂| = 1 ∧ y = |a₁ * x₁ + a₂ * x₂|} = max |a₁| |a₂| := by
  sorry



theorem theorem_5843_problem
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {Ω : Type*}
  (E : (Ω → ℝ) → ℝ)
  (hE_linear : ∀ (f g : Ω → ℝ) (c : ℝ), E (fun ω ↦ c * f ω + g ω) = c * E f + E g)
  (X : Ω → Matrix m n ℝ)
  (u : Ω → n → ℝ)
  (G : Matrix m n ℝ) -- Note: G must be m×n for Xᵀ G u to be defined (Xᵀ is n×m, u is n×1)
  (h_uncorr : ∀ (i : m) (j : n) (k : n), E (fun ω ↦ X ω i j * u ω k) = 0) :
  ∀ (k : n), E (fun ω ↦ Matrix.mulVec ((X ω).transpose * G) (u ω) k) = 0 := by
  sorry











theorem theorem_5517_problem (A B C : ℝ × ℝ)
  (hA : A = (1, 1.7))
  (hB : B = (-2, 0))
  (hC : C = (1, -1.7)) :
  ¬ Collinear ℝ ({A, B, C} : Set (ℝ × ℝ)) := by
  sorry





theorem theorem_7571_problem
  {n : ℕ}
  (A : Matrix (Fin n) (Fin n) ℝ)
  (v w : Matrix (Fin n) (Fin 1) ℝ)
  [Invertible A]
  [Invertible (A + v * w.transpose)]
  (h : 1 + (w.transpose * (⅟A) * v) 0 0 ≠ 0) :
  ⅟(A + v * w.transpose) =
    ⅟A - (1 / (1 + (w.transpose * (⅟A) * v) 0 0)) • ((⅟A) * v * w.transpose * (⅟A)) := by
  sorry





theorem theorem_5509_problem
  (x_1 y_1 x_2 y_2 x_3 y_3 x_4 y_4 x_5 y_5 : ℝ)
  (h_distinct : List.Nodup [(x_1, y_1), (x_2, y_2), (x_3, y_3), (x_4, y_4), (x_5, y_5)])
  (a b c d e f : ℝ)
  (h_nontriv : ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0))
  (h_conic_1 : a * x_1^2 + b * x_1 * y_1 + c * y_1^2 + d * x_1 + e * y_1 + f = 0)
  (h_conic_2 : a * x_2^2 + b * x_2 * y_2 + c * y_2^2 + d * x_2 + e * y_2 + f = 0)
  (h_conic_3 : a * x_3^2 + b * x_3 * y_3 + c * y_3^2 + d * x_3 + e * y_3 + f = 0)
  (h_conic_4 : a * x_4^2 + b * x_4 * y_4 + c * y_4^2 + d * x_4 + e * y_4 + f = 0)
  (h_conic_5 : a * x_5^2 + b * x_5 * y_5 + c * y_5^2 + d * x_5 + e * y_5 + f = 0)
  (x y : ℝ) :
  a * x^2 + b * x * y + c * y^2 + d * x + e * y + f = 0 ↔ 
  Matrix.det !![x^2, x * y, y^2, x, y, 1;
                x_1^2, x_1 * y_1, y_1^2, x_1, y_1, 1;
                x_2^2, x_2 * y_2, y_2^2, x_2, y_2, 1;
                x_3^2, x_3 * y_3, y_3^2, x_3, y_3, 1;
                x_4^2, x_4 * y_4, y_4^2, x_4, y_4, 1;
                x_5^2, x_5 * y_5, y_5^2, x_5, y_5, 1] = 0 := by
  sorry



theorem theorem_4182_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [Nonempty ι]
  (a : ι → E) (b : ι → ℝ)
  (f : E → ℝ)
  -- Condition: f is a piecewise linear convex function defined by coefficients a_i, b_i
  (h_f : ∀ x, f x = (Finset.univ.image (fun i => inner (a i) x + b i)).max' 
    (Finset.image_nonempty.mpr Finset.univ_nonempty)) :
  -- Conclusion: The subdifferential is the convex hull of the active gradients
  ∀ x, let I := {i | inner (a i) x + b i = f x}
       {v : E | ∀ y, f x + inner v (y - x) ≤ f y} = convexHull ℝ (a '' I) := by
  sorry

theorem theorem_7225_problem
  {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  (T : V →ₗ[K] W)
  {n : ℕ} (x : Fin n → V)
  (h : LinearIndependent K (fun i => T (x i))) :
  LinearIndependent K x := by
  sorry







theorem theorem_7674_problem (θ : ℝ)
  (R : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
  (hR : ∀ x, R x = !![Real.cos x, -Real.sin x; Real.sin x, Real.cos x]) :
  R (θ + Real.pi) = -R θ := by
  sorry





theorem theorem_7319_problem (n m : ℕ)
  (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
  sSup {r | ∃ x, x ≠ 0 ∧ r = ‖A x‖ / ‖x‖} = sSup {r | ∃ x, ‖x‖ = 1 ∧ r = ‖A x‖} := by
  sorry

theorem theorem_7850_problem (n : ℕ) (S : Set (Fin n → ℝ)) :
  Convex ℝ S ↔
  ∀ x ∈ S, ∀ y ∈ S, ∀ t : ℝ, t ∈ Set.Icc 0 1 → (1 - t) • x + t • y ∈ S := by
  sorry

theorem theorem_8413_problem
  {K : Type*} [Field K]
  {n : ℕ}
  (h_char : (2 : K) ≠ 0)
  (A B : Matrix (Fin n) (Fin n) K)
  (h : A * B = - (B * A)) :
  Matrix.trace (A * B) = 0 := by
  sorry

theorem theorem_8372_problem (n : ℕ) :
  let L : Set (Matrix (Fin n) (Fin n) ℂ) := {A | ∃ a : ℂ, A = a • (1 : Matrix (Fin n) (Fin n) ℂ)}
  ∃ S : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ), (S : Set (Matrix (Fin n) (Fin n) ℂ)) = L := by
  sorry



theorem theorem_9962_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (P : Matrix n n ℝ)
  (h_symm : P.IsSymm)
  (h_idem : P * P = P) :
  let D := Matrix.diagonal (fun i => P i i)
  let Q := P - D
  spectrum ℝ Q ⊆ Set.Icc (-1) 1 := by
  sorry



theorem theorem_9645_problem (S : Set ℝ) (h_nonempty : S.Nonempty) (h_bdd : BddAbove S) :
  sInf {x | ∃ s ∈ S, x = |sSup S - s|} = 0 := by
  sorry

theorem theorem_9531_problem {n : Type*} [Fintype n] [DecidableEq n]
  {F : Type*} [Field F] (A : Matrix n n F) :
  A = ∑ k : n, ∑ l : n, (A k l) • Matrix.stdBasisMatrix k l 1 := by
  sorry







theorem theorem_7490_problem (m : ℕ) (n : Fin m → ℝ) (k : ℝ)
  (A B : Matrix (Fin m) (Fin m) ℝ)
  (hA : A = Matrix.diagonal (fun i ↦ n i - k))
  (hB : B = fun _ _ ↦ k)
  (hn : ∀ i, n i - k > 0)
  (hk : k ≥ 0) :
  (A + B).PosDef := by
  sorry

theorem theorem_7393_problem
  {n : ℕ}
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA : Invertible A)
  (hB : Invertible B)
  (norm : Matrix (Fin n) (Fin n) ℝ → ℝ)
  (h_hom : ∀ (c : ℝ) (X : Matrix (Fin n) (Fin n) ℝ), norm (c • X) = |c| * norm X)
  (h_sub : ∀ (X Y : Matrix (Fin n) (Fin n) ℝ), norm (X * Y) ≤ norm X * norm Y) :
  norm (⅟A - ⅟B) ≤ norm (⅟A) * norm (⅟B) * norm (A - B) := by
  sorry



theorem theorem_8221_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (T : H →L[ℂ] H) (z : ℂ)
  (A : H →L[ℂ] H) (hA : A = z • (1 : H →L[ℂ] H) - T) :
  ContinuousLinearMap.adjoint A = (star z) • (1 : H →L[ℂ] H) - ContinuousLinearMap.adjoint T := by
  sorry

theorem theorem_8908_problem
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (n : ℕ) [NeZero n]
  (f : MultilinearMap ℝ (fun _ : Fin n => V) ℝ)
  (h_symm : ∀ (v : Fin n → V) (σ : Equiv.Perm (Fin n)), f (v ∘ σ) = f v)
  (x a : V) :
  HasDerivAt (fun t : ℝ => f (fun _ => x + t • a)) 
    (n * f (Function.update (fun _ => x) 0 a)) 0 := by
  sorry





theorem theorem_10315_problem (n m : ℕ)
  (A : Matrix (Fin n) (Fin m) ℝ)
  (B : Matrix (Fin m) (Fin n) ℝ) :
  Matrix.trace (A * B) = Matrix.trace (B * A) := by
  sorry











theorem theorem_9166_problem (n m : ℕ) (A : Fin n → Fin m → ℝ) (b : ℝ) :
  sInf {v | ∃ x : Fin m → ℝ, v = ∑ k, |Matrix.dotProduct (A k) x - b|} =
  sInf {w | ∃ (x : Fin m → ℝ) (y : Fin n → ℝ),
    (∀ k, y k ≥ Matrix.dotProduct (A k) x - b) ∧
    (∀ k, y k ≥ -Matrix.dotProduct (A k) x + b) ∧
    w = ∑ k, y k} := by
  sorry

theorem theorem_9328_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (f : X →ₗ[ℝ] ℝ) :
  sSup {a | ∃ x : X, ‖x‖ ≤ 1 ∧ a = |f x|} =
  sSup {b | ∃ x : X, x ≠ 0 ∧ b = |f x| / ‖x‖} := by
  sorry

theorem theorem_9921_problem
  (n : ℕ) (hn : n ≥ 2)
  (u : Fin n → ℝ) (hu : Matrix.dotProduct u u = 1)
  (R : Matrix (Fin n) (Fin n) ℝ)
  (hR : R = 1 - (2 : ℝ) • Matrix.vecMulVec u u) :
  ∀ x : Fin n → ℝ, Matrix.mulVec R x = x - (2 * Matrix.dotProduct u x) • u := by
  sorry



theorem theorem_7796_problem (z : ℂ) :
  Complex.exp (3 * z) = ∑' n : ℕ, ((3 : ℂ) ^ n / n.factorial) * Complex.exp (3 * ↑(Real.log 2)) * (z - ↑(Real.log 2)) ^ n := by
  sorry

theorem theorem_8803_problem (R : Type*) [CommRing R] (m : Ideal R) (hm : m.IsMaximal)
  (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
  (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N]
  (h_tensor : Subsingleton (TensorProduct R M N)) :
  Subsingleton M ∨ Subsingleton N := by
  sorry











theorem theorem_8021_problem
  (n : ℕ) [NeZero n]
  (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
  (h1 : f 1 = 1)
  (h2 : ∀ A B : Matrix (Fin n) (Fin n) ℝ, f (A * B) = f (B * A))
  (h3 : ∀ A : Matrix (Fin n) (Fin n) ℝ, f A.transpose = f A) :
  ∀ A : Matrix (Fin n) (Fin n) ℝ, f A = (1 / (n : ℝ)) * Matrix.trace A := by
  sorry

theorem theorem_10111_problem
  (α : Type*) [DecidableEq α]
  (n : ℕ)
  (L : Finset ℕ)
  (s : Finset α)
  (hs : s.card = n)
  (F : Finset (Finset α))
  (h_subset : ∀ A ∈ F, A ⊆ s)
  (h_inter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ∈ L) :
  F.card ≤ ∑ i in Finset.range (L.card + 1), Nat.choose n i := by
  sorry

theorem theorem_8205_problem
  (xA yA zA xB yB zB xC yC zC : ℝ)
  (rA rB rC : ℝ)
  (hrA : 0 ≤ rA) (hrB : 0 ≤ rB) (hrC : 0 ≤ rC)
  (xD yD zD : ℝ)
  (h_unique_sol : (xD - xA)^2 + (yD - yA)^2 + (zD - zA)^2 = rA^2 ∧
                  (xD - xB)^2 + (yD - yB)^2 + (zD - zB)^2 = rB^2 ∧
                  (xD - xC)^2 + (yD - yC)^2 + (zD - zC)^2 = rC^2 ∧
                  ∀ x y z,
                    ((x - xA)^2 + (y - yA)^2 + (z - zA)^2 = rA^2 ∧
                     (x - xB)^2 + (y - yB)^2 + (z - zB)^2 = rB^2 ∧
                     (x - xC)^2 + (y - yC)^2 + (z - zC)^2 = rC^2) →
                    x = xD ∧ y = yD ∧ z = zD) :
  (Real.sqrt ((xD - xA)^2 + (yD - yA)^2 + (zD - zA)^2) = rA ∧
   Real.sqrt ((xD - xB)^2 + (yD - yB)^2 + (zD - zB)^2) = rB ∧
   Real.sqrt ((xD - xC)^2 + (yD - yC)^2 + (zD - zC)^2) = rC ∧
   ∀ x y z,
     (Real.sqrt ((x - xA)^2 + (y - yA)^2 + (z - zA)^2) = rA ∧
      Real.sqrt ((x - xB)^2 + (y - yB)^2 + (z - zB)^2) = rB ∧
      Real.sqrt ((x - xC)^2 + (y - yC)^2 + (z - zC)^2) = rC) →
     x = xD ∧ y = yD ∧ z = zD) := by
  sorry





theorem theorem_8278_problem (N k : ℕ)
  (A : Matrix (Fin N) (Fin N) ℝ)
  (U V : Matrix (Fin k) (Fin N) ℝ)
  (hk : k ≤ N) :
  ∑ i : Fin N, ∑ j : Fin N, ((A - U.transpose * V) i j) ^ 2 =
  ∑ i : Fin N, ∑ j : Fin N, (A i j - ∑ l : Fin k, U l i * V l j) ^ 2 := by
  sorry



theorem theorem_10002_problem (f : ℝ → ℝ) (h : ∀ x y, f (x + y) = f x + f y) :
  ∀ (q : ℚ) (x : ℝ), f (q * x) = q * f x := by
  sorry

theorem theorem_9658_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  (A P : Matrix n n ℝ)
  (hP : P.PosDef)
  (h_lyap : (-(A.transpose * P + P * A)).PosDef) :
  ∀ (z : ℂ), (A.charpoly.map (algebraMap ℝ ℂ)).IsRoot z → z.re < 0 := by
  sorry









theorem theorem_8950_problem
  {k : Type*} [Field k]
  {V : Type*} [AddCommGroup V] [Module k V]
  {n : ℕ}
  (v : Basis (Fin n) k V)
  (α : Fin n → V →ₗ[k] k)
  (h : ∀ (i j : Fin n), α i (v j) = if i = j then 1 else 0) :
  ∃ (B : Basis (Fin n) k (V →ₗ[k] k)), ∀ i, B i = α i := by
  sorry

theorem theorem_9268_problem (N n : ℕ)
  (x : Fin N → EuclideanSpace ℝ (Fin n))
  (lam : Fin N → ℝ) :
  (∑ i : Fin N, ∑ j : Fin N, (lam i) * (lam j) * inner (x i) (x j)) =
  (∑ i : Fin N, (lam i)^2 * ‖x i‖^2) +
  2 * (∑ i : Fin N, ∑ j in Finset.filter (fun j => i < j) Finset.univ, (lam i) * (lam j) * inner (x i) (x j)) := by
  sorry

theorem theorem_10015_problem (v w : Fin 2 → ℝ) :
  let dx : (Fin 2 → ℝ) → ℝ := fun u => u 0
  let dy : (Fin 2 → ℝ) → ℝ := fun u => u 1
  let wedge_val := dx v * dy w - dx w * dy v
  let det_val := Matrix.det !![v 0, w 0; v 1, w 1]
  wedge_val = det_val := by
  sorry



theorem theorem_10178_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  {n : Type*} [Fintype n] [DecidableEq n]
  (B : Basis n F V)
  (T : V →ₗ[F] V)
  (v : V) :
  (B.repr (T v) : n → F) = Matrix.mulVec (LinearMap.toMatrix B B T) (B.repr v) := by
  sorry



theorem theorem_7575_problem (n : ℕ) (a b c d : Fin n → ℝ)
  (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
  (hc : ∀ i, 0 < c i) (hd : ∀ i, 0 < d i)
  [NeZero n] :
  ∀ x : Fin n → ℝ, (∀ i, 0 < x i) →
  ∃ i j : Fin n,
    (∑ k : Fin n, ∑ l : Fin n, a k * b l * x k * x l) /
    (∑ k : Fin n, ∑ l : Fin n, c k * d l * x k * x l) ≤
    (a i * b j) / (c i * d j) := by
  sorry

theorem theorem_10265_problem
  (G : Type*) [Group G] [Fintype G]
  (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (N : ℕ) (hN : FiniteDimensional.finrank ℂ V = N)
  (ρ : G →* (V ≃ₗ[ℂ] V))
  (g : G)
  (b₁ b₂ : Basis (Fin N) ℂ V) :
  Matrix.trace (LinearMap.toMatrix b₁ b₁ (ρ g)) = Matrix.trace (LinearMap.toMatrix b₂ b₂ (ρ g)) := by
  sorry





theorem theorem_9339_problem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [DecidableEq K]
  (T : V →ₗ[K] V) (μ : K) (hμ : Module.End.HasEigenvalue T μ) :
  FiniteDimensional.finrank K (Module.End.eigenspace T μ) ≤ (LinearMap.charpoly T).rootMultiplicity μ := by
  sorry







theorem theorem_9489_problem (f : ℂ → ℂ) (M : ℝ) (n : ℕ)
  (h_entire : Differentiable ℂ f)
  (hM : M > 0)
  (h_bound : ∀ z : ℂ, Complex.abs (f z) ≤ M * (1 + (Complex.abs z) ^ n)) :
  ∃ P : Polynomial ℂ, P.degree ≤ n ∧ ∀ z, f z = P.eval z := by
  sorry

theorem theorem_9865_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [Field K]
  (M M1 : Matrix n n K)
  (hM : M.det = 0)
  (hM1 : M1.det ≠ 0) :
  ¬ ∃ (P Q : Matrix n n K), IsUnit P ∧ IsUnit Q ∧ P * M * Q = M1 := by
  sorry





theorem theorem_9796_problem
  (n k d : ℕ)
  (x : Fin n → EuclideanSpace ℝ (Fin d)) :
  let μ : (Fin k → Fin n → ℝ) → Fin k → EuclideanSpace ℝ (Fin d) :=
    fun π i ↦ (∑ j, π i j)⁻¹ • (∑ j, π i j • x j)
  let J : (Fin k → Fin n → ℝ) → ℝ :=
    fun π ↦ ∑ j, ∑ i, (π i j) * ‖x j - μ π i‖^2
  let S : Set (Fin k → Fin n → ℝ) :=
    {π | ∀ i, ∑ j, π i j ≠ 0}
  ContDiffOn ℝ ⊤ J S := by
  sorry





theorem theorem_10892_problem (n : ℕ) (R : Type*) [CommRing R]
  (A B C D : Matrix (Fin n) (Fin n) R) :
  Matrix.det (Matrix.fromBlocks A B C D) = Matrix.det (Matrix.fromBlocks D C B A) := by
  sorry





theorem theorem_10920_problem (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
  (h_symm : M.IsSymm) (h_idem : M ^ 2 = M) :
  ∀ i : Fin n, ∑ j : Fin n, (M i j) ^ 2 = M i i := by
  sorry

