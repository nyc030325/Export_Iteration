import Mathlib
import Mathlib.Tactic









theorem theorem_489424_problem (z : ℂ) :
  ¬ (Complex.abs (z - 5) + Complex.abs (z + 1) ≤ Complex.abs (z - 2)) := by
  sorry





theorem theorem_489239_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
  (h : star A * A = A * star A) :
  Matrix.IsHermitian A ↔ A = star A := by
  sorry

theorem theorem_489582_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (v : ℝ → E) (t : ℝ)
  (h : DifferentiableAt ℝ v t) :
  inner (v t) (deriv v t) = (1 / 2 : ℝ) * deriv (fun x => ‖v x‖ ^ 2) t := by
  sorry



theorem theorem_489753_problem {α : Type*} (n : ℕ) (A : ℕ → Set α) (hn : n > 0) :
  (⋃ i ∈ Finset.range n, A (i + 1)) = Nat.rec ∅ (fun k acc => acc ∪ A (k + 1)) n := by
  sorry

theorem theorem_489872_problem
  {K V W : Type*}
  [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  (T : V →ₗ[K] W) :
  Nonempty ((V ⧸ LinearMap.ker T) ≃ₗ[K] LinearMap.range T) := by
  sorry









theorem theorem_489883_problem (x y : ℝ)
  (hx : x * (-1 + y) = 0)
  (hy : y * (1 + y^2) = 0) :
  x = 0 ∧ y = 0 := by
  sorry





theorem theorem_489740_problem
  (n : ℕ)
  (P : ℝ → ℝ × ℝ)
  (A B : ℝ × ℝ)
  (L : ℝ → ℝ × ℝ)
  (hL : ∀ s, L s = (1 - s) • A + s • B)
  (h_exist : ∃ t s : ℝ, 0 < t ∧ t < 1 ∧ 0 < s ∧ s < 1 ∧ P t = L s) :
  ∃ p : ℝ × ℝ, (∃ t : ℝ, 0 < t ∧ t < 1 ∧ P t = p) ∧
               (∃ s : ℝ, 0 < s ∧ s < 1 ∧ L s = p) := by
  sorry





theorem theorem_489745_problem
  (a : ℝ)
  (f g : ℝ → ℝ)
  (hg_dom : ∀ x ∈ Set.Ico 0 1, a ≤ g x)
  (hg_inc : StrictMonoOn g (Set.Ico 0 1))
  (hg_diff : DifferentiableOn ℝ g (Set.Ico 0 1))
  (hg_lim : Filter.Tendsto g (nhdsWithin 1 (Set.Iio 1)) Filter.atTop)
  (hf_diff : DifferentiableOn ℝ f (Set.Ici a))
  (L : ℝ)
  (h_cont : ContinuousOn (fun x ↦ if x = 1 then L else f (g x)) (Set.Icc 0 1))
  (h_eq : f (g 0) = L) :
  ∃ c ∈ Set.Ioo 0 1, deriv f (g c) = 0 := by
  sorry











theorem theorem_490634_problem (n : ℕ)
  (h_even : Even n)
  (h_gt_2 : n > 2)
  (h_goldbach : ∀ k : ℕ, Even k → k > 2 → ∃ p1 p2 : ℕ, Nat.Prime p1 ∧ Nat.Prime p2 ∧ k = p1 + p2) :
  ∃ p1 p2 : ℕ, Nat.Prime p1 ∧ Nat.Prime p2 ∧ n = p1 + p2 := by
  sorry







theorem theorem_491181_problem (b_seq : ℕ → ℝ) (b : ℝ)
  (h1 : Filter.Tendsto b_seq Filter.atTop (nhds b))
  (h2 : b ≠ 0) :
  ∃ m : ℕ, ∀ n ≥ m, |b_seq n| > |b| / 2 := by
  sorry





theorem theorem_491796_problem {X : Type*} (f : ℕ → X) (hf : Function.Injective f) :
  Set.Countable (Set.range f) := by
  sorry

theorem theorem_490350_problem (u : ℝ → ℝ → ℝ)
  (h_diff : ContDiff ℝ 2 (Function.uncurry u))
  (h_eq : ∀ t x : ℝ,
    let v := fun (t' x' : ℝ) ↦ deriv (fun τ ↦ u τ x') t' - 4 * deriv (fun χ ↦ u t' χ) x'
    deriv (fun τ ↦ v τ x) t + 9 * deriv (fun χ ↦ v t χ) x = 0) :
  ∃ f g : ℝ → ℝ, ∀ t x, u t x = f (x - 9 * t) + g (x + 4 * t) := by
  sorry





















theorem theorem_492157_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- Manifold B setup
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H B] [SmoothManifoldWithCorners I B]
  -- Manifold C setup
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {C : Type*} [TopologicalSpace C] [ChartedSpace G C] [SmoothManifoldWithCorners J C]
  -- Manifold D setup
  {K : Type*} [NormedAddCommGroup K] [NormedSpace 𝕜 K]
  {L : Type*} [TopologicalSpace L] {M : ModelWithCorners 𝕜 K L}
  {D : Type*} [TopologicalSpace D] [ChartedSpace L D] [SmoothManifoldWithCorners M D]
  -- Problem statement variables
  (h : B × C → D) (b : B) (c : C)
  (X : TangentSpace I b) (Y : TangentSpace J c)
  (h_smooth : Smooth (I.prod J) M h) :
  -- The equality
  mfderiv (I.prod J) M h (b, c) (X, Y) =
  mfderiv I M (fun x => h (x, c)) b X + mfderiv J M (fun y => h (b, y)) c Y := by
  sorry













theorem theorem_490471_problem (X : Type*) (t1 t2 : TopologicalSpace X)
  (h1 : @T2Space X t1)
  (h2 : @T2Space X t2)
  (h3 : ∀ (s : Set X), @IsCompact X t1 s ↔ @IsCompact X t2 s) :
  t1 = t2 := by
  sorry





theorem theorem_492663_problem 
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (C M : V → ℝ) 
  (D : ℝ) 
  (hD : D > 0)
  (grad : (V → ℝ) → (V → V)) 
  (div : (V → V) → (V → ℝ))
  -- Condition: Oxygen dynamics are governed by diffusion and consumption.
  -- This implies the existence of a flux J satisfying Fick's law and mass conservation.
  (h_dynamics : ∃ J : V → V, (∀ x, J x = -D • grad C x) ∧ (∀ x, div J x + M x = 0)) :
  ∀ x, div (fun y ↦ -D • grad C y) x = -M x := by
  sorry



theorem theorem_492406_problem (m : ℕ) (hm : m ≥ 1)
  (φ : ℝ → ℝ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_compact : HasCompactSupport φ)
  (hφ_zeros : ∀ k < m, iteratedDeriv k φ 0 = 0) :
  ∃ ψ : ℝ → ℝ, ContDiff ℝ ⊤ ψ ∧ HasCompactSupport ψ ∧ ∀ x, φ x = x ^ m * ψ x := by
  sorry

theorem theorem_492590_problem (p q : ℕ → ℤ)
  (h1 : p 0 = 1)
  (h2 : q 0 = 1)
  (h3 : ∀ n, p (n + 1) = 3 * p n + 4 * q n)
  (h4 : ∀ n, q (n + 1) = 2 * p n + 3 * q n) :
  ∀ n, (p n)^2 = 2 * (q n)^2 - 1 := by
  sorry









theorem theorem_492756_problem
  (f : Polynomial ℤ)
  (m : ℕ)
  (hm : m = f.natDegree)
  (h_lead : f.coeff m ≠ 0)
  (H : ℝ)
  (hH_bound : ∀ i < m, |(f.coeff i : ℝ) / (f.coeff m : ℝ)| ≤ H)
  (hH_max : ∃ i < m, |(f.coeff i : ℝ) / (f.coeff m : ℝ)| = H)
  (n : ℤ)
  (hn_ge : (n : ℝ) ≥ H + 2)
  (hn_prime : Prime (f.eval n)) :
  Irreducible f := by
  sorry

theorem theorem_492865_problem
  (F : Type*) [Field F]
  (m n : ℕ)
  (A : Matrix (Fin m) (Fin n) F) :
  A.rank = A.transpose.rank := by
  sorry



theorem theorem_490525_problem
  (n : ℕ)
  (hn : 0 < n)
  (g : ℝ → ℝ)
  (hg : ContinuousOn g (Set.Ici 0))
  (f : ℝ → ℝ)
  (hf : ∀ θ, 0 < θ → f θ = ∫ y in (0)..θ, g y * ((2 * n : ℝ) / θ ^ (2 * n)) * y ^ (2 * n - 1))
  (h_diff : DifferentiableOn ℝ f (Set.Ioi 0))
  (h_deriv : ∀ θ, 0 < θ → deriv f θ = 0) :
  ∀ θ, 0 < θ → g θ = 0 := by
  sorry



theorem theorem_492979_problem :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  ∀ k : ℕ, (k : ℝ) ≥ (Real.exp 1 * Real.log n) / Real.log (Real.log n) →
  ((Real.exp 1 / (k : ℝ)) ^ k) / (1 - Real.exp 1 / (k : ℝ)) ≤ (n : ℝ) ^ (-2 : ℝ) := by
  sorry

theorem theorem_492921_problem (u : ℝ → ℝ → ℝ)
  (h_diff : DifferentiableOn ℝ (fun p : ℝ × ℝ ↦ u p.1 p.2) {p | p ≠ 0})
  (h_pde : ∀ x y : ℝ, (x, y) ≠ 0 → 
    fderiv ℝ (fun p : ℝ × ℝ ↦ u p.1 p.2) (x, y) (x, y) = 0)
  (h_init : ∀ x y : ℝ, x^2 + y^2 = 1 → u x y = x) :
  ∀ x y : ℝ, (x, y) ≠ 0 → u x y = x / Real.sqrt (x^2 + y^2) := by
  sorry















theorem theorem_493600_problem (c lam n0 : ℝ) (hc : 0 < c) (hlam : 0 < lam) (hn0 : 0 < n0) :
  ∫ x in Set.Ioi n0, Real.exp (-c * x ^ lam) =
  (∫ t in Set.Ioi (c * n0 ^ lam), t ^ (1 / lam - 1) * Real.exp (-t)) / (lam * c ^ (1 / lam)) := by
  sorry





theorem theorem_493581_problem (n : ℕ) (hn : n > 0) :
  ∃ C : ℕ, ∀ m : ℕ, m.Prime → m > C →
  ∃ X Y Z : ℤ,
    ¬((m : ℤ) ∣ X) ∧ ¬((m : ℤ) ∣ Y) ∧ ¬((m : ℤ) ∣ Z) ∧
    X^n + Y^n ≡ Z^n [ZMOD m] := by
  sorry



theorem theorem_493119_problem (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) :
  Filter.Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..1, (↑n * f x) / (1 + (↑n) ^ 2 * x ^ 2)) Filter.atTop (nhds (Real.pi / 2 * f 0)) := by
  sorry

theorem theorem_494056_problem
  (D : Type*)
  (hD : Nonempty D)
  (phi : D → Prop)
  (h : ∀ y : D, phi y) :
  ∀ x : D, phi x := by
  sorry



theorem theorem_493961_problem 
  -- P m w k returns true if Turing Machine m halts on w within k steps
  (P : ℕ → List Bool → ℕ → Bool)
  -- The step-checking function is computable (simulation is effective)
  (hP : Computable (fun (x : ℕ × List Bool × ℕ) => P x.1 x.2.1 x.2.2))
  (L : Set (List Bool))
  -- L is the set of strings where there exists a machine that halts within the fixed bound
  (hL : L = {w | ∃ m, P m w (512^512) = true}) :
  -- L is recursively enumerable (domain of a partial computable function)
  ∃ f : List Bool →. Unit, Partrec f ∧ L = {w | (f w).Dom} := by
  sorry























theorem theorem_494659_problem (an bn zn : ℕ → ℝ) (a b : ℝ)
  (h1 : ∀ n, an n ≤ bn n)
  (h2 : ∀ n, zn n = bn n - an n)
  (h3 : Filter.Tendsto an Filter.atTop (nhds a))
  (h4 : Filter.Tendsto bn Filter.atTop (nhds b)) :
  a ≤ b := by
  sorry

