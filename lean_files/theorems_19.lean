import Mathlib
import Mathlib.Tactic



theorem theorem_96738_problem :
  ∃ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (p : ℝ),
    ((1 : Matrix (Fin n) (Fin n) ℝ) + p • B) * ((1 : Matrix (Fin n) (Fin n) ℝ) + p • B).transpose = 1 ∧
    B.transpose ≠ -B := by
  sorry

theorem theorem_96766_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (A B C : Set V)
  (hA_fin : A.Finite)
  (hB_fin : B.Finite)
  (hA_indep : LinearIndependent K ((↑) : A → V))
  (hB_span : Submodule.span K B = ⊤)
  (hC_sub_A : A ⊆ C)
  (hC_sub_AB : C ⊆ A ∪ B)
  (hC_span : Submodule.span K C = ⊤)
  (hC_min : ∀ (S : Set V), A ⊆ S → S ⊆ A ∪ B → Submodule.span K S = ⊤ → S ⊆ C → S = C) :
  Nonempty (Basis (↥C) K V) := by
  sorry







theorem theorem_96899_problem
  (a11 a12 a21 a22 w11 w12 w23 w24 : ℝ)
  (h1 : a11 * w11 = 1)
  (h2 : a11 * w12 = 1)
  (h3 : a12 * w23 = 0)
  (h4 : a12 * w24 = 1)
  (h5 : a21 * w11 = 0)
  (h6 : a21 * w12 = -1)
  (h7 : a22 * w23 = -1)
  (h8 : a22 * w24 = 1)
  (h9 : w23 ≠ 0)
  (h10 : a12 ≠ 0) :
  False := by
  sorry

theorem theorem_97291_problem
  (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (hf : ContDiff ℝ 2 f)
  (x p : EuclideanSpace ℝ (Fin n)) :
  gradient f (x + p) - gradient f x = ∫ t in (0 : ℝ)..1, (fderiv ℝ (gradient f) (x + t • p)) p := by
  sorry

theorem theorem_97106_problem
  (n : ℕ)
  (B : Matrix (Fin n) (Fin n) ℝ)
  (S : Set (Fin n))
  (Q : Matrix S (Fin n) ℝ)
  (R : Matrix (Fin n) S ℝ)
  (hQ : ∀ (i : S) (j : Fin n), Q i j = if (i : Fin n) = j then 1 else 0)
  (hR : ∀ (i : Fin n) (j : S), R i j = if i = (j : Fin n) then 1 else 0) :
  ∀ (u v : S), (Q * B * R) u v = B u v := by
  sorry













theorem theorem_97175_problem
  (fn : ℕ → ℝ → ℝ)
  (f : ℝ → ℝ)
  (hfn : ∀ (n : ℕ) (x : ℝ), fn n x = (x - 1 / (n : ℝ))^2)
  (hf : ∀ x : ℝ, f x = x^2) :
  TendstoUniformlyOn fn f Filter.atTop (Set.Icc 0 1) := by
  sorry

















theorem theorem_97903_problem (a : ℕ → ℂ) (f : ℂ → ℂ)
  (h_f : ∀ z : ℂ, HasSum (fun n => a n * z ^ n) (f z)) :
  ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z : ℂ, z ≠ 0 → g z = (f z - f 0) / z := by
  sorry







theorem theorem_97600_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
  (hA : IsUnit A) (hAB : IsUnit (A + B)) :
  (A + B)⁻¹ = A⁻¹ - A⁻¹ * B * (A + B)⁻¹ := by
  sorry

theorem theorem_98260_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (S T : V →ₗ[ℂ] V)
  (W : V →ₗ[ℂ] V)
  (hW : W = S - T)
  (h : ∀ x y : V, inner (W x) y = (0 : ℂ)) :
  W = 0 := by
  sorry

theorem theorem_97822_problem
  (n : ℕ)
  (D : Set (Fin n → ℝ))
  (f : (Fin n → ℝ) → (Fin n → ℝ))
  (f_component : Fin n → (Fin n → ℝ) → ℝ)
  (partial_op : Fin n → (Fin n → ℝ))
  (h_components : ∀ z ∈ D, ∀ j, f_component j z = f z j)
  (h_partial : ∀ j, partial_op j = Pi.single j 1) :
  ∀ z ∈ D, f z = ∑ j : Fin n, (f_component j z) • (partial_op j) := by
  sorry

theorem theorem_98221_problem
  (k : ℕ)
  (V : Type*) [AddCommGroup V] [Module ℝ V]
  (f : (Fin k → V) → ℝ)
  (σ τ : Equiv.Perm (Fin k)) :
  let action := fun (π : Equiv.Perm (Fin k)) (g : (Fin k → V) → ℝ) => (fun v => g (v ∘ π))
  ∀ v : Fin k → V, action (σ * τ) f v = action σ (action τ f) v := by
  sorry











theorem theorem_98407_problem
  (n m : ℕ)
  (f : (Fin n → ℝ) × (Fin m → ℝ) → ℝ)
  (hf : ContDiff ℝ ⊤ f)
  (x : Fin n → ℝ)
  (μ : Fin m → ℝ)
  (v : Fin n → ℝ) :
  iteratedFDeriv ℝ n (fun y ↦ f (y, μ)) x (fun _ ↦ v) =
  ∑ I : Fin n → Fin n,
    (iteratedFDeriv ℝ n (fun y ↦ f (y, μ)) x (fun k ↦ Pi.single (I k) 1)) *
    (∏ k : Fin n, v (I k)) := by
  sorry

theorem theorem_98590_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {n : ℕ} (f : Fin n → V →ₗ[F] F) (g : V →ₗ[F] F)
  (h : (⨅ i, LinearMap.ker (f i)) ≤ LinearMap.ker g) :
  ∃ c : Fin n → F, g = ∑ i, c i • f i := by
  sorry

theorem theorem_98389_problem
  (n : ℕ) (k : ℝ)
  (S D : Type*)
  (pair : D → S → ℝ)
  (lap_S : S → S)
  (lap_D : D → D)
  (u : ℝ → D)
  (h_dist_lap : ∀ (d : D) (ϕ : S), pair (lap_D d) ϕ = pair d (lap_S ϕ))
  (h_eqn : ∀ (t : ℝ) (ϕ : S), deriv (fun τ => pair (u τ) ϕ) t - k^2 * pair (lap_D (u t)) ϕ = 0) :
  ∀ (t : ℝ) (ϕ : S), deriv (fun τ => pair (u τ) ϕ) t = k^2 * pair (u t) (lap_S ϕ) := by
  sorry



theorem theorem_98426_problem (n : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
  (h_cont : Continuous f)
  (h_sim : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P.det → f (P * A * P⁻¹) = f A) :
  ∀ (A B : Matrix (Fin n) (Fin n) ℂ), A.charpoly = B.charpoly → f A = f B := by
  sorry





theorem theorem_99507_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (f : ℕ → H) (a : ℕ → ℂ) (x : H)
  (h_ortho : Orthonormal ℂ f)
  (h_sum : HasSum (fun n => a n • f n) x) :
  ‖x‖ ^ 2 = ∑' n, ‖a n‖ ^ 2 := by
  sorry











theorem theorem_99562_problem (M Y p h_U : ℝ)
  (hM : M > 0)
  (hp : 0 < p ∧ p < 1)
  (r h : ℝ)
  (h_def : h = M * p * (1 - p) * h_U)
  (h_bound : 1 - h > 0)
  (r_def : r = (Y - M * p) / Real.sqrt (M * p * (1 - p))) :
  r / Real.sqrt (1 - h) = (Y - M * p) / Real.sqrt (M * p * (1 - p) * (1 - h)) := by
  sorry











theorem theorem_99920_problem
  {J K : Type*} [Fintype K]
  (P : J → K → ℝ → ℝ)
  (t : ℝ)
  (h_diff : ∀ j k, DifferentiableAt ℝ (P j k) t)
  (h_sum : ∀ j u, ∑ k, P j k u = 1) :
  ∀ j, ∑ k, deriv (P j k) t = 0 := by
  sorry

theorem theorem_99949_problem (a b : ℝ) (f : ℝ → ℝ)
  (h : MonotoneOn f (Set.Icc a b)) :
  Set.Countable {x ∈ Set.Icc a b | ¬ ContinuousWithinAt f (Set.Icc a b) x} := by
  sorry

theorem theorem_99839_problem
  (a b c : ℝ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (x₁ x₂ x₃ y₁ y₂ y₃ : ℝ)
  (hx₁ : x₁ = (a / Real.sqrt (a^2 + 8 * b * c)) ^ ((2 : ℝ) / 3))
  (hx₂ : x₂ = (b / Real.sqrt (b^2 + 8 * c * a)) ^ ((2 : ℝ) / 3))
  (hx₃ : x₃ = (c / Real.sqrt (c^2 + 8 * a * b)) ^ ((2 : ℝ) / 3))
  (hy₁ : y₁ = (a * (a^2 + 8 * b * c)) ^ ((1 : ℝ) / 3))
  (hy₂ : y₂ = (b * (b^2 + 8 * c * a)) ^ ((1 : ℝ) / 3))
  (hy₃ : y₃ = (c * (c^2 + 8 * a * b)) ^ ((1 : ℝ) / 3))
  (p q : ℝ)
  (hp : p = 3 / 2)
  (hq : q = 3) :
  |x₁ * y₁ + x₂ * y₂ + x₃ * y₃| ^ 3 ≤ (x₁ ^ p + x₂ ^ p + x₃ ^ p) ^ 2 * (y₁ ^ q + y₂ ^ q + y₃ ^ q) := by
  sorry





theorem theorem_99530_problem :
  ∫ x in Set.Ioi (0 : ℝ), Real.log (|x|) / (1 + x ^ 2) ^ 4 = -23 * Real.pi / 96 := by
  sorry





theorem theorem_100680_problem (n m : ℕ) (hn : n ≠ 0) (X : Matrix (Fin n) (Fin m) ℝ) :
  let ones : Fin n → ℝ := fun _ ↦ 1
  let M : Matrix (Fin m) (Fin m) ℝ := X.transpose * X - (n : ℝ)⁻¹ • (X.transpose * Matrix.vecMulVec ones ones * X)
  IsUnit M.det ↔ LinearIndependent ℝ (Sum.elim X.transpose (fun _ : Unit ↦ ones)) := by
  sorry

theorem theorem_100525_problem (n m : ℕ) (B : Matrix (Fin n) (Fin m) ℝ)
  (L : Matrix (Fin n) (Fin n) ℝ) (h : L = B * B.transpose) :
  Matrix.PosSemidef L := by
  sorry

theorem theorem_100541_problem (n : ℕ) (hn : 1 ≤ n) :
  ConnectedSpace (Matrix.GeneralLinearGroup (Fin n) ℂ) := by
  sorry











theorem theorem_100942_problem
  (n : ℕ)
  (Sigma tau Omega : Matrix (Fin n) (Fin n) ℝ)
  (lam : ℝ)
  (h_tau_diag : tau.IsDiag)
  (h_tau_pos : ∀ i, 0 < tau i i)
  (h_Omega_symm : Omega.IsSymm)
  (h_Omega_psd : Omega.PosSemidef)
  (h_Sigma_eq : Sigma = tau * Omega * tau)
  (h_lam_pos : 0 < lam) :
  (lam • Sigma).IsSymm ∧ (lam • Sigma).PosSemidef := by
  sorry

theorem theorem_100784_problem (x₁ y₁ x₂ y₂ x₃ y₃ : ℝ) :
  let P₁ : ℝ × ℝ := (x₁, y₁)
  let P₂ : ℝ × ℝ := (x₂, y₂)
  let P₃ : ℝ × ℝ := (x₃, y₃)
  let M : Matrix (Fin 3) (Fin 3) ℝ := !![x₁, y₁, 1; x₂, y₂, 1; x₃, y₃, 1]
  Matrix.det M ≠ 0 ↔ ¬ Collinear ℝ ({P₁, P₂, P₃} : Set (ℝ × ℝ)) := by
  sorry

theorem theorem_101044_problem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (C : Set E)
  (hC_convex : Convex ℝ C)
  (hC_cone : ∀ (x : E) (c : ℝ), x ∈ C → 0 ≤ c → c • x ∈ C)
  (phi : E →ₗ[ℝ] ℝ)
  (H : Set E)
  (hH : H = {x | phi x = 1})
  (u : E)
  (hu_boundary : u ∈ frontier C)
  (hu_phi : 0 < phi u)
  (x' : E)
  (hx'_H : x' ∈ H)
  (hx'_ray : ∃ k : ℝ, 0 < k ∧ x' = k • u) :
  x' = (phi u)⁻¹ • u := by
  sorry

theorem theorem_100967_problem (θ u v x y z : ℝ)
  (e_u e_v : ℝ × ℝ × ℝ)
  -- The v-axis coincides with the z-axis
  (h_ev : e_v = (0, 0, 1))
  -- The plane is rotated around the z-axis by θ, and the u-axis is orthogonal to the z-axis.
  -- This corresponds to the direction vector (cos θ, sin θ, 0).
  (h_eu : e_u = (Real.cos θ, Real.sin θ, 0))
  -- The relationship between the 2D coordinates (u,v) and 3D coordinates (x,y,z)
  -- is defined by the vector composition in the plane.
  (h_pos : (x, y, z) = u • e_u + v • e_v) :
  x = u * Real.cos θ ∧ y = u * Real.sin θ ∧ z = v := by
  sorry

theorem theorem_100843_problem :
  ∃ (n : ℕ) (A₁ A₂ : Matrix (Fin n) (Fin n) ℝ),
    (A₁.transpose * A₁).charpoly = (A₂.transpose * A₂).charpoly ∧
    ((A₁ + 1).transpose * (A₁ + 1)).charpoly ≠ ((A₂ + 1).transpose * (A₂ + 1)).charpoly := by
  sorry









theorem theorem_100782_problem
  {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  (T : V →ₗ[K] V)
  (f : Polynomial K) :
  ∀ v : V, v ∈ LinearMap.ker (Polynomial.aeval T f) → T v ∈ LinearMap.ker (Polynomial.aeval T f) := by
  sorry





theorem theorem_100995_problem (n : ℕ) (hn : 0 < n) :
  ∃ E : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ),
    (∀ x ∈ E, x.IsSymm) ∧
    (∀ x ∈ E, Matrix.rank x ≤ 1 → x = 0) ∧
    FiniteDimensional.finrank ℝ E = n * (n + 1) / 2 - 1 ∧
    ∀ E' : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ),
      (∀ x ∈ E', x.IsSymm) →
      (∀ x ∈ E', Matrix.rank x ≤ 1 → x = 0) →
      FiniteDimensional.finrank ℝ E' ≤ n * (n + 1) / 2 - 1 := by
  sorry



theorem theorem_101397_problem
  (K : Type*) [Field K]
  (V : Type*) [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  (T : V →ₗ[K] V)
  (h_nilp : IsNilpotent T)
  (h_ker_eq_im : LinearMap.ker T = LinearMap.range T) :
  T ^ 2 = 0 := by
  sorry

theorem theorem_101755_problem (n : ℕ) :
  let A : Set (Matrix.GeneralLinearGroup (Fin n) ℝ) :=
    {B | ∀ i j : Fin n, i ≠ j → (B : Matrix (Fin n) (Fin n) ℝ) i j = 0}
  IsClosed A := by
  sorry



theorem theorem_101899_problem
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (T : X →L[𝕜] X)
  (h : ∃ e₁ : X, ‖e₁‖ = 1 ∧ T e₁ = e₁) :
  ‖T‖ = 1 := by
  sorry



theorem theorem_101537_problem
  (n : ℕ)
  (a b : Fin n → ℝ)
  (h_neq : a ≠ b)
  (f : (Fin n → ℝ) → ℝ)
  (h : AffineMap ℝ (Fin n → ℝ) ℝ)
  (ha : h a = f a)
  (hb : h b = f b) :
  ∀ t : ℝ, t ∈ Set.Icc 0 1 → h (t • a + (1 - t) • b) = t * f a + (1 - t) * f b := by
  sorry





theorem theorem_102156_problem
  (k : ℕ)
  (A : Matrix (Fin k) (Fin k) ℝ)
  (ρ : ℝ)
  (u v : Fin k → ℝ)
  (h_k : k > 0)
  (h_A_01 : ∀ i j, A i j = 0 ∨ A i j = 1)
  (h_rho_pos : 0 < ρ)
  (h_u_eig : Matrix.vecMul u A = ρ • u)
  (h_v_eig : Matrix.mulVec A v = ρ • v)
  (h_u_pos : ∀ i, 0 < u i)
  (h_v_pos : ∀ i, 0 < v i)
  (p : Fin k → ℝ)
  (h_p_def : ∀ i, p i = (u i * v i) / (∑ j, u j * v j)) :
  ∃ (c : ℝ) (n : Fin k → ℤ), ∀ i, p i = c * ρ ^ (n i) := by
  sorry

theorem theorem_102493_problem
  (F V : Type*)
  [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V] :
  ∃ Φ : (V →ₗ[F] V) ≃ₗ[F] Module.Dual F (V →ₗ[F] V),
    ∀ (S T : V →ₗ[F] V), Φ S T = LinearMap.trace F V (S * T) := by
  sorry





theorem theorem_102399_problem
  (K R : Type*)
  [Field K] [Ring R] [Algebra K R]
  [Module.Finite K R]
  [Module R (R →ₗ[K] K)]
  [IsScalarTower K R (R →ₗ[K] K)]
  (f : R →ₗ[R] (R →ₗ[K] K))
  (h_mono : Function.Injective f) :
  Function.Bijective f := by
  sorry



