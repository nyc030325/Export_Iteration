import Mathlib
import Mathlib.Tactic











theorem theorem_436784_problem (a b c d : ℝ)
  (P Q : Matrix (Fin 3) (Fin 3) ℝ)
  (hP : P = !![1, a, b; 0, 0, 0; 0, 0, 0])
  (hQ : Q = !![0, 0, 0; c, 1, d; 0, 0, 0]) :
  Matrix.det ((1 : Matrix (Fin 3) (Fin 3) ℝ) - (P + Q)) = -a * c := by
  sorry

theorem theorem_437253_problem 
  (n k : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (P : Matrix (Fin n) (Fin k) ℝ)
  (D : Matrix (Fin k) (Fin k) ℝ)
  (hD_def : D = P.transpose * P)
  (hD_diag : D.IsDiag)
  (hD_inv : D * D⁻¹ = 1) -- Assume D is invertible
  (D_inv_sqrt : Matrix (Fin k) (Fin k) ℝ)
  (D_sqrt : Matrix (Fin k) (Fin k) ℝ)
  (h_inv_sqrt_sq : D_inv_sqrt * D_inv_sqrt = D⁻¹) -- Definition of inverse square root
  (h_sqrt_inv : D_sqrt * D_inv_sqrt = 1) -- Definition of D^{1/2} as inverse of D^{-1/2}
  (h_inv_sqrt_symm : D_inv_sqrt.IsSymm) -- Implied by D being diagonal
  (Q : Matrix (Fin n) (Fin k) ℝ)
  (hQ_def : Q = P * D_inv_sqrt)
  (B : Matrix (Fin k) (Fin k) ℝ)
  (hB_def : B = D⁻¹ * P.transpose * A * P) :
  D_sqrt * B * D_inv_sqrt = Q.transpose * A * Q := by
  sorry



theorem theorem_437004_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (n : ℕ)
  (h_char : CharP F 2)
  (h_dim : FiniteDimensional.finrank F V = n)
  (φ : MultilinearMap F (fun _ : Fin n => V) F)
  (h_alt : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V),
    φ (v ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : F) * φ v) :
  ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), φ (v ∘ σ) = φ v := by
  sorry

theorem theorem_436905_problem
  {F : Type*} [Field F] [Fintype F]
  {m : ℕ}
  (Δ : Set (Fin m → F))
  (hΔ : ∀ (L : Submodule F (Fin m → F)), FiniteDimensional.finrank F L = 1 →
    ∃! v, v ∈ Δ ∧ L = Submodule.span F {v})
  (u : Fin m → F) (hu : u ≠ 0) :
  ∃! p : (Fin m → F) × F, p.1 ∈ Δ ∧ p.2 ≠ 0 ∧ u = p.2 • p.1 := by
  sorry









theorem theorem_437365_problem {n : ℕ} {F : Type*} [Field F]
  (A B C D : Matrix (Fin n) (Fin n) F) :
  let L : Matrix (Fin n) (Fin n) F → Matrix (Fin n) (Fin n) F := fun X ↦ A * X * B + C * X * D
  let M : Matrix (Fin n × Fin n) (Fin n × Fin n) F := (B.transpose).kronecker A + (D.transpose).kronecker C
  ∃ (v : Matrix (Fin n) (Fin n) F ≃ (Fin n × Fin n → F)),
    ∀ (X : Matrix (Fin n) (Fin n) F),
      L X = 0 ↔ M.mulVec (v X) = 0 := by
  sorry







theorem theorem_436540_problem (n : ℕ) (x : Fin n → Fin n → ℝ)
  (h_ortho : ∀ i j, Matrix.dotProduct (x i) (x j) = if i = j then 1 else 0) :
  (-1 : ℝ)^(n - 1) * ∑ σ : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign σ : ℝ) * ∏ i, x i (σ i)) = 1 := by
  sorry











theorem theorem_437038_problem (a : ℝ) (ha : 0 < a) :
  circleIntegral (fun z ↦ 1 / z ^ 2) 0 a = 0 := by
  sorry



theorem theorem_437577_problem (X Y : Type*)
  [Denumerable X] [Denumerable Y] :
  Nonempty (lp (fun _ : X ↦ ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : Y ↦ ℂ) 2) := by
  sorry







theorem theorem_437943_problem
  (n m : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (C : Matrix (Fin m) (Fin m) ℝ)
  (U : Matrix (Fin n) (Fin m) ℝ)
  (V : Matrix (Fin m) (Fin n) ℝ)
  (hA : Invertible A)
  (hC : Invertible C)
  (hAux : Invertible (C⁻¹ + V * A⁻¹ * U)) :
  (A + U * C * V)⁻¹ = A⁻¹ - A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ := by
  sorry





theorem theorem_438563_problem (a b c : ℝ)
  (A : Matrix (Fin 3) (Fin 3) ℝ)
  (hA : A = !![1, 1, 1; a, b, c; a^2, b^2, c^2]) :
  A.det = (b - a) * (c - a) * (c - b) := by
  sorry









theorem theorem_438899_problem
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  (Q : LinearMap.BilinForm ℝ V)
  (h_symm : Q.IsSymm)
  (h_cs : ∀ u v : V, |Q u v| ^ 2 ≤ Q u u * Q v v)
  (e : V)
  (he : Q e e = 0) :
  ∀ ϕ : V, Q e ϕ = 0 := by
  sorry

theorem theorem_438515_problem
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (A B C D : V →ₗ[F] V) (k : F) :
  (k • A + B) ⊗ₜ[F] (C + D) =
  k • (A ⊗ₜ[F] C) + k • (A ⊗ₜ[F] D) + (B ⊗ₜ[F] C) + (B ⊗ₜ[F] D) := by
  sorry







theorem theorem_438298_problem
  (n : ℕ) (hn : n > 0)
  (a : Fin n → ℝ)
  (b₁ b₂ : ℝ)
  (h_b : b₁ < b₂)
  (C : Set (Fin n → ℝ))
  (hC : C = { w | (∀ i, 0 ≤ w i) ∧ (∀ i j, i ≤ j → w j ≤ w i) })
  (R : Set (Fin n → ℝ))
  (hR : R = { v | ∃ k : Fin n, v = fun i ↦ if i ≤ k then 1 else 0 })
  (H₁ : Set (Fin n → ℝ))
  (hH₁ : H₁ = { x | Matrix.dotProduct a x = b₁ })
  (H₂ : Set (Fin n → ℝ))
  (hH₂ : H₂ = { x | Matrix.dotProduct a x = b₂ })
  (P : Set (Fin n → ℝ))
  (hP : P = C ∩ { x | b₁ ≤ Matrix.dotProduct a x ∧ Matrix.dotProduct a x ≤ b₂ }) :
  Set.extremePoints ℝ P =
    { x | x ∈ P ∧ ∃ v ∈ R, ∃ t ≥ 0, x = t • v ∧ (x ∈ H₁ ∨ x ∈ H₂) } := by
  sorry







theorem theorem_438706_problem
  {𝕜 V : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V]
  (I₁ I₂ : InnerProductSpace.Core 𝕜 V)
  (h_ortho : ∀ (v w : V), I₁.inner v w = 0 ↔ I₂.inner v w = 0) :
  ∃ k : ℝ, 0 < k ∧ ∀ (v w : V), I₁.inner v w = (k : 𝕜) * I₂.inner v w := by
  sorry



theorem theorem_439196_problem (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (p v : EuclideanSpace ℝ (Fin n))
  (t : ℝ)
  (hf : Differentiable ℝ f) :
  deriv (fun t => f (p + t • v)) t = inner (gradient f (p + t • v)) v := by
  sorry

theorem theorem_439321_problem (n m : ℕ)
  (R : Matrix (Fin n) (Fin m) ℝ)
  (γ : ℝ)
  (hγ : 0 < γ) :
  let I : Matrix (Fin n) (Fin n) ℝ := 1
  (R * R.transpose + γ • I) * (R * R.transpose + γ • I)⁻¹ =
  R * R.transpose * (R * R.transpose + γ • I)⁻¹ + γ • (R * R.transpose + γ • I)⁻¹ := by
  sorry

theorem theorem_439307_problem {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [CommRing R]
  (P : Matrix n n R) (hP : P ^ 3 = 1) [Invertible P]
  (S : Matrix n n R) (hS : S = P - 1)
  (F : Matrix n n R → Matrix n n R)
  (hF : ∀ X, F X = 2 • X + P⁻¹ * X + 2 • X * P + P * X * P) :
  F S = 0 := by
  sorry

theorem theorem_439096_problem
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι κ : Type*} [Fintype ι]
  (x : ι → V)
  (p : κ → V)
  (μ : ι → κ → ℝ)
  (j : κ) :
  ∑ i, μ i j * inner (‖x i‖⁻¹ • x i) (‖p j‖⁻¹ • p j) =
  inner (∑ i, μ i j • (‖x i‖⁻¹ • x i)) (‖p j‖⁻¹ • p j) := by
  sorry







theorem theorem_439391_problem 
  (β₀ β₁ β₂ β₃ : ℝ)
  -- avg_y represents the "avg. y_it" function dependent on post_t and treated_i
  (avg_y : ℝ → ℝ → ℝ)
  -- The regression model assumption implies the average y takes this functional form
  -- (assuming the error term has an expectation of zero)
  (h_model : ∀ (post treated : ℝ), 
    avg_y post treated = β₀ + β₁ * post + β₂ * treated + β₃ * (post * treated)) :
  β₃ = ((avg_y 1 1 - avg_y 0 1) - (avg_y 1 0 - avg_y 0 0)) := by
  sorry





theorem theorem_439524_problem
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → ℝ) (x₀ a : E)
  (h_diff : Differentiable ℝ f)
  (h_eq : ∀ u : E, f (x₀ + u) - f x₀ = 2 * inner a x₀ * inner a u + (inner a u)^2)
  (L : E →L[ℝ] ℝ)
  (h_L : ∀ u : E, L u = 2 * inner a x₀ * inner a u) :
  fderiv ℝ f x₀ = L := by
  sorry

theorem theorem_439637_problem
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (a : H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
  (F : H →ₗ[ℝ] ℝ)
  (h_coercive : ∃ α : ℝ, 0 < α ∧ ∀ v : H, a v v ≥ α * ‖v‖^2)
  (u w : H)
  (hu : ∀ v : H, a u v = F v)
  (hw : ∀ v : H, a w v = F v) :
  u = w := by
  sorry















theorem theorem_440121_problem
  (n : ℕ)
  (V : Type*) [AddCommGroup V] [Module ℝ V]
  (F : MultilinearMap ℝ (fun _ : Fin n ↦ V) ℝ)
  (h_alt : ∀ (v : Fin n → V) (i j : Fin n), i ≠ j → v i = v j → F v = 0) :
  ∀ (v : Fin n → V) (i j : Fin n), i ≠ j → F (v ∘ Equiv.swap i j) = -F v := by
  sorry

theorem theorem_440016_problem
  (n : ℕ)
  (W : Matrix (Fin n) (Fin n) ℝ)
  (hW_symm : W.IsSymm)
  (hW_diag : ∀ i, W i i = 0)
  (P : (Fin n → ℕ) → ℝ)
  (a : Fin n → (Fin n → ℝ) → ℝ)
  (ha_def : ∀ i x, a i x = 1 / 2 * W i i * x i + 1 / 2 * ∑ j in Finset.univ.erase i, (W i j + W j i) * x j)
  (hP_form : ∀ i, ∃ h : (Fin n → ℕ) → ℝ,
    (∀ x y, (∀ j, j ≠ i → x j = y j) → h x = h y) ∧
    (∀ x, P x = h x * Real.exp (a i (fun k ↦ (x k : ℝ)) * (x i : ℝ))))
  (hP_pos : ∀ x, P x > 0)
  (x_fixed : Fin n → ℕ)
  (hx_binary : ∀ k, x_fixed k = 0 ∨ x_fixed k = 1)
  (i : Fin n) :
  let x1 := Function.update x_fixed i 1
  let x0 := Function.update x_fixed i 0
  let cond_prob := P x1 / (P x0 + P x1)
  let val_a := a i (fun k ↦ (x1 k : ℝ))
  cond_prob = Real.exp val_a / (Real.exp val_a + 1) := by
  sorry

theorem theorem_440572_problem
  (m n p : ℕ)
  (f : (Fin m → ℝ) → (Fin n → ℝ))
  (g : (Fin n → ℝ) → (Fin p → ℝ))
  (v : Fin m → ℝ)
  (hf : Differentiable ℝ f)
  (hg : Differentiable ℝ g) :
  fderiv ℝ (g ∘ f) v = (fderiv ℝ g (f v)).comp (fderiv ℝ f v) := by
  sorry









theorem theorem_440603_problem 
  {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  (B : Matrix n m ℝ) (K : Matrix m n ℝ) (S : Matrix n n ℝ) (S_sqrt : Matrix n n ℝ)
  (hS : S_sqrt * S_sqrt.transpose = S)
  (I_n : Matrix n n ℝ := 1)
  (M : Matrix (Sum n m) n ℝ := Matrix.of (fun i j => 
    match i with
    | Sum.inl i => (I_n + B * K) i j
    | Sum.inr i => K i j)) :
  let Sigma_Z := M * S * M.transpose
  let Sigma_Z_sqrt := M * S_sqrt
  Sigma_Z_sqrt * Sigma_Z_sqrt.transpose = Sigma_Z := by
  sorry



theorem theorem_440316_problem
  (n : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (α : ℝ)
  (h_diff : Differentiable ℝ f)
  (h_alpha : 0 < α)
  (h_strong_convex : ∀ x y : EuclideanSpace ℝ (Fin n),
    f x + inner (gradient f x) (y - x) + (α / 2) * ‖y - x‖^2 ≤ f y) :
  ∀ x y : EuclideanSpace ℝ (Fin n),
    (α / 2) * ‖y - x‖^2 + inner (gradient f x) (y - x) ≤ f y - f x := by
  sorry



theorem theorem_440861_problem (n m : ℕ) (f : (Fin n → ℝ) → (Fin m → ℝ))
  (e : Fin n → Fin n → ℝ) (he : e = fun i => Pi.single i 1)
  (u : Fin m → Fin m → ℝ) (hu : u = fun j => Pi.single j 1) :
  ∃ f_j : Fin m → (Fin n → ℝ) → ℝ,
    ∀ x : Fin n → ℝ, f x = ∑ j : Fin m, (f_j j x) • (u j) := by
  sorry



theorem theorem_440774_problem (R : Type*) [CommRing R] [Nontrivial R] :
  ¬ ∃ v : R × R, ∀ x : R × R, ∃ r : R, r • v = x := by
  sorry

















theorem theorem_441265_problem
  {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (n : ℕ)
  (v : Fin n → V)
  (hv : LinearIndependent K v)
  (w : Fin (n + 1) → V)
  (hw : ∀ i, w i ∈ Submodule.span K (Set.range v)) :
  ¬ LinearIndependent K w := by
  sorry





theorem theorem_441467_problem 
  (x₁ y₁ z₁ w₁ : ℝ) 
  (u₀ v₀ t₀ : ℝ) 
  (F₁ : ℝ → ℝ → ℝ → ℝ → ℝ) 
  (F₂ F₃ : ℝ → ℝ → ℝ → ℝ) 
  (h_w : w₁ ≠ 0)
  (h_u : u₀ = x₁ / w₁)
  (h_v : v₀ = y₁ / w₁)
  (h_t : t₀ = z₁ / w₁)
  (h_sol : F₁ 1 u₀ v₀ t₀ = 0 ∧ F₂ u₀ v₀ t₀ = 0 ∧ F₃ u₀ v₀ t₀ = 0) :
  x₁ = w₁ * u₀ ∧ y₁ = w₁ * v₀ ∧ z₁ = w₁ * t₀ := by
  sorry





theorem theorem_441390_problem (n : ℕ) (x : Fin n → ℝ) (p q : ℝ)
  (h1 : 1 ≤ p) (h2 : p < q) :
  (∑ i, |x i| ^ p) ^ (1 / p) ≤ (n : ℝ) ^ (1 / p - 1 / q) * (∑ i, |x i| ^ q) ^ (1 / q) := by
  sorry

theorem theorem_442149_problem
  {n : Type*} [Fintype n] [DecidableEq n]
  [NormedAddCommGroup (Matrix n n ℝ)] [NormedSpace ℝ (Matrix n n ℝ)]
  (A : Matrix n n ℝ)
  (β : ℝ)
  (hA : IsUnit A)
  (hβ : 0 < β) :
  ‖β • A‖ * ‖(β • A)⁻¹‖ = ‖A‖ * ‖A⁻¹‖ := by
  sorry

theorem theorem_442356_problem (n : ℕ) (p : ℝ) (x y z : Fin n → ℝ)
  (hp : 1 ≤ p) :
  (∑ i, |(x - z) i| ^ p) ^ (1 / p) ≤
  (∑ i, |(x - y) i| ^ p) ^ (1 / p) + (∑ i, |(y - z) i| ^ p) ^ (1 / p) := by
  sorry



