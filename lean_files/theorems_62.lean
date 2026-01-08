import Mathlib
import Mathlib.Tactic



theorem theorem_332877_problem :
  ∃ (n : ℕ) (B C : Matrix (Fin n) (Fin n) ℝ),
    B.PosDef ∧ C.PosDef ∧
    let A : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ max (B i j) (C i j)
    ¬ A.PosDef := by
  sorry

theorem theorem_332704_problem
  (n m : ℕ)
  (A : Matrix (Fin n) (Fin m) ℝ)
  (W : Matrix (Fin n) (Fin n) ℝ)
  (b : Matrix (Fin n) (Fin 1) ℝ)
  (hW_symm : W.IsSymm)
  (hW_pos : W.PosDef)
  (h_inv : Invertible (A.transpose * W * A)) :
  (b.transpose * W * A * (A.transpose * W * A)⁻¹ * A.transpose * W * b) 0 0 =
  Matrix.trace (W * b * b.transpose * W * A * (A.transpose * W * A)⁻¹ * A.transpose) := by
  sorry

theorem theorem_332908_problem :
  ∃ F : ℕ → ℝ → ℝ,
    (∀ n : ℕ, sSup (Set.range (fun x ↦ |F n x|)) = 1) ∧
    ¬ (∀ x : ℝ, Filter.Tendsto (fun n ↦ F n x) Filter.atTop (nhds 0)) := by
  sorry

theorem theorem_333379_problem
  (n m : Type*) [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  (A : Matrix n n ℝ) (C D : Matrix m m ℝ)
  (hA : A.IsSymm) (hC : C.IsSymm) (hD : D.IsSymm)
  (h_cong : ∃ P : Matrix (n ⊕ m) (n ⊕ m) ℝ, IsUnit P.det ∧
    P.transpose * (Matrix.fromBlocks A 0 0 C) * P = Matrix.fromBlocks A 0 0 D) :
  ∃ Q : Matrix m m ℝ, IsUnit Q.det ∧ Q.transpose * C * Q = D := by
  sorry









theorem theorem_333566_problem
  (n q p : ℕ)
  (Bx : Matrix (Fin n) (Fin q) ℝ)
  (Bz : Matrix (Fin n) (Fin p) ℝ)
  (M : Matrix (Fin n) (Fin q × Fin p) ℝ)
  -- Condition: M is constructed by selecting rows from the Kronecker product where row indices match (i = r)
  (hM : ∀ (i : Fin n) (j : Fin q) (s : Fin p),
    M i (j, s) = (Matrix.kronecker Bx Bz) (i, i) (j, s)) :
  -- Conclusion: M is defined as M_{i, (j,s)} = (B_x)_{ij} (B_z)_{is}
  ∀ (i : Fin n) (j : Fin q) (s : Fin p),
    M i (j, s) = Bx i j * Bz i s := by
  sorry





theorem theorem_333418_problem (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) :
  ∃ (P : Matrix (Fin m) (Fin m) ℤ) (Q : Matrix (Fin n) (Fin n) ℤ),
    IsUnit P ∧ IsUnit Q ∧
    let B := P * A * Q
    (∀ i j, i.val ≠ j.val → B i j = 0) ∧
    (∀ i j, i.val = j.val → 0 ≤ B i j) ∧
    (∀ i j i' j', i.val = j.val → i'.val = j'.val → i.val + 1 = i'.val → B i j ∣ B i' j') := by
  sorry

theorem theorem_333802_problem
  {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  (A : Matrix I K ℝ) (B : Matrix J K ℝ)
  (hA : 1 ≤ A.rank) (hB : 1 ≤ B.rank) :
  let KR : Matrix (I × J) K ℝ := Matrix.of (fun (ij : I × J) k => A ij.1 k * B ij.2 k)
  min (A.rank + B.rank - 1) (Fintype.card K) ≤ KR.rank := by
  sorry



































theorem theorem_334190_problem
  -- Coordinates for P_{i-1}, P_i, P_{i+1}
  (x_prev y_prev x_curr y_curr x_next y_next : ℝ)
  -- 1. Define vectors v1 and v2
  (v1 : ℝ × ℝ := (x_prev - x_curr, y_prev - y_curr))
  (v2 : ℝ × ℝ := (x_next - x_curr, y_next - y_curr))
  -- Condition: Simple polygon implies vertices are not collinear locally (cross product non-zero)
  (cross_val : ℝ := v1.1 * v2.2 - v1.2 * v2.1)
  (h_simple : cross_val ≠ 0) :
  let norm := λ (v : ℝ × ℝ) => Real.sqrt (v.1^2 + v.2^2)
  -- 2. Normalize v1 and v2
  let v1_prime := (v1.1 / norm v1, v1.2 / norm v1)
  let v2_prime := (v2.1 / norm v2, v2.2 / norm v2)
  -- 3. Compute bisector b
  let b := (v1_prime.1 + v2_prime.1, v1_prime.2 + v2_prime.2)
  -- 4. Correct the direction
  let b_corrected := (Real.sign cross_val * b.1, Real.sign cross_val * b.2)
  -- Definition of geometric outward direction for validation:
  -- For CCW polygon, outward is to the right.
  -- Right normal of incoming edge (P_prev -> P_curr, vector -v1)
  -- Right normal of outgoing edge (P_curr -> P_next, vector v2)
  let rotate_minus_90 := λ (v : ℝ × ℝ) => (v.2, -v.1)
  let n_in := rotate_minus_90 (-v1.1, -v1.2)
  let n_out := rotate_minus_90 v2
  -- Normalize normals for purely directional sum
  let n_in_u := (n_in.1 / norm n_in, n_in.2 / norm n_in)
  let n_out_u := (n_out.1 / norm n_out, n_out.2 / norm n_out)
  let true_outward := (n_in_u.1 + n_out_u.1, n_in_u.2 + n_out_u.2)
  -- 5. Conclusion: The corrected vector points in the true outward direction
  -- (i.e., they are positive scalar multiples of each other)
  ∃ k : ℝ, k > 0 ∧ b_corrected = (k * true_outward.1, k * true_outward.2) := by
  sorry



theorem theorem_334563_problem
  (n d : ℕ)
  (x : Fin n → Fin d → ℝ)
  (y : Fin n → ℝ)
  (α : Fin n → ℝ)
  (S : Finset (Fin n))
  (θ₀ : ℝ)
  (hS_nonempty : S.card > 0)
  (hy : ∀ i, y i = 1 ∨ y i = -1)
  (h_support : ∀ t ∈ S, y t * ((∑ j : Fin n, α j * y j * Matrix.dotProduct (x j) (x t)) + θ₀) = 1) :
  θ₀ = (1 / (S.card : ℝ)) * ∑ t in S, (y t - ∑ j : Fin n, α j * y j * Matrix.dotProduct (x j) (x t)) := by
  sorry







theorem theorem_335224_problem (d : ℕ) :
  LinearIndependent ℝ (fun (n : Fin d) => fun (x : ℝ) ↦ Real.sin (((n : ℕ) + 1 : ℝ) * x)) := by
  sorry



theorem theorem_335292_problem
  (n : ℕ) (hn : 0 < n)
  (a b : Fin n → ℝ)
  (ones : Fin n → ℝ)
  (h_ones : ones = fun _ ↦ 1)
  (dot : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
  (h_dot : ∀ u v, dot u v = ∑ i, u i * v i)
  (mean : (Fin n → ℝ) → ℝ)
  (h_mean : ∀ v, mean v = (1 / (n : ℝ)) * dot v ones)
  (norm_sq : (Fin n → ℝ) → ℝ)
  (h_norm_sq : ∀ v, norm_sq v = dot v v)
  (h_b : dot b ones = 0) :
  ((1 / (n : ℝ)) * norm_sq a - (mean a)^2) * ((1 / (n : ℝ)) * norm_sq b) ≥
  ((1 / (n : ℝ)) * dot a b)^2 := by
  sorry

theorem theorem_335538_problem
  (n d : ℕ)
  (G : SimpleGraph (Fin n))
  [DecidableRel G.Adj]
  (f : Fin n → Fin d → ℝ)
  (X : Matrix (Fin n) (Fin d) ℝ)
  (hX : ∀ i j, X i j = f i j)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : ∀ i j, A i j = if G.Adj i j then 1 else 0)
  (D_mat : Matrix (Fin n) (Fin n) ℝ)
  (hD : ∀ i j, D_mat i j = if i = j then (G.degree i : ℝ) else 0)
  (Δ : Matrix (Fin n) (Fin n) ℝ)
  (hΔ : Δ = D_mat - A) :
  (X.transpose * Δ * X).trace =
  (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n, if G.Adj i j then ∑ k : Fin d, (f i k - f j k)^2 else 0 := by
  sorry







theorem theorem_335430_problem
  (n : ℕ)
  (y tau_vec : Fin n → ℝ)
  (tau_e : (Fin n → ℝ) → ℝ)
  (j : Fin n)
  (h_dep : ∃ f : ℝ → ℝ, ∀ x, tau_e x = f (x j)) :
  ∀ (i : Fin n), i ≠ j → ∀ (x : Fin n → ℝ) (v : ℝ), tau_e (Function.update x i v) = tau_e x := by
  sorry

theorem theorem_335557_problem (n : ℕ) (u v w x : Fin n → Fin n → ℝ) :
  ∑ i : Fin n, ∑ j : Fin n, (u i j * v j i + w j i * x i j) =
  ∑ i : Fin n, ∑ j : Fin n, (u i j * v j i + w i j * x j i) := by
  sorry

theorem theorem_336785_problem (k m : ℕ)
  (f g : (Fin k → ℝ) → (Fin m → ℝ))
  (D : Set (Fin k → ℝ))
  (hf : Continuous f)
  (hg : Continuous g)
  (hD : Dense D)
  (h_eq : ∀ x ∈ D, f x = g x) :
  ∀ x, f x = g x := by
  sorry

theorem theorem_336155_problem
  (x y : ℕ → ℝ)
  (a : ℝ)
  (n : ℕ → ℕ)
  (hn : StrictMono n)
  (hx : Filter.Tendsto (x ∘ n) Filter.atTop (nhds a))
  (h_diff : Filter.Tendsto (fun i ↦ |y (n i) - x (n i)|) Filter.atTop (nhds 0)) :
  Filter.Tendsto (y ∘ n) Filter.atTop (nhds a) := by
  sorry



theorem theorem_336169_problem (a b c x y z : ℝ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (h_tri_abc : a + b > c ∧ a + c > b ∧ b + c > a)
  (h_tri_xyz : x + y > z ∧ x + z > y ∧ y + z > x)
  (h_ord_abc : a ≤ b ∧ b ≤ c)
  (h_ord_xyz : x ≤ y ∧ y ≤ z) :
  (∃ k : ℝ, k > 0 ∧ a = k * x ∧ b = k * y ∧ c = k * z) ↔
  crossProduct ![a, b, c] ![x, y, z] = 0 := by
  sorry









theorem theorem_336524_problem (n q p : ℕ)
  (hn : n > 0)
  [NeZero q]
  [Fact p.Prime]
  (hpq : p ∣ q)
  (hlt : p < q) :
  let total_matrices := Fintype.card (Matrix (Fin n) (Fin n) (ZMod q))
  let A_singular_count := Fintype.card { A : Matrix (Fin n) (Fin n) (ZMod q) // A.det = 0 }
  let B_singular_count := Fintype.card { A : Matrix (Fin n) (Fin n) (ZMod q) // (A.map (ZMod.castHom hpq (ZMod p))).det = 0 }
  (B_singular_count : ℚ) / total_matrices > (A_singular_count : ℚ) / total_matrices := by
  sorry



theorem theorem_336589_problem (n : ℕ)
  (l : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
  (x : Fin n → ℝ) :
  fderiv ℝ l x = l := by
  sorry

theorem theorem_336454_problem
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (x : ℕ → X)
  (h : CauchySeq (fun n => ∑ i in Finset.range n, x i)) :
  Summable x := by
  sorry







theorem theorem_336384_problem
  {K V : Type*}
  [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (L : Module.End K V)
  (ν : K)
  (m : ℕ) (hm : m = L.charpoly.rootMultiplicity ν)
  (k : ℕ) (hk : k = FiniteDimensional.finrank K (Module.End.eigenspace L ν)) :
  k ≤ m := by
  sorry

theorem theorem_336428_problem (p : ℕ)
  (A B C V : Matrix (Fin p) (Fin 1) ℝ)
  (hV : ∀ i, V i 0 = 1) :
  ∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p, A i 0 * B j 0 * C k 0 =
  (A.transpose * V) 0 0 * (B.transpose * V) 0 0 * (C.transpose * V) 0 0 := by
  sorry











theorem theorem_337133_problem (k : ℕ) (m : ℕ → ℝ)
  (h : ∀ n : ℕ, ∑ i in Finset.Icc 1 k, m i * (n : ℝ) ^ (2 ^ i) = 0) :
  ∀ i ∈ Finset.Icc 1 k, m i = 0 := by
  sorry







theorem theorem_337531_problem 
  {K E : Type*} [Fintype K] [Fintype E]
  (c_A1 c_A2 : ℝ)
  (u_1 v_1 : K → ℝ)
  (u_2 v_2 : E → ℝ)
  (h_c1 : 0 ≤ c_A1)
  (h_c2 : 0 ≤ c_A2) :
  (∑ k, c_A1 * u_1 k * v_1 k) + (∑ e, c_A2 * u_2 e * v_2 e) ≤
  (max c_A1 c_A2) * 
  Real.sqrt ((∑ k, (u_1 k) ^ 2) + (∑ e, (u_2 e) ^ 2)) * 
  Real.sqrt ((∑ k, (v_1 k) ^ 2) + (∑ e, (v_2 e) ^ 2)) := by
  sorry





theorem theorem_337968_problem
  {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  (n : ℕ)
  (Ti : Fin n → V →ₗ[F] F)
  (T : V →ₗ[F] F)
  (h_indep : LinearIndependent F Ti)
  (h_ker : (⨅ i, LinearMap.ker (Ti i)) ≤ LinearMap.ker T) :
  ∃ c : Fin n → F, T = ∑ i, c i • Ti i := by
  sorry



theorem theorem_338155_problem
  (R : Type*) [CommRing R] [TopologicalSpace R] [TopologicalRing R] [T1Space R]
  (n : ℕ)
  (h_cont : Continuous (Matrix.det : Matrix (Fin n) (Fin n) R → R)) :
  IsClosed {A : Matrix (Fin n) (Fin n) R | Matrix.det A = 0} := by
  sorry











theorem theorem_338530_problem
  (n m : ℕ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (B : Matrix (Fin n) (Fin m) ℝ)
  (C : Matrix (Fin m) (Fin n) ℝ)
  (D : Matrix (Fin m) (Fin m) ℝ)
  (h_D : D = 0)
  (h_rel_deg : C * B = 0)
  (h_rank : B.rank = m)
  (h_inputs : m ≤ n)
  (h_m_pos : m > 0) :
  ¬ ∃ P : Matrix (Fin n) (Fin n) ℝ, P.PosDef ∧ P * B = C.transpose := by
  sorry

theorem theorem_337129_problem
  {X : Type*} [AddCommGroup X] [Module ℝ X]
  (A B : Set X)
  (n : ℕ)
  (x_star : Fin n → X →ₗ[ℝ] ℝ)
  (q : Fin n → ℝ)
  (hq : ∀ i, 0 ≤ q i)
  (h_sup : ∀ i, sSup ((x_star i) '' A) ≤ sSup ((x_star i) '' B)) :
  sSup ((∑ i, q i • x_star i) '' A) ≤ sSup ((∑ i, q i • x_star i) '' B) := by
  sorry

theorem theorem_337755_problem
  (G : Set ℂ) (hG_open : IsOpen G) (hG_conn : IsConnected G)
  (f : ℂ → ℂ) (hf_holo : DifferentiableOn ℂ f G)
  (a : ℝ)
  (L : Set ℂ) (hL_def : L = {z : ℂ | z.re = a})
  (h_inter_nonempty : (G ∩ L).Nonempty)
  (h_zero_on_L : ∀ z ∈ G, z ∈ L → f z = 0) :
  ∀ z ∈ G, f z = 0 := by
  sorry

theorem theorem_338669_problem
  (n : ℕ)
  (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
  (t t₀ : ℝ)
  (h : ∀ i j, HasSum (fun k : ℕ => (iteratedDeriv k (fun x => A x i j) t₀) / (k.factorial : ℝ) * (t - t₀) ^ k) (A t i j)) :
  HasSum (fun k : ℕ => (t - t₀) ^ k • Matrix.of (fun i j => (iteratedDeriv k (fun x => A x i j) t₀) / (k.factorial : ℝ))) (A t) := by
  sorry

theorem theorem_338552_problem
  (W : Type*) [AddCommGroup W] [Module ℝ W]
  (g : Unit → W) :
  ∃! (g_tilde : ℝ →ₗ[ℝ] W), g = g_tilde ∘ (fun (_ : Unit) ↦ (1 : ℝ)) := by
  sorry



theorem theorem_338363_problem
  (a b c d e f : ℝ)
  (h_det : a * d - b * c ≠ 0)
  (A B C D E F : ℝ) :
  ∃ A' B' C' D' E' F' : ℝ,
    let T : ℝ × ℝ → ℝ × ℝ := fun p ↦ (a * p.1 + b * p.2 + e, c * p.1 + d * p.2 + f)
    let S := {p : ℝ × ℝ | A * p.1^2 + B * p.1 * p.2 + C * p.2^2 + D * p.1 + E * p.2 + F = 0}
    let S' := {p : ℝ × ℝ | A' * p.1^2 + B' * p.1 * p.2 + C' * p.2^2 + D' * p.1 + E' * p.2 + F' = 0}
    T '' S = S' := by
  sorry





theorem theorem_338597_problem (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA : A.PosDef) (hB : B.PosDef)
  (hBA : (B - A).PosDef) :
  (A⁻¹ - B⁻¹).PosDef := by
  sorry





theorem theorem_338441_problem
  (M K : Matrix (Fin 3) (Fin 3) ℝ)
  (s : Fin 3 → ℝ)
  (S : Matrix (Fin 3) (Fin 3) ℝ)
  (T : Matrix (Fin 3) (Fin 3) ℝ)
  (r : Fin 3 → ℝ)
  (hM : M ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
  (hS : S = Matrix.diagonal s)
  (hT : T = M * S)
  (hK : K ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
  (hr : ∀ i, IsGreatest {y | ∃ u, (∀ j, |u j| ≤ 1) ∧ y = |((K.transpose * T).mulVec u) i|} (r i)) :
  ∀ i, r i = ∑ j, |(K.transpose * T) i j| := by
  sorry

theorem theorem_338924_problem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
  (h : Matrix.det A ≠ 0) :
  A⁻¹ = (Matrix.det A)⁻¹ • Matrix.adjugate A := by
  sorry

theorem theorem_339053_problem (n : ℕ)
  (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
  (f : ℝ → (Fin n → ℝ))
  (g : Fin n → ℝ)
  (hf : Continuous f) :
  ∃! u : ℝ → (Fin n → ℝ), (∀ t, HasDerivAt u (A (u t) + f t) t) ∧ u 0 = g := by
  sorry





