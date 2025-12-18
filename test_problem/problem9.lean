import Mathlib

open Filter BigOperators Set Topology Function Module EReal Inner Pointwise

/- medium -/
theorem EReal_epi_closed_of_Real_epi_closed_of_nebot_netop {E : Type*} [NormedAddCommGroup E] {s : Set E}
    {f : E → EReal} {xn : ℕ → E × EReal} {x : E} {y : EReal}
    (hybot : y ≠ ⊥) (hytop : y ≠ ⊤) (hxy : ∀ (n : ℕ), (xn n).1 ∈ s ∧ f (xn n).1 ≤ (xn n).2)
    (hlim : Tendsto xn atTop (𝓝 (x, y)))
    (h : _root_.IsClosed {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2}) :
    f x ≤ y := by
  lift y to Real using ⟨hytop, hybot⟩
  let g := Prod.map (@id E) EReal.toReal
  have in_and_le : ∃ᶠ (x : ℕ) in atTop, (g (xn x)).1 ∈ s ∧ f (g (xn x)).1 ≤ (g (xn x)).2 := by
    simp [g]
    refine Eventually.and_frequently ?hp ?hq
    refine Filter.eventually_of_forall ?hp.hp
    intro n
    apply (hxy n).1
    refine frequently_atTop.mpr ?hq.a
    intro N
    by_cases hxntop : ∀ b ≥ N, (xn b).2 = ⊤
    simp [Prod.tendsto_iff] at hlim
    have key : y = (⊤ : EReal) :=
      tendsto_nhds_unique hlim.2 (tendsto_atTop_of_eventually_const hxntop)
    exact False.elim (hytop key)
    simp at hxntop
    obtain ⟨b, hb⟩ := hxntop
    use b
    simp
    constructor
    exact hb.1
    by_cases hfb : f (xn b).1 = ⊥
    rw [hfb]; simp
    by_cases hxnbot : (xn b).2 = ⊥
    have : f (xn b).1 = ⊥ := bot_unique <| hxnbot ▸ (hxy b).2
    exact False.elim (hfb this)
    rw [EReal.coe_toReal hb.2 hxnbot]
    apply (hxy b).2
  have prep : Tendsto (fun n => (xn n).2.toReal) atTop (𝓝 y) := by
    rw [← tendsto_coe]
    simp [Prod.tendsto_iff] at *
    obtain hm := hlim.2
    have : ∀ᶠ x in atTop, (fun a ↦ ↑(xn a).2.toReal) x = (xn x).2 := by
      rw [@tendsto_iff_seq_tendsto] at hm
      simp
      by_contra! hab
      let x : ℕ → ℕ := fun n => (hab n).choose
      have xs := fun n => (hab n).choose_spec
      have xlim :  Tendsto x atTop atTop := by
        simp [tendsto_atTop_atTop, x]
        intro t
        exact ⟨t, fun a hab => Nat.le_trans hab (xs a).1⟩
      have mx : ∀ n, ((xn ∘ x) n).2 = ⊤ ∨  ((xn ∘ x) n).2 = ⊥ := by
        intro n
        simp [x]
        by_contra!
        apply (xs n).2
        refine coe_toReal this.1 this.2
      have := hm _ xlim
      rw [@tendsto_atTop'] at this
      have innbhd : {(⊥ : EReal), ⊤}ᶜ ∈ 𝓝 ↑y := by
        refine (IsOpen.mem_nhds_iff ?hs).mpr ?_
        simp
        rw [← @Finset.coe_pair]; simp
        refine Finite.isClosed ?hs.hs
        simp
        simp
      have ⟨a, ha⟩:= this {⊥, ⊤}ᶜ innbhd
      exact (ha a (by simp)) (id (Or.symm (mx a)))
    exact (tendsto_congr' this).mpr hm
  have glim : Tendsto (g ∘ xn) atTop (𝓝 (x, y)) := by
    simp [Prod.tendsto_iff] at *
    simp [g]
    exact ⟨hlim.left, prep⟩
  have := IsClosed.mem_of_frequently_of_tendsto h in_and_le glim
  simp at this
  exact this.2
