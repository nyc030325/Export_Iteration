import Mathlib

open Matrix Finset Filter Topology spectrum

/- 6 : medium -/
def Matrix.lowerPart {α : Type*} {n : ℕ} (X : Matrix (Fin n) (Fin n) α) [Zero α] :
  Matrix (Fin n) (Fin n) α := fun i j => if j ≥ i then 0 else X i j

def Matrix.upperPart {α : Type*} {n : ℕ} (X : Matrix (Fin n) (Fin n) α) [Zero α] :
  Matrix (Fin n) (Fin n) α := fun i j => if j ≤ i then 0 else X i j

abbrev Matrix.diagPart {n α : Type*} [DecidableEq n] (X : Matrix n n α) [Zero α] :=
  Matrix.diagonal (fun i => X i i)

lemma Matrix.non_zero_diag {α : Type*} {n : ℕ} [NormedField α] (A : Matrix (Fin n) (Fin n) α)
    (hA : ∀ i, A i i ≠ 0) : IsUnit (A.diagPart + A.lowerPart).det := by
  have h_diag : ∀ i, IsUnit ((A.diagPart + A.lowerPart) i i) := by
    intro i
    simp [lowerPart]
    exact hA i
  have hd : A.diagPart.BlockTriangular ⇑OrderDual.toDual := by
    simp [diagPart]
    exact blockTriangular_diagonal fun i ↦ A i i
  have hl : A.lowerPart.BlockTriangular ⇑OrderDual.toDual := by
    unfold lowerPart
    unfold BlockTriangular
    simp
    intro i j hij hji
    absurd hij
    simpa using hji.le
  have h : (A.diagPart + A.lowerPart).BlockTriangular ⇑OrderDual.toDual := by
    exact BlockTriangular.add hd hl
  have det_eq : (A.diagPart + A.lowerPart).det =
      ∏ i : (Fin n), (A.diagPart + A.lowerPart) i i :=
    det_of_lowerTriangular (A.diagPart + A.lowerPart) h
  have det_unit : IsUnit (A.diagPart + A.lowerPart).det := by
    rw [det_eq]
    simp [- add_apply]
    push_neg
    simp [- add_apply] at h_diag
    push_neg at h_diag
    rw [@prod_ne_zero_iff]
    intro a ha
    exact h_diag a
  exact det_unit
