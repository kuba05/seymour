import Seymour.Matroid.Regularity

/-!
# Matroid Duality

Here we study the duals of matroids given by their standard representation.
-/
open scoped Classical
open scoped Matrix
open scoped Classical

variable {α R : Type*} [DecidableEq α]

/-- The dual of standard representation (transpose the matrix and flip its signs). -/
def StandardRepr.dual [DivisionRing R] (S : StandardRepr α R) : StandardRepr α R where
  X := S.Y
  Y := S.X
  hXY := S.hXY.symm
  B := - S.Bᵀ -- the sign is chosen following Oxley (it does not change the resulting matroid)
  decmemX := S.decmemY
  decmemY := S.decmemX

postfix:max "✶" => StandardRepr.dual

/-- The dual of dual is the original standard representation. -/
lemma StandardRepr.dual_dual [DivisionRing R] (S : StandardRepr α R) : S✶✶ = S := by
  simp [StandardRepr.dual]

lemma StandardRepr.dual_indices_union_eq [DivisionRing R] (S : StandardRepr α R) : S✶.X ∪ S✶.Y = S.X ∪ S.Y :=
  Set.union_comm S.Y S.X

@[simp]
lemma StandardRepr.dual_ground [DivisionRing R] (S : StandardRepr α R) : S✶.toMatroid.E = S.toMatroid.E :=
  S.dual_indices_union_eq

lemma dual_standard_is_dual [DivisionRing R](S : StandardRepr α R) :
    S.dual.toMatroid = S.toMatroid.dual := by
      sorry

lemma isRegular.dual2 [Fintype α]{M : Matroid α} (hM : M.IsRegular) :
    (M✶).IsRegular := by
      unfold Matroid.IsRegular
      unfold Matroid.IsRegular at hM
      obtain ⟨X, Y, x, hTU, hEq⟩ := hM
      obtain ⟨someBase, h_someBase⟩ := x.toMatroid.exists_isBase  
      obtain ⟨S, ⟨_, hS, hSTU⟩⟩ := x.exists_standardRepr_isBase_isTotallyUnimodular h_someBase hTU 
      let S' := S.dual
      refine ⟨S'.X, S'.X ∪ S'.Y, S'.toFull, ?_⟩
      constructor
      · unfold S'
        change Matrix.IsTotallyUnimodular (((1 : Matrix S.Y S.Y _) ◫ -S.Bᵀ) · ∘ Subtype.toSum)
        have h1 : S.Bᵀ.IsTotallyUnimodular := by 
          rw [<- Matrix.transpose_isTotallyUnimodular_iff] at hSTU
          exact hSTU
        have h2 : (-S.Bᵀ).IsTotallyUnimodular := h1.neg
        have h3 : (1 ◫ -S.Bᵀ).IsTotallyUnimodular := h2.one_fromCols
        exact Matrix.IsTotallyUnimodular.comp_cols h3 Subtype.toSum
      · convert_to S.dual.toMatroid = M.dual
        rw [dual_standard_is_dual, hS, hEq]
