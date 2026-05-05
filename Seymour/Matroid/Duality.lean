import Seymour.Matroid.Regularity

/-!
# Matroid Duality

Here we study the duals of matroids given by their standard representation.
-/
open scoped Classical
open scoped Matrix

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


def StandardRepr.equivX {S S' : StandardRepr α R} (h : S.X = S'.X) :
    S'.X ≃ S.X :=
  Equiv.setCongr h.symm

def StandardRepr.equivUnion {S S' : StandardRepr α R} (h : S.X = S'.X) (hY : S.Y = S'.Y) :
    ↑ (S'.X ∪ S'.Y) ≃ ↑ (S.X ∪ S.Y) :=
  Equiv.setCongr ( by rw [h, hY])
-- 1. Turn the set equality into a type equivalence
def StandardRepr.domainEquiv {S S' : StandardRepr α R} (h : S.X = S'.X ∧ S.Y = S'.Y) :
    ↑(S'.X ∪ S'.Y) ≃ ↑(S.X ∪ S.Y) :=
  Equiv.setCongr (by rw [h.1, h.2])


set_option diagnostics true
def VectorsWithOnlySomeIndexes (R: Type*)[Field R] (E : Set α)(S: Set α) : Submodule R (E → R) where
  -- The set of vectors v where v(a) = 0 for all a ∉ S
  carrier := {v : E → R | ∀ a: E, (a: α) ∉ S → v a = 0}
  zero_mem' := by
    intro a _
    rfl
  add_mem' := by
    intro u v hu hv a ha
    simp [hu a ha, hv a ha]
  smul_mem' := by
    intro c v hv a ha
    simp [hv a ha]
    



/-
private lemma base_iff_complement [Finite α] [Field R] (S : StandardRepr α R) (X : Set α) :
    S.toMatroid.IsBase X ↔ (rowSpace R S) ⊓ (VectorsWithOnlySomeIndexes R S.toMatroid.E Xᶜ) = ⊥  ∧ Set.ncard X = Module.finrank R (rowSpace R S) := by
  rw [Matroid.isBase_iff_maximal_indep]
  constructor
  · intro hX
    constructor
    · sorry
    · sorry
  · intro ⟨hX, hXSize⟩
    have h := Submodule.finrank_sup_add_finrank_inf_eq (rowSpace R S) (VectorsWithOnlySomeIndexes R S.toMatroid.E Xᶜ)
    rw [hX] at h
    sorry
    -/

  

    
        



