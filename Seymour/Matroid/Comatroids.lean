import Seymour.Matroid.Duality

open scoped Matrix
open Classical
variable {α R : Type*} [DecidableEq α] [Field R]

def rowSpace {R: Type*} [DivisionRing R] (S : StandardRepr α R) : Submodule R (↑S.toMatroid.E → R) :=
    Submodule.span R (Set.range S.toFull)

def colSpace {R: Type*} [DivisionRing R] (S : StandardRepr α R) : Submodule R (↑S.X → R) :=
    Submodule.span R (Set.range S.toFullᵀ)

noncomputable def extendFunction {A B : Set α} [Field R](f : A → R): B → R :=
  fun x =>
    if h : (x : α) ∈ A then
      f ⟨(x : α), h⟩
    else
      0

noncomputable def algebraicOrtho [Fintype α] {R : Type*} [Field R] {E : Set α}
  (M : Submodule R (E → R)) : Submodule R (E → R) where
  carrier := {v | ∀ u ∈ M, ∑ i, u i * v i = 0}
  zero_mem' := by simp
  add_mem' hx hy u hu := by simp [hx u hu, hy u hu, mul_add, Finset.sum_add_distrib]
  smul_mem' c x hx u hu := by 
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm]
    rw [<- Finset.mul_sum]
    simp [<- Finset.mul_sum, hx u hu]

lemma mem_cast_algebraicOrtho {α R : Type*} [Fintype α] [Field R]
    {E₁ E₂ : Set α} (h : E₁ = E₂) (M : Submodule R (E₁ → R)) (v : E₂ → R) :
    v ∈ h ▸ algebraicOrtho M ↔ 
    ∀ u ∈ M, ∑ i : E₁, u i * v ⟨i.val, h ▸ i.property⟩ = 0 := by
  -- Because E₁ and E₂ are free variables here, subst works perfectly!
  subst h
  -- The cast disappears, and the goal becomes definitionally true.
  rfl

  
lemma Matroid.isBase_ncard [Fintype α]{M : Matroid α} {I J : Set α} (h_size : I.ncard = J.ncard) (hI : M.IsBase I) (hJ : M.Indep J) :
    M.IsBase J := by 
      rw [Matroid.isBase_iff_maximal_indep]
      simp [Maximal, hJ]
      intro y hY hJ_y
      obtain ⟨B, ⟨hB_base, hB_subset⟩⟩ := hY.exists_isBase_superset 
      have : y.ncard ≤ J.ncard := by
        have : B.ncard = J.ncard := by
          rw [<- h_size]
          have x := (Matroid.isBase_exchange M).encard_isBase_eq hB_base hI
          apply_fun ENat.toNat at x
          change B.ncard = I.ncard at x
          exact x
        rw [<-this]
        exact Set.ncard_le_ncard hB_subset 

      have := Set.eq_of_subset_of_ncard_le hJ_y this
      simp [this]
            



      
  
set_option pp.proofs true
lemma StandardRepr.toMatroid.isBase_iff [Fintype α]{A : StandardRepr α R} {I : Set α} (hI : I ⊆ (A.X ∪ A.Y)):
  A.toMatroid.IsBase I ↔ (I.ncard = A.X.ncard ∧ LinearIndependent R (A.toFull.submatrix id (fun j => ⟨j.val, hI j.property⟩): Matrix A.X I R)ᵀ ) := by
  --A.toMatroid.IsBase I ↔ (I.ncard = A.X.ncard ∧ LinearIndependent R (A.toFull.submatrix id (fun j => ⟨j.val, hI j.property⟩): Matrix A.X I R)ᵀ ) := by
    set small : Matrix A.X I R := (A.toFull.submatrix id (fun j => ⟨j.val, hI j.property⟩))
    constructor
    · intro hI_base
      have hI_size : I.ncard = A.X.ncard := by
        have := (A.toMatroid.isBase_exchange).encard_isBase_eq hI_base A.toMatroid_isBase_X 
        apply_fun ENat.toNat at this
        change I.ncard = A.X.ncard at this
        exact this
      simp [hI_size]
      rw [StandardRepr.toMatroid, Matrix.toMatroid, IndepMatroid.matroid_IsBase, Maximal] at hI_base
      have : A.toMatroid.Indep I := hI_base.1
      rw [StandardRepr.toMatroid_indep_iff_submatrix] at this
      obtain ⟨hI, this⟩ := this
      unfold small
      convert this
    intro ⟨hI_size, linear_indep⟩ 
    apply Matroid.isBase_ncard hI_size.symm A.toMatroid_isBase_X
    rw [StandardRepr.toMatroid_indep_iff_submatrix]
    use hI
    convert linear_indep

private lemma dual_standardrepr_dual_matroid_helper [Fintype α] [Field R] (A B : StandardRepr α R) (I : Set α)
  (same_types : A.X = B.Y ∧ A.Y = B.X)
  (hI: I ⊆ (A.X ∪ A.Y)) (hSize : I.ncard = A.X.ncard):
    let E := (A.X ∪ A.Y)
    let J := E \ I
    let M : Matrix A.X E R := A.toFull
    let N : Matrix A.Y E R := by dsimp [E]; rw [same_types.1, same_types.2, Set.union_comm]; exact B.toFull
    let Msmall : Matrix A.X I R := 
      M.submatrix id (fun j => ⟨j.val, hI j.property⟩)
    let Nsmall : Matrix A.Y J.Elem R :=
      N.submatrix id (fun j => ⟨j.val, j.property.1⟩ )
    M * Nᵀ = 0 → LinearIndependent R Msmallᵀ → LinearIndependent R Nsmallᵀ
    := by
      intro E J M N Msmall Nsmall h_ort h_I
      by_contra h_J
      sorry
private lemma StandardDualOrto [Fintype α](A : StandardRepr α R) :
    have same_types : A.X = A.dual.Y ∧ A.Y = A.dual.X := by simp[StandardRepr.dual]
    let E := (A.X ∪ A.Y)
    let M : Matrix A.X E R := A.toFull
    let N : Matrix A.Y E R := by dsimp [E]; rw [same_types.1, same_types.2, Set.union_comm]; exact A.dual.toFull
    M * Nᵀ = 0 := by
      intro same_types E M N
      have h1 : A.X = A✶.Y := same_types.left
      have h2 : A.Y = A✶.X := same_types.right
      unfold M N same_types E StandardRepr.toFull StandardRepr.dual
      dsimp
      ext i j
      simp only [Matrix.zero_apply, Matrix.mul_apply, Matrix.transpose_apply]
      dsimp [Matrix.fromCols]
      dsimp [Matrix]
      rw [← Equiv.sum_comp]
      sorry


--- LinearIndependent R (N.submatrix id (fun j => ⟨j.val, j.property.1⟩ ))ᵀ
lemma StandardRepr.dual_toMatroid_dual [Fintype α](A : StandardRepr α R) :
  A.toMatroid = A.dual.toMatroid.dual := by 
    rw [Matroid.ext_iff_isBase]
    have same_E : A.toMatroid.E = A.dual.toMatroid.dual.E := by simp [StandardRepr.dual, Set.union_comm]
    have same_E2 : A.toMatroid.E = A.dual.toMatroid.E := by simp [StandardRepr.dual, Set.union_comm]
    constructor
    · exact same_E
    · intro I hI
      rw [Matroid.dual_isBase_iff']
      rw [same_E, Matroid.dual_ground] at hI
      simp only [hI, and_true] 
      have {I : Set α}(A : StandardRepr α R) (hI : I ⊆ A.dual.toMatroid.E) : A.toMatroid.IsBase I → A.dual.toMatroid.IsBase (A.dual.toMatroid.E \ I) := by
        have same_E : A.toMatroid.E = A.dual.toMatroid.dual.E := by simp [StandardRepr.dual, Set.union_comm]
        have same_E2 : A.toMatroid.E = A.dual.toMatroid.E := by simp [StandardRepr.dual, Set.union_comm]
        intro hI_base
        have hI_size : I.ncard = A.X.ncard := by
          have := (A.toMatroid.isBase_exchange).encard_isBase_eq hI_base A.toMatroid_isBase_X 
          apply_fun ENat.toNat at this
          change I.ncard = A.X.ncard at this
          exact this

        rw [StandardRepr.toMatroid.isBase_iff (A := A) (I := I)
          (hI := by rw [<- same_E2] at hI; dsimp at hI; exact hI)] at hI_base
        set J := A.toMatroid.E \ I
        have hJ : J ⊆ A.dual.toMatroid.E := by
          unfold J
          rw [same_E2]
          exact Set.diff_subset
        rw [<- same_E2, StandardRepr.toMatroid.isBase_iff (A := A.dual) (hI := hJ)]
        constructor
        · have : A.X.ncard + A.Y.ncard = (A.X ∪ A.Y).ncard := by rw [Set.ncard_union_eq A.hXY]
          dsimp [J, StandardRepr.dual]
          rw [Set.ncard_diff]
          simp [<-this, hI_size]
          rw [<- same_E2] at hI
          simp at hI
          exact hI
        · have := dual_standardrepr_dual_matroid_helper (A:=A) (B:=A.dual) (I:=I) hI_size
            (same_types := by simp [StandardRepr.dual])
            (hI := by rw [<- same_E2] at hI; dsimp at hI; exact hI) (StandardDualOrto A)
          set M := A.dual.toFull
          set N := A.toFull
          have t := this hI_base.2
          clear hI_base this N 
          simp at t
          simp only [J, A.toMatroid_E]
          have h : A.dual.X = A.Y := by dsimp [StandardRepr.dual]
          convert t using 1
          simp
          ext r c
          simp only [Matrix.submatrix_apply, Matrix.transpose_apply, id]
          revert M
          congr! with M t
          generalize_proofs h_eq h_1 h_2
          have h_set : A✶.Y ∪ A✶.X = A✶.X ∪ A✶.Y := Set.union_comm A✶.Y A✶.X
          have h_heq : HEq (M c (Subtype.mk (↑r) h_eq)) (cast h_1 M c (Subtype.mk (↑r) h_2)) := by 
            simp [h_set]
            generalize hS : A✶.Y ∪ A✶.X = S2 at h_1 h_2 h_set ⊢
            subst h_set
            rw [cast_eq]
          exact eq_of_heq h_heq
      constructor
      · have := this A hI
        exact this
      · set J := A.toMatroid.E \ I
        set hJ : J ⊆ A.toMatroid.E := by 
          unfold J
          exact Set.diff_subset
        have := this A.dual hJ
        simp [StandardRepr.dual_dual, J, hI] at this
        convert_to A✶.toMatroid.IsBase ((A.X ∪ A.Y) \ I) → A.toMatroid.IsBase ((A.X ∪ A.Y) ∩ I)
        · rw [<-same_E2]
          simp
        · rw [<-same_E2] at hI
          dsimp at hI
          rw [Set.inter_eq_right.mpr hI]
        · exact this



     /- 
lemma StandardRepr.dual_vector_matroid_via_orthogonal_complement [Fintype α][Field R] (A B : StandardRepr α R)
    (same_types : A.toMatroid.E = B.toMatroid.E)(h :rowSpace B = same_types ▸ algebraicOrtho (rowSpace A)):
    A.toMatroid.dual = B.toMatroid := by 
        rw [IndepMatroid.matroid_IsBase]
        have same_types2: A.X ∪ A.Y = B.X ∪ B.Y := by
          simp at same_types
          exact same_types
        have (F : Set α)(hF : F ⊆ A.X ∪ A.Y) : A.toMatroid.Indep F ↔ B.toMatroid.Indep (B.toMatroid.E \ F) := by
          have : F ⊆ ↑B.toMatroid.E := by
            simp at same_types
            rw [same_types] at hF
            exact hF
          rw [<-not_iff_not]
          constructor
          · intro h_indep
            rw [StandardRepr.toMatroid_indep_iff_submatrix] at h_indep
            push_neg at h_indep
            obtain h_dep := h_indep hF
            have := by
              rw [Fintype.not_linearIndependent_iff] at h_dep
              exact h_dep
            rw [not_linearIndependent_iff] at h_dep
            clear h_indep
            rw [StandardRepr.toMatroid_indep_iff_elem] 
            push_neg
            intro hI
            rw [not_linearIndependent_iff]
            obtain ⟨s, g, ⟨h_dep, h_nonzero⟩ ⟩ := h_dep
            have : extendFunction g ∈ rowSpace B := by
              simp [h]
              rw [mem_cast_algebraicOrtho same_types]
              intro u hu
              unfold rowSpace StandardRepr.toFull at hu
              unfold extendFunction
              simp
              sorry
            have := by
              dsimp [rowSpace] at this
              rw [Finsupp.mem_span_range_iff_exists_finsupp] at this
              exact this

            obtain ⟨c, hc⟩ := this


            use Finset.univ
            use extendFunction c

            sorry

              --change ∀ u ∈ rowSpace A, ∑ i, u i * extendFunction g i = 0

              --sorry
          
            let v : (A.X ∪ A.Y).Elem → R := fun i => if hi : i.val ∈ F then c ⟨i.val, hi⟩ else 0

          sorry
        sorry




theorem StandardRepr.dual_matroid_is_matroid_dual [DivisionRing R](S: StandardRepr α R):
    S.dual.toMatroid = S.toMatroid.dual := by

      sorry

-/
