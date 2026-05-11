import Seymour.Matroid.Duality

open scoped Matrix
open Classical

section nove_pridane

private lemma l1_aux {α β γ : Type} (X Y Z : Set α) (hZ : Y ∪ X = Z) (z : Z.Elem) (f : β → (Y ∪ X).Elem → γ) (j : β) :
    (hZ ▸ f) j z = (hZ ▸ f j) z := by
  subst hZ
  rfl

private lemma l1 {α β : Type} [DecidableEq α] (X Y : Set α) (i : X.Elem) (j : Y.Elem) (A : Y.Elem → Y.Elem → β) (B : Y.Elem → X.Elem → β) :
    ((Set.union_comm X Y).symm ▸
      fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j ⟨i.val, Set.subset_union_left i.property⟩ =
    ((Set.union_comm X Y).symm ▸ (
      fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j) ⟨i.val, Set.subset_union_left i.property⟩ := by
  apply l1_aux

private lemma l2_aux {α β : Type} (X Y Z : Set α) (hZ : Y ∪ X = Z) (z : Z.Elem) (f : (Y ∪ X).Elem → β) :
    (hZ ▸ f) z = f (hZ ▸ z) := by
  subst hZ
  rfl

private lemma l2 {α β : Type} [DecidableEq α] (X Y : Set α) (i : X.Elem) (j : Y.Elem) (A : Y.Elem → Y.Elem → β) (B : Y.Elem → X.Elem → β) :
    ((Set.union_comm X Y).symm ▸ (
      fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j) ⟨i.val, Set.subset_union_left i.property⟩ =
    ((fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j) ((Set.union_comm X Y).symm ▸ ⟨i.val, Set.subset_union_left i.property⟩) := by
  apply l2_aux

private lemma ll {α β : Type} [DecidableEq α] (X Y : Set α) (i : X.Elem) (j : Y.Elem) (A : Matrix Y.Elem Y.Elem β) (B : Matrix Y.Elem X.Elem β) :
    ((Set.union_comm X Y).symm ▸
      fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j ⟨i.val, Set.subset_union_left i.property⟩ =
    (fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j ⟨i.val, Set.subset_union_right i.property⟩ := by
  rw [l1, l2]
  congr
  ext
  apply Subtype.subst_elem

-- TODO and move to `Matrix/Basic` and rename!
lemma lll {α β : Type} [DecidableEq α] [CommSemiring β] {x : α} [Fintype α]
    (f : α → β) :
    ∑ i : α, (1 : Matrix α α β) x i * f i = f x := by
  convert fintype_sum_of_single_nonzero (fun i : α => (1 : Matrix α α β) x i * f i) x (by
    intro i hix
    convert zero_mul _
    exact Matrix.one_apply_ne' hix
  )
  simp

end nove_pridane

variable {α R : Type} [DecidableEq α] [Field R]

def rowSpace {R: Type} [DivisionRing R] (S : StandardRepr α R) : Submodule R (↑S.toMatroid.E → R) :=
    Submodule.span R (Set.range S.toFull)

def colSpace {R: Type} [DivisionRing R] (S : StandardRepr α R) : Submodule R (↑S.X → R) :=
    Submodule.span R (Set.range S.toFullᵀ)

noncomputable def extendFunction {A B : Set α} [Field R](f : A → R): B → R :=
  fun x =>
    if h : (x : α) ∈ A then
      f ⟨(x : α), h⟩
    else
      0


lemma Matroid.isBase_ncard {M : Matroid α} (hM : M.RankFinite) {I J : Set α} (h_size : I.ncard = J.ncard) (hI : M.IsBase I) (hJ : M.Indep J) :
    M.IsBase J := by
      rw [Matroid.isBase_iff_maximal_indep]
      simp [Maximal, hJ]
      intro y hY hJ_y
      obtain ⟨B, ⟨hB_base, hB_subset⟩⟩ := hY.exists_isBase_superset
      obtain ⟨finite_base, h_finite_base⟩  := hM.exists_finite_isBase
      have hB_is_finite := h_finite_base.1.finite_of_finite h_finite_base.2 hB_base
      have hy_is_finite := hB_is_finite.subset hB_subset
      have : y.ncard ≤ J.ncard := by
        have : B.ncard = J.ncard := by
          rw [← h_size]
          have x := (Matroid.isBase_exchange M).encard_isBase_eq hB_base hI
          apply_fun ENat.toNat at x
          change B.ncard = I.ncard at x
          exact x
        rw [←this]
        have := Set.encard_le_encard hB_subset
        exact Set.ncard_le_ncard hB_subset hB_is_finite

      exact (Set.eq_of_subset_of_ncard_le hJ_y this hy_is_finite).symm.subset






set_option pp.proofs true
lemma StandardRepr.toMatroid.isBase_iff {A : StandardRepr α R} [Fintype A.X] [Fintype A.Y] {I : Set α} (hI : I ⊆ (A.X ∪ A.Y)):
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
    apply Matroid.isBase_ncard (A.toMatroid_rankFinite_of_finite_X) hI_size.symm A.toMatroid_isBase_X
    rw [StandardRepr.toMatroid_indep_iff_submatrix]
    use hI
    convert linear_indep

lemma Matrix.almost_square_transpose_LinearIndependent {A B : Set α}[Fintype A] [Fintype B](N : Matrix A B R) (h_card : #A = #B) : LinearIndependent R N → LinearIndependent R Nᵀ := by
  intro hN_rows
  rw [linearIndependent_iff_card_eq_finrank_span] at hN_rows
  rw [linearIndependent_iff_card_eq_finrank_span, <- h_card, hN_rows]
  have {U V : Set α}[Fintype U][Fintype V](M : Matrix U V R): Set.finrank R (Set.range M) = M.rank := by
    rw [Matrix.rank_eq_finrank_span_row M]
    rfl
  repeat rw [this]
  exact (Matrix.rank_transpose N).symm


private lemma dual_standardrepr_dual_matroid_helper  [Field R] (A B : StandardRepr α R) [Fintype A.X][Fintype A.Y][Fintype B.X][Fintype B.Y](I : Set α)[Fintype I]
    (hXY : A.X = B.Y) (hYX : A.Y = B.X) (hI : I ⊆ (A.X ∪ A.Y)) (hSize : I.ncard = A.X.ncard) :
    let M : Matrix A.X (A.X ∪ A.Y).Elem R := A.toFull
    let N : Matrix A.Y (A.X ∪ A.Y).Elem R := hXY ▸ hYX ▸ Set.union_comm B.Y B.X ▸ B.toFull
    M * Nᵀ = 0 →
    let M' : Matrix A.X I R := M.submatrix id hI.elem
    let N' : Matrix A.Y ((A.X ∪ A.Y) \ I).Elem R := N.submatrix id Set.diff_subset.elem
    LinearIndependent R M'ᵀ → LinearIndependent R N'ᵀ
    := by
  intro M N h0 M' N' hM'
  by_contra hN'
  let U := (A.X ∪ A.Y).Elem
  let p := fun (x : U) => x.val ∈ I

  have : ¬ LinearIndependent R N' := by
    intro hN_rows
    apply hN'
    have : #(A.Y) = #↑((A.X ∪ A.Y) \ I) := by
      repeat rw [Fintype.card_eq_nat_card]
      convert_to A.Y.ncard = ((A.X ∪ A.Y) \ I).ncard
      rw [Set.ncard_diff hI, Set.ncard_union_eq A.hXY]
      simp [hSize]
    apply Matrix.almost_square_transpose_LinearIndependent N' 
    convert this
    exact hN_rows

  have hN'2 : ∃ (e: A.Y → R), N'ᵀ *ᵥ e = 0 ∧ e ≠ 0 := by
    obtain ⟨e, h_sum, h_nz⟩ := Fintype.not_linearIndependent_iff.mp this
    use e
    constructor
    · ext i
      have h_sum_i := congr_fun h_sum i
      rw [<-h_sum_i]
      unfold Matrix.mulVec dotProduct
      simp [mul_comm]
    · simp [h_nz]
      intro h
      obtain ⟨i, hi⟩ := h_nz
      exact hi (congr_fun h i)

  have hM'_isFull (e : I → R) : M' *ᵥ e = 0 → e = 0 := by 
    intro h_mul
    ext i
    apply Fintype.linearIndependent_iff.mp hM' e
    unfold Matrix.mulVec dotProduct at h_mul
    simp at h_mul
    rw [<- h_mul]
    ext x
    simp [mul_comm]

  have : LinearIndependent R N := by
    apply Fintype.linearIndependent_iff.mpr 
    intro g hg j
    rw [funext_iff] at hg
    have := hg ⟨j, Set.subset_union_right j.2⟩
    unfold N StandardRepr.toFull at this
    simp [Matrix.fromCols_apply_inl] at this
    have : ∑ x : A.Y, g x * (1 : Matrix A.Y A.Y R) x j = 0 := by
      rw [<- this]
      apply Fintype.sum_congr
      intro i
      congr 1
      simp [Matrix.fromCols, Subtype.toSum]
      clear this hg g hM'_isFull hN'2 p U hN' hM' M' h0 
      clear this N' N M hSize hI
      /-convert_to 1 i j =
    (Eq.symm hXY ▸
        Eq.symm hYX ▸ Eq.symm (Set.union_comm B.Y B.X) ▸ fun x => Matrix.of (fun i => 1 i ⊕ᵥ B.B i) x ∘ Subtype.toSum)
      i (Subtype.mk (↑j) (Set.subset_union_right j.property)) ↔-/



      /-obtain ⟨AX, AY, A_repr⟩ := A
      obtain ⟨BX, BY, B_repr⟩ := B
      dsimp only at hXY hYX ⊢
      subst_vars
      have h_comm : BX ∪ BY = BY ∪ BX := Set.union_comm BX BY
      generalize hU : BX ∪ BY = U at h_comm ⊢
      generalize hV : BY ∪ BX = V at h_comm ⊢
      subst h_comm-/

       

      sorry
    simp [Matrix.one_apply] at this
    exact this
    

   /- 
  have : LinearIndependent R N := by 
    unfold N StandardRepr.toFull Matrix.fromCols
    clear hN'2 hM'_isFull this p U hN' hM' N' M' h0 N M hSize 
    cases A
    cases B
    dsimp only at hXY hYX ⊢
    subst_vars
    simp
    generalize hY : B.Y = Y at hXY ⊢
    subst Y
    generalize hX : B.X = X at hYX ⊢
    subst X
    apply LinearIndependent.of_comp (LinearMap.funLeft R R Sum.inl)-/
    

  have hN_isFull (e : A.Y → R) :  Nᵀ *ᵥ e = 0 → e = 0 := by 
    intro h_mul
    ext i
    apply Fintype.linearIndependent_iff.mp this e
    unfold Matrix.mulVec dotProduct at h_mul
    simp at h_mul
    rw [<- h_mul]
    ext x
    simp [mul_comm]


  let e_I : I ≃ { x : (A.X ∪ A.Y).Elem // p x } := {
    toFun := fun x => ⟨⟨x.val, hI x.prop⟩, x.prop⟩
    invFun := fun x => ⟨x.val.val, x.prop⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext rfl
  }
  obtain ⟨e, he1⟩ := hN'2
  let v := Nᵀ *ᵥ e
  have he2 := hN_isFull e
  let v' : I → R := fun j => v ⟨j.val, hI j.prop⟩
  have he3 := hM'_isFull v'
  have he4 : M *ᵥ v = 0 := by -- from h0 and v
    unfold v
    rw [Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]
  have hi : ∀ i : {x : U // ¬ p x}, v i = 0 := by -- from he1.1, N' and v
    intro i
    have := he1.1
    unfold v
    unfold N' at this
    let i_cast : ↑((A.X ∪ A.Y) \ I) := ⟨i.val.val, ⟨i.val.property, i.property⟩⟩
    have hi := congr_fun this i_cast
    exact hi
  have he6 : M' *ᵥ v' = 0 := by
    ext i 
    have h4_i := congr_fun he4 i
    rw [<- h4_i]
    unfold M'
    unfold Matrix.mulVec Matrix.submatrix dotProduct v'
    simp
    symm
    have : ∑ x : U, M i x * v x = ∑ x : {x : U // p x}, M i x * v x + ∑ x : {x : U // ¬ p x}, M i x * v x := by
      classical
      symm
      exact Fintype.sum_subtype_add_sum_subtype (fun x => x.val ∈ I) (fun x => M i x * v x)

    have hh : ∑ x : {x : U // ¬ p x}, M i x * v x = 0 := by
      simp [p, hi]
    simp [hh] at this
    rw [this]
    symm
    exact Equiv.sum_comp e_I (fun x => M i x * v x)

  have v'_is_zero : v' = 0 := he3 he6
  clear he3 he6 
  have v_is_zero : v = 0 := by
    ext i
    by_cases h : p i
    · have h_in := congr_fun v'_is_zero ⟨i.val, h⟩
      exact h_in
    · exact hi ⟨i, h⟩
  exact he1.2 (he2 v_is_zero)
    





  

private lemma StandardDualOrto  (S : StandardRepr α R) [Fintype S.X][Fintype S.Y]:
    S.toFull * (Set.union_comm S.X S.Y ▸ S.dual.toFull)ᵀ = 0 := by
  unfold StandardRepr.toFull StandardRepr.dual
  dsimp only
  ext i j
  simp only [Matrix.zero_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.fromCols]
  rw [←S.hXY.equivSumUnion.sum_comp, Fintype.sum_sum_type]
  conv_lhs => congr; simp; rw [lll]
  show ((Set.union_comm S.X S.Y).symm ▸
    fun x : S.Y.Elem => (fun i : S.Y.Elem => Sum.elim ((1 : Matrix S.Y.Elem S.Y.Elem R) i) ((-S.Bᵀ) i)) x ∘ Subtype.toSum) j ⟨i.val, _⟩
    + _ = (0 : R)
  have hh :
      ((Set.union_comm S.X S.Y).symm ▸
        fun x : S.Y.Elem => (fun i : S.Y.Elem => Sum.elim ((1 : Matrix S.Y.Elem S.Y.Elem R) i) ((-S.Bᵀ) i)) x ∘ Subtype.toSum) j ⟨i.val, Set.subset_union_left i.property⟩ =
       (fun x : S.Y.Elem => (fun i : S.Y.Elem => Sum.elim ((1 : Matrix S.Y.Elem S.Y.Elem R) i) ((-S.Bᵀ) i)) x ∘ Subtype.toSum) j ⟨i.val, Set.subset_union_right i.property⟩
  · convert ll S.X S.Y i j 1 (-S.Bᵀ)
  rw [hh]
  have hiY : i.val ∉ S.Y
  · exact S.hXY.ni_right_of_in_left i.property
  simp [Subtype.toSum, hiY]

  -- first part done

  conv => 
    lhs
    rhs
    rhs
    ext x
    lhs
    rw [dif_neg]
    · simp
    · exact Set.disjoint_left.mp S.hXY.symm x.property
  show   -S.B i j +
      ∑ y,
        S.B i y *
          ((Set.union_comm S.X S.Y).symm ▸
            fun x : S.Y.Elem => (fun i : S.Y.Elem => Sum.elim ((1 : Matrix S.Y.Elem S.Y.Elem R) i) ((-S.Bᵀ) i)) x ∘ Subtype.toSum) j
            (Subtype.mk (↑y) (Set.subset_union_right y.property)) = 0
  convert_to -S.B i j +
      ∑ y,
        S.B i y *
          ( (1 : Matrix S.Y.Elem S.Y.Elem R) y j) = 
    0 
  simp
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  generalize hp : Eq.symm (Set.union_comm S.X S.Y) = p

  -- 2. Discard the equality between proofs (this is what caused the failure)
  clear hp

  conv =>
    lhs
    rhs
    rhs
  sorry
  convert_to -S.B i j + S.B i j = 0
  · rw [← Matrix.mul_apply, Matrix.mul_one]
  · simp


    


--- LinearIndependent R (N.submatrix id (fun j => ⟨j.val, j.property.1⟩ ))ᵀ
lemma StandardRepr.dual_toMatroid_dual (A : StandardRepr α R) [Fintype A.X][Fintype A.Y]:
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
      have {I : Set α}(A : StandardRepr α R) (hI : I ⊆ A.dual.toMatroid.E) [Fintype A.X][Fintype A.Y]: A.toMatroid.IsBase I → A.dual.toMatroid.IsBase (A.dual.toMatroid.E \ I) := by
        have same_E : A.toMatroid.E = A.dual.toMatroid.dual.E := by simp [StandardRepr.dual, Set.union_comm]
        have same_E2 : A.toMatroid.E = A.dual.toMatroid.E := by simp [StandardRepr.dual, Set.union_comm]
        intro hI_base
        have hI_size : I.ncard = A.X.ncard :=
          congr_arg ENat.toNat ((A.toMatroid.isBase_exchange).encard_isBase_eq hI_base A.toMatroid_isBase_X)
        rw [StandardRepr.toMatroid.isBase_iff (A := A) (I := I)
          (hI := by rw [← same_E2] at hI; exact hI)] at hI_base
        set J := A.toMatroid.E \ I
        have hJ : J ⊆ A.dual.toMatroid.E := by
          unfold J
          rw [same_E2]
          exact Set.diff_subset
        have : Fintype A.dual.X := by
          dsimp [StandardRepr.dual]
          assumption
        have : Fintype A.dual.Y := by
          dsimp [StandardRepr.dual]
          assumption
        rw [← same_E2, StandardRepr.toMatroid.isBase_iff (A := A.dual) (hI := hJ)]
        constructor
        · have : A.X.ncard + A.Y.ncard = (A.X ∪ A.Y).ncard := by rw [Set.ncard_union_eq A.hXY]
          dsimp [J, StandardRepr.dual] at hI ⊢
          rw [Set.union_comm] at hI
          have h_union_fin : (A.X ∪ A.Y).Finite := (Set.toFinite A.X).union (Set.toFinite A.Y)
          have h_I_fin : Fintype ↑I := (Set.Finite.subset h_union_fin hI).fintype
          convert_to (A.X ∪ A.Y).ncard - I.ncard = A.Y.ncard
          · rw [Set.ncard_diff]
            exact hI
          · omega

        · 
          have : Fintype I := by 
            dsimp [J, StandardRepr.dual] at hI
            rw [Set.union_comm] at hI
            have h_union_fin : (A.X ∪ A.Y).Finite := (Set.toFinite A.X).union (Set.toFinite A.Y)
            exact (Set.Finite.subset h_union_fin hI).fintype
          have := dual_standardrepr_dual_matroid_helper A A.dual I rfl rfl (subset_of_subset_of_eq hI same_E.symm) hI_size (StandardDualOrto A)
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
          apply eq_of_heq

          have elim_cast (U: Set _)(heq : A.dual.X ∪ A.dual.Y = U)(elem_r : U) : elem_r.val = ↑r → HEq (M c (Subtype.mk (↑r) h_eq)) ((heq ▸ M) c elem_r) := by
            intro h_val
            subst heq
            apply heq_of_eq
            congr 1
            apply Subtype.ext
            exact h_val.symm
          apply elim_cast (A✶.Y ∪ A✶.X) h_1 (h_2.elem r)
          rfl
      constructor
      · have := this A hI
        exact this
      · set J := A.toMatroid.E \ I
        set hJ : J ⊆ A.toMatroid.E := by
          unfold J
          exact Set.diff_subset
        have xx : Fintype A.dual.X := by
          dsimp [StandardRepr.dual]
          assumption
        have xx : Fintype A.dual.Y := by
          dsimp [StandardRepr.dual]
          assumption
        have := this A.dual hJ
        simp [StandardRepr.dual_dual, J, hI] at this
        convert_to A✶.toMatroid.IsBase ((A.X ∪ A.Y) \ I) → A.toMatroid.IsBase ((A.X ∪ A.Y) ∩ I)
        · rw [←same_E2]
          simp
        · rw [←same_E2] at hI
          dsimp at hI
          rw [Set.inter_eq_right.mpr hI]
        · exact this



