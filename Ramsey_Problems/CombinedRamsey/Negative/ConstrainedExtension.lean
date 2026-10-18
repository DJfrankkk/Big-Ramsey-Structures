import CombinedRamsey.Negative.EncodingGenericRules
import CombinedRamsey.Negative.EncodingRealizations
import RelationalRamsey632.Existence.FiniteExtension
import RelationalRamsey632.Existence.Homogeneity
import CombinedRamsey.Negative.PersistenceTypes

/-! All finite extensions and back-and-forth use the constrained EP only. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632 RelationalRamsey632.Existence

variable {X : Type}

theorem constrained_extend_one_point {V : Type} [Finite V]
    (K : RelStructure language X)
    (hEP : ConstrainedGeneric.ExtensionProperty language LegalModel K)
    (B : RelStructure language (V ⊕ Unit)) (hB : LegalModel B)
    (f : RelEmbedding (B.pullback Sum.inl) K) :
    ∃ g : RelEmbedding B K, ∀ v : V, g (Sum.inl v) = f v := by
  classical
  letI := Fintype.ofFinite V
  let phi := onePointEquiv V
  let Bfin := B.pullback phi
  let old : RelEmbedding (Bfin.pullback Fin.castSucc) K := {
    toFun := fun i => f ((Fintype.equivFin V).symm i)
    injective := f.injective.comp (Fintype.equivFin V).symm.injective
    map_rel := fun R t => by
      have hp : phi ∘ Fin.castSucc ∘ t = Sum.inl ∘ (Fintype.equivFin V).symm ∘ t := by
        funext i
        simpa only [Equiv.apply_symm_apply, Function.comp_def] using
          onePointEquiv_old V ((Fintype.equivFin V).symm (t i))
      change B.rel R (phi ∘ Fin.castSucc ∘ t) ↔ _
      rw [hp]
      exact f.map_rel R ((Fintype.equivFin V).symm ∘ t) }
  obtain ⟨gfin,hg⟩ := hEP (Fintype.card V) Bfin
    (legalModel_hereditary B hB phi phi.injective) old
  let intoFin : RelEmbedding B Bfin := {
    toFun := phi.symm
    injective := phi.symm.injective
    map_rel := fun R t => by
      change B.rel R t ↔ B.rel R (phi ∘ phi.symm ∘ t)
      simp [Function.comp_def] }
  refine ⟨gfin.comp intoFin, ?_⟩
  intro v
  have hidx : phi.symm (.inl v) = (Fintype.equivFin V v).castSucc := by
    apply phi.injective
    rw [phi.apply_symm_apply]
    exact (onePointEquiv_old V v).symm
  change gfin (phi.symm (.inl v)) = f v
  rw [hidx,hg]
  exact congrArg f ((Fintype.equivFin V).symm_apply_apply v)

def finLastEquiv (m : ℕ) : (Fin m ⊕ Unit) ≃ Fin (m+1) :=
  (Equiv.sumCongr (Equiv.refl (Fin m)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv

theorem finLastEquiv_old (m : ℕ) (i : Fin m) : finLastEquiv m (.inl i) = i.castSucc := by
  simp [finLastEquiv]
  apply Fin.ext
  rfl

def sumLastEquiv (V : Type) (m : ℕ) : ((V ⊕ Fin m) ⊕ Unit) ≃ (V ⊕ Fin (m+1)) :=
  (Equiv.sumAssoc V (Fin m) Unit).trans (Equiv.sumCongr (Equiv.refl V) (finLastEquiv m))

theorem sumLastEquiv_old (V : Type) (m : ℕ) (x : V ⊕ Fin m) :
    sumLastEquiv V m (.inl x) = Sum.map id Fin.castSucc x := by
  cases x <;> simp [sumLastEquiv, finLastEquiv_old]

theorem constrained_extend_fin {V : Type} [Finite V]
    (K : RelStructure language X)
    (hEP : ConstrainedGeneric.ExtensionProperty language LegalModel K) (m : ℕ)
    (D : RelStructure language (V ⊕ Fin m)) (hD : LegalModel D)
    (f : RelEmbedding (D.pullback Sum.inl) K) :
    ∃ g : RelEmbedding D K, ∀ v, g (.inl v) = f v := by
  classical
  induction m with
  | zero =>
    let proj : V ⊕ Fin 0 → V := Sum.elim id Fin.elim0
    have hp : ∀ x : V ⊕ Fin 0, Sum.inl (proj x) = x := by
      intro x; cases x with
      | inl x => rfl
      | inr x => exact Fin.elim0 x
    let e : RelEmbedding D (D.pullback Sum.inl) := {
      toFun := proj
      injective := fun x y h => (hp x).symm.trans ((congrArg Sum.inl h).trans (hp y))
      map_rel := fun R t => by
        change D.rel R t ↔ D.rel R (Sum.inl ∘ proj ∘ t)
        have he : Sum.inl ∘ proj ∘ t = t := funext (fun i => hp (t i))
        rw [he] }
    exact ⟨f.comp e, fun _ => rfl⟩
  | succ m ih =>
    let j : V ⊕ Fin m → V ⊕ Fin (m+1) := Sum.map id Fin.castSucc
    have hj : Function.Injective j := Sum.map_injective.mpr ⟨Function.injective_id, Fin.castSucc_injective m⟩
    let Dold := D.pullback j
    obtain ⟨gold,hold⟩ := ih Dold (legalModel_hereditary D hD j hj) f
    let phi := sumLastEquiv V m
    let B := D.pullback phi
    have hred : B.pullback Sum.inl = Dold := by
      apply RelStructure.ext_rel
      intro r R t
      have he : phi ∘ Sum.inl ∘ t = j ∘ t := funext (fun i => sumLastEquiv_old V m (t i))
      change D.rel R (phi ∘ Sum.inl ∘ t) ↔ D.rel R (j ∘ t)
      rw [he]
    let old : RelEmbedding (B.pullback Sum.inl) K := {
      toFun := gold
      injective := gold.injective
      map_rel := fun R t => (Iff.of_eq (congrArg (fun A => A.rel R t) hred)).trans
        (gold.map_rel R t) }
    obtain ⟨g,hg⟩ := constrained_extend_one_point K hEP B
      (legalModel_hereditary D hD phi phi.injective) old
    let into : RelEmbedding D B := {
      toFun := phi.symm
      injective := phi.symm.injective
      map_rel := fun R t => by
        change D.rel R t ↔ D.rel R (phi ∘ phi.symm ∘ t)
        simp [Function.comp_def] }
    refine ⟨g.comp into, ?_⟩
    intro v
    have hidx : phi.symm (.inl v) = .inl (.inl v) := by
      apply phi.injective
      simp [phi, sumLastEquiv]
    change g (phi.symm (.inl v)) = f v
    rw [hidx,hg]
    exact hold v

theorem constrained_rel_finite_extension (K : RelStructure language X)
    (hEP : ConstrainedGeneric.ExtensionProperty language LegalModel K) : RelFiniteExtension K := by
  classical
  intro V W _ _ D hDi hDl f
  letI := Fintype.ofFinite W
  let e := (Fintype.equivFin W).symm
  let phi : V ⊕ Fin (Fintype.card W) ≃ V ⊕ W := Equiv.sumCongr (Equiv.refl V) e
  let Dfin := D.pullback phi
  obtain ⟨gfin,hg⟩ := constrained_extend_fin K hEP (Fintype.card W) Dfin
    (legalModel_hereditary D ⟨hDi,hDl⟩ phi phi.injective) f
  let into : RelEmbedding D Dfin := {
    toFun := phi.symm
    injective := phi.symm.injective
    map_rel := fun R t => by
      change D.rel R t ↔ D.rel R (phi ∘ phi.symm ∘ t)
      simp [Function.comp_def] }
  exact ⟨gfin.comp into, hg⟩

open scoped FirstOrder

theorem constrained_extension_pair (K : RelStructure language X) (hK : LegalModel K)
    (hEP : ConstrainedGeneric.ExtensionProperty language LegalModel K) :
    @FirstOrder.Language.IsExtensionPair language.toFirstOrder X X K.toFirstOrder K.toFirstOrder := by
  classical
  letI := K.toFirstOrder
  intro f x
  by_cases hx : x ∈ f.val.dom
  · exact ⟨f,hx,le_refl f⟩
  · haveI : Finite f.val.dom := f.property.finite
    let F : Set X := f.val.dom
    let B := K.pullback (insertMap F x)
    letI := B.toFirstOrder
    let old : RelEmbedding (B.pullback Sum.inl) K := {
      toFun := f.val.toEmbedding
      injective := f.val.toEmbedding.injective
      map_rel := fun R t => (f.val.toEmbedding.map_rel' R t).symm }
    obtain ⟨g,hg⟩ := constrained_extend_one_point K hEP B
      (legalModel_hereditary K hK (insertMap F x) (insertMap_injective F x hx)) old
    let s := RelEmbedding.pullback K (insertMap F x) (insertMap_injective F x hx)
    let sf := s.toFirstOrder
    let gf := g.toFirstOrder
    let p : FirstOrder.Language.PartialEquiv language.toFirstOrder X X := {
      dom := sf.toHom.range
      cod := gf.toHom.range
      toEquiv := gf.equivRange.comp sf.equivRange.symm }
    haveI : Finite p.dom := Finite.of_equiv (F ⊕ Unit) sf.equivRange.toEquiv
    have hFG : p.dom.FG := FirstOrder.Language.Substructure.FG.of_finite
    refine ⟨⟨p,hFG⟩,?_,?_⟩
    · exact ⟨Sum.inr (),rfl⟩
    · change f.val ≤ p
      have hle : f.val.dom ≤ p.dom := fun y hy => ⟨Sum.inl ⟨y,hy⟩,rfl⟩
      refine ⟨hle,?_⟩
      ext y
      change ((gf.equivRange.comp sf.equivRange.symm)
        (FirstOrder.Language.Substructure.inclusion hle y)).val = f.val.toEmbedding y
      have hidx : sf.equivRange.symm (FirstOrder.Language.Substructure.inclusion hle y) = .inl y := by
        apply sf.equivRange.injective
        rw [sf.equivRange.apply_symm_apply]
        apply Subtype.ext
        rfl
      change gf (sf.equivRange.symm (FirstOrder.Language.Substructure.inclusion hle y)) = _
      rw [hidx]
      exact hg y

theorem constrained_ultrahomogeneous [Countable X] (K : RelStructure language X)
    (hK : LegalModel K) (hEP : ConstrainedGeneric.ExtensionProperty language LegalModel K) :
    @FirstOrder.Language.IsUltrahomogeneous language.toFirstOrder X K.toFirstOrder := by
  letI := K.toFirstOrder
  exact (FirstOrder.Language.isUltrahomogeneous_iff_IsExtensionPair
    (FirstOrder.Language.Structure.cg_of_countable)).mpr (constrained_extension_pair K hK hEP)

theorem constrained_finite_homogeneous [Countable X] (K : RelStructure language X)
    (hK : LegalModel K) (hEP : ConstrainedGeneric.ExtensionProperty language LegalModel K) :
    FiniteEmbeddingHomogeneous K :=
  finiteEmbeddingHomogeneous_of_ultrahomogeneous K (constrained_ultrahomogeneous K hK hEP)

theorem constrained_age_exact {V : Type} [Finite V] (K : RelStructure language X)
    (hK : LegalModel K) (hEP : ConstrainedGeneric.ExtensionProperty language LegalModel K)
    (A : RelStructure language V) : Nonempty (RelEmbedding A K) ↔ LegalModel A := by
  constructor
  · rintro ⟨e⟩
    have h := legalModel_hereditary K hK e e.injective
    rwa [e.pullback_eq] at h
  · intro hA
    let phi : Empty ⊕ V ≃ V := {
      toFun := Sum.elim Empty.elim id
      invFun := Sum.inr
      left_inv := fun x => by cases x with
        | inl x => exact x.elim
        | inr x => rfl
      right_inv := fun _ => rfl }
    let D := A.pullback phi
    have hD := legalModel_hereditary A hA phi phi.injective
    let f : RelEmbedding (D.pullback Sum.inl) K := {
      toFun := Empty.elim
      injective := fun x => x.elim
      map_rel := fun R t => by cases R <;> exact (t 0).elim }
    obtain ⟨g,_⟩ := constrained_rel_finite_extension K hEP Empty V D hD.1 hD.2 f
    let into : RelEmbedding A D := {
      toFun := Sum.inr
      injective := Sum.inr_injective
      map_rel := fun _ _ => Iff.rfl }
    exact ⟨g.comp into⟩

end CombinedRamsey.Negative
