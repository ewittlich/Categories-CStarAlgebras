import Mathlib

noncomputable section

open CategoryTheory

/-- The type of C⋆-algebras with ⋆-algebra morphisms. -/
structure CStarAlg :=
  (carrier : Type u)
  [nonUnitalNormedRing : NonUnitalNormedRing carrier]
  [starRing : StarRing carrier]
  [cstarRing : CStarRing carrier]
  [normedSpace : NormedSpace ℂ carrier]
  [isScalarTower : IsScalarTower ℂ carrier carrier]
  [smulCommClass : SMulCommClass ℂ carrier carrier]
  [starModule : StarModule ℂ carrier]
  [completeSpace : CompleteSpace carrier]

/-- The type of unital C⋆-algebras with unital ⋆-algebra morphisms. -/
structure CStarAlg₁ :=
  (carrier : Type u)
  [normedRing : NormedRing carrier]
  [starRing : StarRing carrier]
  [cstarRing : CStarRing carrier]
  [normedAlgebra : NormedAlgebra ℂ carrier]
  [starModule : StarModule ℂ carrier]
  [completeSpace : CompleteSpace carrier]

/- The type of commutative unital C⋆-algebras with unital ⋆-algebra morphisms. -/
--def CommCStarAlg₁ := FullSubcategory (fun A : CStarAlg₁ ↦ ∀ x y : A.carrier, x * y = y * x)
  ---(carrier : Type u)
  ---[normedCommRing : NormedCommRing carrier]
  ---[starRing : StarRing carrier]
  ---[cstarRing : CStarRing carrier]
  ---[normedAlgebra : NormedAlgebra ℂ carrier]
  ---[starModule : StarModule ℂ carrier]
  ---[completeSpace : CompleteSpace carrier]

namespace CStarAlg

noncomputable instance : Inhabited CStarAlg := ⟨⟨ℂ⟩⟩

instance : CoeSort CStarAlg (Type u) := ⟨CStarAlg.carrier⟩

attribute [instance] nonUnitalNormedRing starRing cstarRing normedSpace
  isScalarTower smulCommClass starModule completeSpace

noncomputable instance : Category CStarAlg.{u} :=
{ Hom := fun A B ↦ A →⋆ₙₐ[ℂ] B,
  id := fun A ↦ NonUnitalStarAlgHom.id ℂ A,
  comp := fun f g ↦ g.comp f }

instance instFunLike (X Y : CStarAlg) : FunLike (X ⟶ Y) X Y :=
  inferInstanceAs <| FunLike (X →⋆ₙₐ[ℂ] Y) X Y

instance instNonUnitalAlgHomClass (X Y : CStarAlg) : NonUnitalAlgHomClass (X ⟶ Y) ℂ X Y :=
  inferInstanceAs <| NonUnitalAlgHomClass (X →⋆ₙₐ[ℂ] Y) ℂ X Y

instance instStarHomClass (X Y : CStarAlg) : StarHomClass (X ⟶ Y) X Y :=
  inferInstanceAs <| StarHomClass (X →⋆ₙₐ[ℂ] Y) X Y

noncomputable instance : ConcreteCategory CStarAlg.{u} where
  forget :=
    { obj := fun A ↦ A
      map := fun f ↦ f }
  forget_faithful :=
    { map_injective := fun {X Y} ↦ DFunLike.coe_injective }




/-- Construct a bundled `CStarAlg` from the underlying type and appropriate type classes. -/
def of (A : Type u) [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [ NormedSpace ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] [CompleteSpace A] :
  CStarAlg := ⟨A⟩

@[simp] lemma coe_of (A : Type u) [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
  [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
  [CompleteSpace A] : (of A : Type u) = A := rfl

instance forgetNonUnitalNormedRing (A : CStarAlg) : NonUnitalNormedRing ((forget CStarAlg).obj A) :=
  A.nonUnitalNormedRing

instance forgetStarRing (A : CStarAlg) : StarRing ((forget CStarAlg).obj A) :=
  A.starRing

instance forgetCStarRing (A : CStarAlg) : CStarRing ((forget CStarAlg).obj A) :=
  A.cstarRing

instance forgetNormedSpace (A : CStarAlg) : NormedSpace ℂ ((forget CStarAlg).obj A) :=
  A.normedSpace

instance forgetIsScalarTower (A : CStarAlg) :
    IsScalarTower ℂ ((forget CStarAlg).obj A) ((forget CStarAlg).obj A) :=
  A.isScalarTower

instance forgetSMulCommClass (A : CStarAlg) :
    SMulCommClass ℂ ((forget CStarAlg).obj A) ((forget CStarAlg).obj A) :=
  A.smulCommClass

instance forgetStarModule (A : CStarAlg) : StarModule ℂ ((forget CStarAlg).obj A) :=
  A.starModule

instance forgetCompleteSpace (A : CStarAlg) : CompleteSpace ((forget CStarAlg).obj A) :=
  A.completeSpace

end CStarAlg

namespace CStarAlg₁

noncomputable instance : Inhabited CStarAlg₁ := ⟨⟨ℂ⟩⟩

instance : CoeSort CStarAlg₁ Type* := ⟨CStarAlg₁.carrier⟩

attribute [instance] normedRing starRing cstarRing normedAlgebra starModule
  completeSpace

noncomputable instance : Category CStarAlg₁.{u} where
  Hom A B := A →⋆ₐ[ℂ] B
  id A := StarAlgHom.id ℂ A
  comp f g := g.comp f

instance instFunLike (X Y : CStarAlg₁) : FunLike (X ⟶ Y) X Y :=
  inferInstanceAs <| FunLike (X →⋆ₐ[ℂ] Y) X Y

instance instAlgHomClass (X Y : CStarAlg₁) : AlgHomClass (X ⟶ Y) ℂ X Y :=
  inferInstanceAs <| AlgHomClass (X →⋆ₐ[ℂ] Y) ℂ X Y

instance instStarHomClass (X Y : CStarAlg₁) : StarHomClass (X ⟶ Y) X Y :=
  inferInstanceAs <| StarHomClass (X →⋆ₐ[ℂ] Y) X Y

noncomputable instance : ConcreteCategory CStarAlg₁.{u} where
  forget :=
    { obj := fun A ↦ A
      map := fun f ↦ f }
  forget_faithful :=
    { map_injective := fun {X Y} ↦ DFunLike.coe_injective }

/-- Construct a bundled `CStarAlg₁` from the underlying type and appropriate type classes. -/
def of (A : Type u) [NormedRing A] [StarRing A] [CStarRing A] [NormedAlgebra ℂ A]
  [StarModule ℂ A] [CompleteSpace A] : CStarAlg₁ := ⟨A⟩

@[simp] lemma coe_of (A : Type u) [NormedRing A] [StarRing A] [CStarRing A] [NormedAlgebra ℂ A]
  [StarModule ℂ A] [CompleteSpace A] : (of A : Type u) = A := rfl

instance hasForget₂CStarAlg : HasForget₂ CStarAlg₁ CStarAlg where
  forget₂ :=
    { obj := fun X ↦ { carrier := X.carrier }
      -- need to bump Mathlib to a newer version
      map := fun {X Y} f ↦ NonUnitalStarAlgHomClass.toNonUnitalStarAlgHom f }

noncomputable instance hasForget₂Algebra : HasForget₂ CStarAlg₁ (AlgebraCat ℂ) where
  forget₂ :=
    { obj := fun X ↦ {carrier:= X.carrier},
      map := fun {X Y} f ↦ AlgHomClass.toAlgHom f }

end CStarAlg₁

/-- The type of commutative unital C⋆-algebras with unital ⋆-algebra morphisms.

This is implemented as a full subcategory of `CStarAlg₁`. -/
def CommCStarAlg₁ := FullSubcategory (fun A : CStarAlg₁ ↦ ∀ x y : A.carrier, x * y = y * x)

namespace CommCStarAlg₁

instance : Category CommCStarAlg₁ := FullSubcategory.category _

instance : ConcreteCategory CommCStarAlg₁ := FullSubcategory.concreteCategory _

instance : HasForget₂ CommCStarAlg₁ CStarAlg₁ := FullSubcategory.hasForget₂ _

instance : HasForget₂ CommCStarAlg₁ (AlgebraCat ℂ) :=
  HasForget₂.trans (CommCStarAlg₁) (CStarAlg₁) (AlgebraCat ℂ)

instance : CoeSort CommCStarAlg₁.{u} (Type u) := ⟨fun A ↦ A.obj⟩

instance instFunLike (X Y : CommCStarAlg₁) : FunLike (X ⟶ Y) X Y :=
  inferInstanceAs <| FunLike (X →⋆ₐ[ℂ] Y) X Y

instance instAlgHomClass (X Y : CommCStarAlg₁) : AlgHomClass (X ⟶ Y) ℂ X Y :=
  inferInstanceAs <| AlgHomClass (X →⋆ₐ[ℂ] Y) ℂ X Y

instance instStarHomClass (X Y : CommCStarAlg₁) : StarHomClass (X ⟶ Y) X Y :=
  inferInstanceAs <| StarHomClass (X →⋆ₐ[ℂ] Y) X Y

instance (A : CommCStarAlg₁) : NormedCommRing A where
  mul_comm := A.property

/-- Construct a bundled `CommCStarAlg₁` from the underlying type and appropriate type classes. -/
def of (A : Type u) [NormedCommRing A] [StarRing A] [CStarRing A] [NormedAlgebra ℂ A]
    [StarModule ℂ A] [CompleteSpace A] : CommCStarAlg₁ where
  obj := ⟨A⟩
  property := mul_comm

@[simp] lemma coe_of (A : Type u) [NormedCommRing A] [StarRing A] [CStarRing A]
  [NormedAlgebra ℂ A] [StarModule ℂ A] [CompleteSpace A] : (of A : Type u) = A := rfl

end CommCStarAlg₁

namespace StarAlgEquiv

/-- Build an isomorphism in the category `CStarAlg` from a `StarAlgEquiv` between C⋆-algebras -/
@[simps]
noncomputable def toCStarAlgIso {A B : Type u} [NonUnitalNormedRing A] [StarRing A]
  [CStarRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [StarModule ℂ A] [CompleteSpace A] [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
  [NormedSpace ℂ B] [IsScalarTower ℂ B B] [SMulCommClass ℂ B B] [StarModule ℂ B]
  [CompleteSpace B] (e : A ≃⋆ₐ[ℂ] B) : CStarAlg.of A ≅ CStarAlg.of B :=
{ hom := (e : A →⋆ₙₐ[ℂ] B),
  inv := (e.symm : B →⋆ₙₐ[ℂ] A),
  hom_inv_id := NonUnitalStarAlgHom.ext $ fun _ ↦ e.symm_apply_apply _,
  inv_hom_id := NonUnitalStarAlgHom.ext $ fun _ ↦ e.apply_symm_apply _ }

/-- Build an isomorphism in the category `CStarAlg₁` from a `StarAlgEquiv` between unital
C⋆-algebras -/
@[simps]
noncomputable def toCStarAlg₁Iso {A B : Type u} [NormedRing A] [StarRing A] [CStarRing A]
  [NormedAlgebra ℂ A] [StarModule ℂ A] [CompleteSpace A] [NormedRing B] [StarRing B]
  [CStarRing B] [NormedAlgebra ℂ B] [StarModule ℂ B] [CompleteSpace B]
  (e : A ≃⋆ₐ[ℂ] B) : CStarAlg₁.of A ≅ CStarAlg₁.of B :=
{ hom := (e : A →⋆ₐ[ℂ] B),
  inv := (e.symm : B →⋆ₐ[ℂ] A),
  hom_inv_id := StarAlgHom.ext $ fun _ => e.symm_apply_apply _,
  inv_hom_id := StarAlgHom.ext $ fun _ => e.apply_symm_apply _ }

/-- Build an isomorphism in the category `CommCStarAlg₁` from a `StarAlgEquiv` between
commutative unital C⋆-algebras -/
@[simps]
noncomputable def toCommCStarAlg₁Iso {A B : Type u} [NormedCommRing A] [StarRing A]
  [CStarRing A] [NormedAlgebra ℂ A] [StarModule ℂ A] [CompleteSpace A] [NormedCommRing B]
  [StarRing B] [CStarRing B] [NormedAlgebra ℂ B] [StarModule ℂ B] [CompleteSpace B]
  (e : A ≃⋆ₐ[ℂ] B) : CommCStarAlg₁.of A ≅ CommCStarAlg₁.of B :=
{ hom := (e : A →⋆ₐ[ℂ] B),
  inv := (e.symm : B →⋆ₐ[ℂ] A),
  hom_inv_id := StarAlgHom.ext $ fun _ => e.symm_apply_apply _,
  inv_hom_id := StarAlgHom.ext $ fun _ => e.apply_symm_apply _ }

end StarAlgEquiv

namespace CategoryTheory.Iso

/-- Build a `StarAlgEquiv` from an isomorphism in the category `CStarAlg`. -/
noncomputable def CStarAlgIsoToStarAlgEquiv {X Y : CStarAlg} (i : X ≅ Y) : X ≃⋆ₐ[ℂ] Y :=
{ toFun    := i.hom,
  invFun   := i.inv,
  left_inv  := i.hom_inv_id_apply,
  right_inv := i.inv_hom_id_apply,
  map_add'  := map_add i.hom,
  map_mul'  := map_mul i.hom,
  map_smul' := map_smul i.hom,
  map_star' := map_star i.hom, }

/-- Build a `StarAlgEquiv` from an isomorphism in the category `CStarAlg₁`. -/
noncomputable def CStarAlg₁IsoToStarAlgEquiv {X Y : CStarAlg₁} (i : X ≅ Y) : X ≃⋆ₐ[ℂ] Y :=
{ toFun    := i.hom,
  invFun   := i.inv,
  left_inv  := i.hom_inv_id_apply,
  right_inv := i.inv_hom_id_apply,
  map_add'  := map_add i.hom,
  map_mul'  := map_mul i.hom,
  map_smul' := map_smul i.hom,
  map_star' := map_star i.hom, }

set_option synthInstance.maxHeartbeats 100000 in
/-- Build a `StarAlgEquiv` from an isomorphism in the category `CommCStarAlg₁`. -/
noncomputable def CommCStarAlg₁IsoToStarAlgEquiv {X Y : CommCStarAlg₁} (i : X ≅ Y) :
  X ≃⋆ₐ[ℂ] Y :=
{ toFun    := i.hom,
  invFun   := i.inv,
  left_inv  := i.hom_inv_id_apply,
  right_inv := i.inv_hom_id_apply,
  map_add'  := map_add i.hom,
  map_mul'  := map_mul i.hom,
  map_smul' := map_smul i.hom,
  map_star' := map_star i.hom, }

end CategoryTheory.Iso

instance CStarAlg.forgetReflectsIsos : (forget CStarAlg.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CStarAlg).map f)
    let e : X ≃⋆ₐ[ℂ] Y := { i.toEquiv, f with }
    exact e.toCStarAlgIso.isIso_hom

instance CStarAlg₁.forgetReflectsIsos : (forget CStarAlg₁.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CStarAlg₁).map f)
    let e : X ≃⋆ₐ[ℂ] Y := { i.toEquiv, f with map_smul' := map_smul f }
    exact e.toCStarAlg₁Iso.isIso_hom

instance CommCStarAlg₁.forgetReflectsIsos : (forget CommCStarAlg₁.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommCStarAlg₁).map f)
    let e : X ≃⋆ₐ[ℂ] Y := { i.toEquiv, f with map_smul' := map_smul f }
    exact e.toCommCStarAlg₁Iso.isIso_hom
