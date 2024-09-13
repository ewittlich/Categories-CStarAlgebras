import Mathlib

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

/-- The type of commutative unital C⋆-algebras with unital ⋆-algebra morphisms. -/
structure CommCStarAlg₁ :=
(carrier : Type u)
[normedCommRing : NormedCommRing carrier]
[starRing : StarRing carrier]
[cstarRing : CStarRing carrier]
[normedAlgebra : NormedAlgebra ℂ carrier]
[starModule : StarModule ℂ carrier]
[completeSpace : CompleteSpace carrier]

namespace CStarAlg

noncomputable instance : Inhabited CStarAlg := ⟨⟨ℂ⟩⟩

instance : CoeSort CStarAlg (Type u) := ⟨CStarAlg.carrier⟩

attribute [instance] nonUnitalNormedRing starRing cstarRing normedSpace
  isScalarTower smulCommClass starModule completeSpace

noncomputable instance : Category CStarAlg.{u} :=
{ Hom := fun A B => A →⋆ₙₐ[ℂ] B,
  id := fun A => NonUnitalStarAlgHom.id ℂ A,
  comp := fun f g => g.comp f }

noncomputable instance : ConcreteCategory CStarAlg.{u} :=
{ forget :=
    { obj := fun A => A,
      map := fun {X Y} f => f.toFun },
  forget_faithful := by
    -- ⊢ { obj := fun A ↦ A.carrier, map := fun {X Y} f ↦ f.toFun, map_id := ⋯, map_comp := ⋯ }.Faithful
    apply
    sorry }

/-- Construct a bundled `CStarAlg` from the underlying type and appropriate type classes. -/
def of (A : Type u) [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [ NormedSpace ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] [CompleteSpace A] :
  CStarAlg := ⟨A⟩

@[simp] lemma coe_of (A : Type u) [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
  [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
  [CompleteSpace A] : (of A : Type u) = A := rfl

instance forgetNonUnitalNormedRing (A : CStarAlg) :
  NonUnitalNormedRing ((forget CStarAlg).obj A) :=
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

noncomputable instance : Category CStarAlg₁.{u} :=
{ Hom := fun A B => A →⋆ₐ[ℂ] B,
  id := fun A => StarAlgHom.id ℂ A,
  comp := fun  f g => g.comp f }

noncomputable instance : ConcreteCategory CStarAlg₁.{u} :=
{ forget := { obj := fun A => A, map := fun {X Y} f => f.toFun },
  forget_faithful := by
    sorry
     }

/-- Construct a bundled `CStarAlg₁` from the underlying typa and appropriate type classes. -/
def of (A : Type u) [NormedRing A] [StarRing A] [CStarRing A] [NormedAlgebra ℂ A]
  [StarModule ℂ A] [CompleteSpace A] : CStarAlg₁ := ⟨A⟩

@[simp] lemma coe_of (A : Type u) [NormedRing A] [StarRing A] [CStarRing A] [NormedAlgebra ℂ A]
  [StarModule ℂ A] [CompleteSpace A] : (of A : Type u) = A := rfl

noncomputable instance forgetToCStarAlg : forget₂ CStarAlg₁ CStarAlg :=
{ forget₂ :=
  { obj := fun A => ⟨A⟩,
    map := fun A B f => (f : A →⋆ₙₐ[ℂ] B), } }

noncomputable instance forgetToAlgebra : forget₂ CStarAlg₁ (Algebra ℂ) :=
{ forget₂ :=
  { obj := fun A => ⟨A⟩,
    map := fun A B f => f.to_alg_hom } }

end CStarAlg₁

namespace CommCStarAlg₁

noncomputable instance : Inhabited CommCStarAlg₁ := ⟨⟨ℂ⟩⟩

instance : CoeSort CommCStarAlg₁ Type* := ⟨CommCStarAlg₁.carrier⟩

attribute [instance] normedCommRing starRing cstarRing normedAlgebra starModule
  completeSpace

noncomputable instance : Category CommCStarAlg₁.{u} :=
{ Hom := fun A B => A →⋆ₐ[ℂ] B,
  id := fun A => StarAlgHom.id ℂ A,
  comp := fun f g => g.comp f }

noncomputable instance : ConcreteCategory CommCStarAlg₁.{u} :=
{ forget := { obj := fun A => A, map := fun {X Y} f => f.toFun },
  forget_faithful := by
    sorry
    }

/-- Construct a bundled `CommCStarAlg₁` from the underlying typa and appropriate type classes. -/
def of (A : Type u) [NormedCommRing A] [StarRing A] [CStarRing A] [NormedAlgebra ℂ A]
  [StarModule ℂ A] [CompleteSpace A] : CommCStarAlg₁ := ⟨A⟩

@[simp] lemma coe_of (A : Type u) [NormedCommRing A] [StarRing A] [CStarRing A]
  [NormedAlgebra ℂ A] [StarModule ℂ A] [CompleteSpace A] : (of A : Type u) = A := rfl

instance forget_to_CStarAlg₁ : forget₂ CommCStarAlg₁ CStarAlg₁ :=
{ forget₂ :=
  { obj := fun A => ⟨A⟩,
    map := fun {X Y} f => f.toFun } }

end CommCStarAlg₁

namespace StarAlgEquiv

/-- Build an isomorphism in the category `CStarAlg` from a `star_alg_equiv` between C⋆-algebras -/
@[simps]
noncomputable def CStarAlgIso {A B : Type u} [NonUnitalNormedRing A] [StarRing A]
  [CStarRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [StarModule ℂ A] [CompleteSpace A] [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
  [NormedSpace ℂ B] [IsScalarTower ℂ B B] [SMulCommClass ℂ B B] [StarModule ℂ B]
  [CompleteSpace B] (e : A ≃⋆ₐ[ℂ] B) : CStarAlg.of A ≅ CStarAlg.of B :=
{ Hom := (e : A →⋆ₙₐ[ℂ] B),
  inv := (e.symm : B →⋆ₙₐ[ℂ] A),
  hom_inv_id' := NonUnitalStarAlgHom.ext $ fun _ => e.symm_apply_apply _,
  inv_hom_id' := NonUnitalStarAlgHom.ext $ fun _ => e.apply_symm_apply _ }

/-- Build an isomorphism in the category `CStarAlg₁` from a `star_alg_equiv` between unital
C⋆-algebras -/
@[simps]
noncomputable def CStarAlg₁Iso {A B : Type u} [NormedRing A] [StarRing A] [CStarRing A]
  [NormedAlgebra ℂ A] [StarModule ℂ A] [CompleteSpace A] [NormedRing B] [StarRing B]
  [CStarRing B] [NormedAlgebra ℂ B] [StarModule ℂ B] [CompleteSpace B]
  (e : A ≃⋆ₐ[ℂ] B) : CStarAlg₁.of A ≅ CStarAlg₁.of B :=
{ hom := (e : A →⋆ₐ[ℂ] B),
  inv := (e.symm : B →⋆ₐ[ℂ] A),
  hom_inv_id' := StarAlgHom.ext $ fun _ => e.SymmApplyApply _,
  inv_hom_id' := StarAlgHom.ext $ fun _ => e.ApplySymmApply _ }

/-- Build an isomorphism in the category `CommCStarAlg₁` from a `star_alg_equiv` between
commutative unital C⋆-algebras -/
@[simps]
noncomputable def CommCStarAlg₁Iso {A B : Type u} [NormedCommRing A] [StarRing A]
  [CStarRing A] [NormedAlgebra ℂ A] [StarModule ℂ A] [CompleteSpace A] [NormedCommRing B]
  [StarRing B] [CStarRing B] [NormedAlgebra ℂ B] [StarModule ℂ B] [CompleteSpace B]
  (e : A ≃⋆ₐ[ℂ] B) : CommCStarAlg₁.of A ≅ CommCStarAlg₁.of B :=
{ hom := (e : A →⋆ₐ[ℂ] B),
  inv := (e.symm : B →⋆ₐ[ℂ] A),
  hom_inv_id' := StarAlgHom.ext $ fun _ => e.SymmApplyApply _,
  inv_hom_id' := star_alg_hom.ext $ fun _ => e.ApplySymmApply _ }

end StarAlgEquiv

namespace category_theory.iso

/-- Build a `star_alg_equiv` from an isomorphism in the category `CStarAlg`. -/
noncomputable def CStarAlg_iso_to_star_alg_equiv {X Y : CStarAlg} (i : X ≅ Y) : X ≃⋆ₐ[ℂ] Y :=
{ to_fun    := i.Hom,
  inv_fun   := i.inv,
  left_inv  := i.hom_inv_id_apply,
  right_inv := i.inv_hom_id_apply,
  map_add'  := map_add i.hom,
  map_mul'  := map_mul i.hom,
  map_smul' := map_smul i.hom,
  map_star' := map_star i.hom, }

/-- Build a `star_alg_equiv` from an isomorphism in the category `CStarAlg₁`. -/
noncomputable def CStarAlg₁_iso_to_star_alg_equiv {X Y : CStarAlg₁} (i : X ≅ Y) : X ≃⋆ₐ[ℂ] Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := i.hom_inv_id_apply,
  right_inv := i.inv_hom_id_apply,
  map_add'  := map_add i.hom,
  map_mul'  := map_mul i.hom,
  map_smul' := map_smul i.hom,
  map_star' := map_star i.hom, }

/-- Build a `star_alg_equiv` from an isomorphism in the category `CommCStarAlg₁`. -/
noncomputable def CommCStarAlg₁_iso_to_star_alg_equiv {X Y : CommCStarAlg₁} (i : X ≅ Y) :
  X ≃⋆ₐ[ℂ] Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := i.hom_inv_id_apply,
  right_inv := i.inv_hom_id_apply,
  map_add'  := map_add i.hom,
  map_mul'  := map_mul i.hom,
  map_smul' := map_smul i.hom,
  map_star' := map_star i.hom, }

end category_theory.iso

instance CStarAlg.forget_reflects_isos : reflects_isomorphisms (forget CStarAlg.{u}) :=
{ reflects := λ X Y f _,
  begin
    resetI,
    let i := as_iso ((forget CStarAlg).map f),
    let e : X ≃⋆ₐ[ℂ] Y := { ..f, ..i.to_equiv },
    exact ⟨(is_iso.of_iso e.to_CStarAlg_iso).1⟩,
  end }

instance CStarAlg₁.forget_reflects_isos : reflects_isomorphisms (forget CStarAlg₁.{u}) :=
{ reflects := λ X Y f _,
  begin
    resetI,
    let i := as_iso ((forget CStarAlg₁).map f),
    let e : X ≃⋆ₐ[ℂ] Y := { map_smul' := map_smul f, ..f, ..i.to_equiv },
    exact ⟨(is_iso.of_iso e.to_CStarAlg₁_iso).1⟩,
  end }

instance CommCStarAlg₁.forget_reflects_isos : reflects_isomorphisms (forget CommCStarAlg₁.{u}) :=
{ reflects := λ X Y f _,
  begin
    resetI,
    let i := as_iso ((forget CommCStarAlg₁).map f),
    let e : X ≃⋆ₐ[ℂ] Y := { map_smul' := map_smul f, ..f, ..i.to_equiv },
    exact ⟨(is_iso.of_iso e.to_CommCStarAlg₁_iso).1⟩,
  end }
Footer
