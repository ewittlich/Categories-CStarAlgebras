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
  comp := fun A B C f g => g.comp f }

noncomputable instance : ConcreteCategory CStarAlg.{u} :=
{ forget := { obj := fun A => A, map := fun A B f => f },
  forget_faithful := { } }

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

noncomputable instance : inhabited CStarAlg₁ := ⟨⟨ℂ⟩⟩

instance : has_coe_to_sort CStarAlg₁ Type* := ⟨CStarAlg₁.α⟩

attribute [instance] is_normed_ring is_star_ring is_cstar_ring is_normed_algebra is_star_module
  is_complete_space

noncomputable instance : category CStarAlg₁.{u} :=
{ hom := λ A B, A →⋆ₐ[ℂ] B,
  id := λ A, star_alg_hom.id ℂ A,
  comp := λ A B C f g, g.comp f }

noncomputable instance : concrete_category CStarAlg₁.{u} :=
{ forget := { obj := λ A, A, map := λ A B f, f },
  forget_faithful := { } }

/-- Construct a bundled `CStarAlg₁` from the underlying typa and appropriate type classes. -/
def of (A : Type u) [normed_ring A] [star_ring A] [cstar_ring A] [normed_algebra ℂ A]
  [star_module ℂ A] [complete_space A] : CStarAlg₁ := ⟨A⟩

@[simp] lemma coe_of (A : Type u) [normed_ring A] [star_ring A] [cstar_ring A] [normed_algebra ℂ A]
  [star_module ℂ A] [complete_space A] : (of A : Type u) = A := rfl

noncomputable instance has_forget_to_CStarAlg : has_forget₂ CStarAlg₁ CStarAlg :=
{ forget₂ :=
  { obj := λ A, ⟨A⟩,
    map := λ A B f, (f : A →⋆ₙₐ[ℂ] B), } }

noncomputable instance has_forget_to_Algebra : has_forget₂ CStarAlg₁ (Algebra ℂ) :=
{ forget₂ :=
  { obj := λ A, ⟨A⟩,
    map := λ A B f, f.to_alg_hom } }

end CStarAlg₁

namespace CommCStarAlg₁

noncomputable instance : inhabited CommCStarAlg₁ := ⟨⟨ℂ⟩⟩

instance : has_coe_to_sort CommCStarAlg₁ Type* := ⟨CommCStarAlg₁.α⟩

attribute [instance] is_normed_comm_ring is_star_ring is_cstar_ring is_normed_algebra is_star_module
  is_complete_space

noncomputable instance : category CommCStarAlg₁.{u} :=
{ hom := λ A B, A →⋆ₐ[ℂ] B,
  id := λ A, star_alg_hom.id ℂ A,
  comp := λ A B C f g, g.comp f }

noncomputable instance : concrete_category CommCStarAlg₁.{u} :=
{ forget := { obj := λ A, A, map := λ A B f, f },
  forget_faithful := { } }

/-- Construct a bundled `CommCStarAlg₁` from the underlying typa and appropriate type classes. -/
def of (A : Type u) [normed_comm_ring A] [star_ring A] [cstar_ring A] [normed_algebra ℂ A]
  [star_module ℂ A] [complete_space A] : CommCStarAlg₁ := ⟨A⟩

@[simp] lemma coe_of (A : Type u) [normed_comm_ring A] [star_ring A] [cstar_ring A]
  [normed_algebra ℂ A] [star_module ℂ A] [complete_space A] : (of A : Type u) = A := rfl

instance has_forget_to_CStarAlg₁ : has_forget₂ CommCStarAlg₁ CStarAlg₁ :=
{ forget₂ :=
  { obj := λ A, ⟨A⟩,
    map := λ A B f, f } }

end CommCStarAlg₁
