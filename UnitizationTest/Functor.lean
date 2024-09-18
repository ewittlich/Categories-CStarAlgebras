import UnitizationTest.Basic

open CategoryTheory

open Unitization in
noncomputable def CStarAlg.unitization : CStarAlg ⥤ CStarAlg₁ where
  obj A := ⟨Unitization ℂ A⟩
  map f := starMap f
  map_id _ := starMap_id
  map_comp _ _ := starMap_comp

universe u v

namespace CommCStarAlg₁

noncomputable def ofCompHaus : CompHaus.{u}ᵒᵖ ⥤ CommCStarAlg₁.{u} where
  obj X := ⟨⟨C(X.unop, ℂ)⟩, mul_comm⟩
  map {X Y} f := ContinuousMap.compStarAlgHom' ℂ ℂ f.unop

open Opposite in
noncomputable def toCompHaus : CommCStarAlg₁.{u} ⥤ CompHaus.{u}ᵒᵖ where
  obj A := ⟨{toTop := {α := WeakDual.characterSpace ℂ A}, prop := True.intro}⟩
  map {X Y} f := op (WeakDual.CharacterSpace.compContinuousMap f)

noncomputable def gelfandDuality : CommCStarAlg₁.{u} ≌ CompHaus.{u}ᵒᵖ where
  functor := toCompHaus
  inverse := ofCompHaus
  unitIso := NatIso.ofComponents fun A ↦(gelfandStarTransform A).toCommCStarAlg₁Iso (B := (toCompHaus ⋙ ofCompHaus).obj A)
  counitIso := NatIso.op <| show (𝟭 CompHaus) ≅ (ofCompHaus.rightOp ⋙ toCompHaus.leftOp)
    from NatIso.ofComponents fun X ↦ CompHausLike.isoOfHomeo (WeakDual.CharacterSpace.homeoEval X ℂ)

end CommCStarAlg₁

structure LocCompHaus where
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  [locallyCompactSpace : LocallyCompactSpace carrier]
  [t2space : T2Space carrier]

namespace LocCompHaus

noncomputable instance : Inhabited LocCompHaus := ⟨⟨Empty⟩⟩

instance : CoeSort LocCompHaus (Type u) := ⟨LocCompHaus.carrier⟩

attribute [instance] topologicalSpace locallyCompactSpace t2space

noncomputable instance : Category LocCompHaus.{u} where
  Hom X Y := CocompactMap X Y
  id X := CocompactMap.id X
  comp f g := g.comp f

instance instFunLike (X Y : LocCompHaus) : FunLike (X ⟶ Y) X Y :=
  inferInstanceAs <| FunLike (CocompactMap X Y) X Y

instance instCocompactMapClass (X Y : LocCompHaus) : CocompactMapClass (X ⟶ Y) X Y :=
  inferInstanceAs <| CocompactMapClass (CocompactMap X Y) X Y

noncomputable instance : ConcreteCategory LocCompHaus.{u} where
  forget :=
    { obj := fun A ↦ A
      map := fun f ↦ f }
  forget_faithful :=
    { map_injective := fun {X Y} ↦ DFunLike.coe_injective }

/-- Construct a bundled `LocCompHaus` from the underlying type and appropriate type classes. -/
def of (A : Type u) [TopologicalSpace A] [LocallyCompactSpace A] [T2Space A] : LocCompHaus := ⟨A⟩

@[simp] lemma coe_of (A : Type u) [TopologicalSpace A] [LocallyCompactSpace A] [T2Space A] : (of A : Type u) = A := rfl

instance forgetTopologicalSpace (A : LocCompHaus) : TopologicalSpace ((forget LocCompHaus).obj A) :=
  A.topologicalSpace

instance forgetLocallyCompactSpace (A : LocCompHaus) : LocallyCompactSpace ((forget LocCompHaus).obj A) :=
  A.locallyCompactSpace

instance forgetT2Space (A : LocCompHaus) : T2Space ((forget LocCompHaus).obj A) :=
  A.t2space

end LocCompHaus
