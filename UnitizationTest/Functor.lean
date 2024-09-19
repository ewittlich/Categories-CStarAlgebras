import UnitizationTest.Basic

open CategoryTheory

section Unitization

open Unitization

-- this should be in Mathlib
def Unitization.fstStarAlgHom (R A : Type*) [CommSemiring R] [NonUnitalSemiring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarAddMonoid R] [Star A] :
    Unitization R A →⋆ₐ[R] R where
  toAlgHom := fstHom R A
  map_star' _ := rfl

section fst_snd

variable {R A B : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A]
    [StarRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [NonUnitalSemiring B]
    [StarRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B] [StarModule R B]

-- this should be in Mathlib
@[simp]
theorem Unitization.fst_starMap (φ : A →⋆ₙₐ[R] B) (x : Unitization R A) :
    fst (starMap φ x) = fst x := by
  induction x using ind
  simp [algebraMap_eq_inl]

-- this should be in Mathlib
@[simp]
theorem Unitization.snd_starMap (φ : A →⋆ₙₐ[R] B) (x : Unitization R A) :
    snd (starMap φ x) = φ (snd x) := by
  induction x using ind
  simp [algebraMap_eq_inl]

end fst_snd

/-- The functor which sends a C⋆-algebra to its unitization, and a non-unital
star homomorphism `f` to `Unitization.starMap f`. -/
noncomputable def CStarAlg.unitization : CStarAlg ⥤ CStarAlg₁ where
  obj A := ⟨Unitization ℂ A⟩
  map f := starMap f
  map_id _ := starMap_id
  map_comp _ _ := starMap_comp

/-- The functor `CStarAlg.unitization` upgraded to a functor into the category of unital
C⋆-algebras over `ℂ`. -/
noncomputable def CStarAlg.unitization_over : CStarAlg ⥤ Over (CStarAlg₁.of ℂ) :=
  unitization.toOver _ (fstStarAlgHom ℂ ·) (fun f ↦ by ext x; exact Unitization.fst_starMap f x)

-- this should be the inverse to `CStarAlg.unitization_over`, but we can't do this because
-- we're lacking (a) the kernel of a star homomorphism as a `TwoSidedIdeal`, and
-- (b) a C⋆-algebra structure on `TwoSidedIdeal`s.
-- Given `A : Over (CStarAlg₁.of ℂ)`, this should send `A` to `ker A.hom`.
-- Given a morphism `f : A ⟶ B` in `Over (CStarAlg₁.of ℂ)`, this should send `f` to
-- the restriction `f.left : ker A.hom →⋆ₙₐ[ℂ] ker B.hom`, admittedly a bit messy.
noncomputable def CStarAlg.ker_over : Over (CStarAlg₁.of ℂ) ⥤ CStarAlg := sorry

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
  unitIso := NatIso.ofComponents
    fun A ↦ (gelfandStarTransform A).toCommCStarAlg₁Iso (B := (toCompHaus ⋙ ofCompHaus).obj A)
  counitIso := NatIso.op <|
    show (𝟭 CompHaus) ≅ (ofCompHaus.rightOp ⋙ toCompHaus.leftOp) from NatIso.ofComponents
      fun X ↦ CompHausLike.isoOfHomeo (WeakDual.CharacterSpace.homeoEval X ℂ)

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
def of (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] : LocCompHaus := ⟨X⟩

@[simp] lemma coe_of (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] : (of X : Type u) = X := rfl

instance forgetTopologicalSpace (X : LocCompHaus) : TopologicalSpace ((forget LocCompHaus).obj X) :=
  X.topologicalSpace

instance forgetLocallyCompactSpace (X : LocCompHaus) : LocallyCompactSpace ((forget LocCompHaus).obj X) :=
  X.locallyCompactSpace

instance forgetT2Space (X : LocCompHaus) : T2Space ((forget LocCompHaus).obj X) :=
  X.t2space

variable {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]

-- `  CategoryTheory.Under.post`

end LocCompHaus

/-- The category of pointed compact Hausdorff spaces. -/
def PtCompHaus := Under (CompHaus.of PUnit)

namespace PtCompHaus

instance : Category PtCompHaus := instCategoryUnder _

example : (Under (CompHaus.of PUnit))ᵒᵖ ≌ Over (CompHaus.of PUnit) := sorry

end PtCompHaus
