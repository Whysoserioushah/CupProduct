import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

open CategoryTheory MonoidalCategory groupCohomology

variable (R G : Type u) [CommRing R] [Group G]

-- instance : HasForget₂ (Rep R G) Ab := .trans (Rep R G) (ModuleCat R) Ab

-- instance : (forget₂ (Rep R G) Ab).Additive :=
--   inferInstanceAs (_ ⋙ _).Additive

-- instance : (forget₂ (Rep R G) Ab).PreservesHomology :=
--   { preservesKernels _ _ _ := Limits.comp_preservesLimit _ _
--     preservesCokernels _ _ _:= Limits.comp_preservesColimit _ _ }

noncomputable section

open LinearMap

variable {R G} (A B : Rep R G)

lemma mem_tensorInvariants (a : A.ρ.invariants) (b : B.ρ.invariants) (g : G) :
    ((A ⊗ B).ρ g) (a.1 ⊗ₜ b.1) = a.1 ⊗ₜ b.1 := by
  simp [a.2 g, b.2 g]

def cup0Aux' (a : A.ρ.invariants) : B.ρ.invariants →ₗ[R] (A ⊗ B).ρ.invariants where
  toFun b := ⟨TensorProduct.tmul R a.1 b.1, mem_tensorInvariants A B a b⟩
  map_add' := fun ⟨b1, hb1⟩ ⟨b2, hb2⟩ ↦ by
    ext; simp [TensorProduct.tmul_add]
  map_smul' r := fun ⟨b, hb⟩ ↦ by ext; simp

def cup0Aux : A.ρ.invariants →ₗ[R] B.ρ.invariants →ₗ[R] (A ⊗ B).ρ.invariants where
  toFun := cup0Aux' A B
  map_add' := fun ⟨a1, ha1⟩ ⟨a2, ha2⟩ ↦ by
    ext; simp [cup0Aux', TensorProduct.add_tmul]
  map_smul' r := fun ⟨a, ha⟩ ↦ by ext; simp [cup0Aux', TensorProduct.smul_tmul]

open LinearMap

noncomputable def cup0 : H0 A →ₗ[R] H0 B →ₗ[R] H0 (A ⊗ B) where
  toFun a := (H0Iso (A ⊗ B)).inv.hom ∘ₗ cup0Aux A B ((H0Iso A).hom.hom a) ∘ₗ (H0Iso B).hom.hom
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
lemma cup0_apply (a : H0 A) (b : H0 B) : cup0 A B a b = (H0Iso (A ⊗ B)).inv.hom
  ⟨((H0Iso A).hom.hom a).1 ⊗ₜ ((H0Iso B).hom.hom b).1, mem_tensorInvariants A B
    (H0Iso A|>.hom.hom a) (H0Iso B|>.hom.hom b)⟩ := rfl

@[simp]
lemma H0Iso_hom_cup0_coe (a : H0 A) (b : H0 B) : ((H0Iso (A ⊗ B)).hom.hom (cup0 A B a b)).1 =
    ((H0Iso A).hom.hom a).1 ⊗ₜ[R] ((H0Iso B).hom.hom b).1 := by
  rw [cup0_apply, Iso.inv_hom_id_apply]

noncomputable def cup0' : H0 A ⊗ H0 B ⟶ H0 (A ⊗ B) :=
  ModuleCat.ofHom <| TensorProduct.lift (cup0 A B)

lemma map_id_tensor_comp_H0Iso_inv {M1 M2 N1 N2 : Rep R G} (f : M1 ⊗ N1 ⟶ M2 ⊗ N2) :
    (Rep.invariantsFunctor R G).map f ≫ (H0Iso (M2 ⊗ N2)).inv =
    (H0Iso (M1 ⊗ N1)).inv ≫ map (MonoidHom.id G) f 0 := by
  apply_fun (fun f ↦ (H0Iso _).hom ≫ f ≫ (H0Iso _).hom) using by aesop_cat
  simp only [← Category.assoc, (Iso.hom_comp_eq_id (H0Iso _)).2 rfl, Category.id_comp]
  -- simp only [Action.tensorObj_V, Rep.tensor_ρ, Category.assoc, Iso.inv_comp_eq_id (H0Iso _) |>.2,
  --   map_id_comp_H0Iso_hom]
  -- change _ = (H0Iso (M1 ⊗ N1)).hom ≫ _
  -- erw [Category.comp_id]
  sorry

lemma map_id_tensor_comp_H0Iso_inv_apply {M1 M2 N1 N2 : Rep R G} (f : M1 ⊗ N1 ⟶ M2 ⊗ N2)
    (x : (M1 ⊗ N1).ρ.invariants) :
    ((H0Iso (M2 ⊗ N2)).inv.hom (((Rep.invariantsFunctor R G).map f).hom x)) =
    (map (MonoidHom.id G) f 0).hom ((H0Iso (M1 ⊗ N1)).inv.hom x) := by
  -- erw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
  -- conv_rhs => erw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
  -- rw [map_id_tensor_comp_H0Iso_inv]
  -- rfl
  sorry

@[reassoc]
lemma smallcommSq1 {M N : Rep R G} (φ : M ⟶ N) : (Rep.invariantsFunctor R G).map (A ◁ φ) ≫
    (H0Iso (A ⊗ N)).inv = (H0Iso (A ⊗ M)).inv ≫
    groupCohomology.map (MonoidHom.id G) (A ◁ φ) 0 := by
  -- apply_fun (fun f ↦ (H0Iso _).hom ≫ f ≫ (H0Iso _).hom) using by aesop_cat
  -- simp only [← Category.assoc, (Iso.hom_comp_eq_id (H0Iso _)).2 rfl, Category.id_comp]
  -- simp only [Action.tensorObj_V, Rep.tensor_ρ, Category.assoc, Iso.inv_comp_eq_id (H0Iso _) |>.2,
  --   map_id_comp_H0Iso_hom, Iso.cancel_iso_hom_left]
  -- rfl
  sorry

lemma smallcommSq1_apply {M N : Rep R G} (φ : M ⟶ N) (x : (A ⊗ M).ρ.invariants) :
    (H0Iso (A ⊗ N)).inv.hom (((Rep.invariantsFunctor R G).map (A ◁ φ)).hom x) =
    (groupCohomology.map (MonoidHom.id G) (A ◁ φ) 0).hom ((H0Iso (A ⊗ M)).inv.hom x) := by
  -- rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
  -- erw [← LinearMap.comp_apply]
  -- rw [← ModuleCat.hom_comp, smallcommSq1 A φ]
  -- rfl
  sorry

noncomputable section

open TensorProduct in
set_option backward.isDefEq.respectTransparency false in
def cup0NatTrans' : .prod (functor R G 0) (functor R G 0) ⋙ tensor (ModuleCat R) ⟶
    tensor (Rep R G) ⋙ functor R G 0 where
  app MN := cup0' MN.1 MN.2
  naturality {MN MN'} := fun ⟨f1, f2⟩ ↦ by
    dsimp
    ext1
    simp only [ModuleCat.MonoidalCategory.tensorObj_carrier, ModuleCat.hom_comp,
      ModuleCat.hom_tensorHom]
    ext m n
    -- refine TensorProduct.ext' fun m n ↦ by
    simp only [cup0', ModuleCat.hom_ofHom, AlgebraTensorModule.curry_apply, restrictScalars_self,
      curry_apply, coe_comp, Function.comp_apply, map_tmul]
    conv_lhs => tactic => with_reducible convert lift.tmul _ _
    conv_lhs => tactic => with_reducible convert cup0_apply _ _ _ _
    conv_rhs => enter [2]; tactic => with_reducible convert lift.tmul _ _
    conv_rhs => enter [2]; tactic => with_reducible convert cup0_apply _ _ _ _
    rw [← map_id_tensor_comp_H0Iso_inv_apply (f1 ⊗ₘ f2)]
    congr 1
    ext1
    simp [Rep.invariantsFunctor]

variable (R G) in
abbrev cup0NatTrans :=
  Functor.curry.map <| @cup0NatTrans' R G _ _

abbrev cup0NatTransLeft := cup0NatTrans R G|>.app A

set_option backward.isDefEq.respectTransparency false in
@[simps]
def toTensorLeftNatTrans (F : Rep R G ⥤ ModuleCat R) (a : F.obj A) :
    F ⟶ (Functor.curry.obj (F.prod F ⋙ tensor (ModuleCat R))).obj A where
  app B := ModuleCat.ofHom <| TensorProduct.mk _ _ _ a
  naturality {X Y} f := by
    ext1
    simp only [Functor.curry_obj_obj_obj, Functor.comp_obj, Functor.prod_obj, tensor_obj,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom, Functor.curry_obj_obj_map, Functor.comp_map,
      Functor.prod_map, CategoryTheory.Functor.map_id, tensor_map, id_tensorHom,
      ModuleCat.hom_whiskerLeft]
    ext x
    simp [ModuleCat.MonoidalCategory.tensorObj_carrier, TensorProduct.mk_apply]

lemma cup0Left_map {X Y : Rep R G} (f : X ⟶ Y) :
    ((Functor.curry.obj ((functor R G 0).prod (functor R G 0) ⋙
      tensor (ModuleCat R))).obj A).map f = H0 A ◁ map (MonoidHom.id G) f 0 := by
  simp

lemma cup0Left_map' {X Y : Rep R G} (f : X ⟶ Y) :
    ((Functor.curry.obj (tensor (Rep R G) ⋙ functor R G 0)).obj A).map f
     = map (.id G) (A ◁ f) 0 := by
  simp

set_option backward.isDefEq.respectTransparency false in
lemma cup0Left_naturality {B1 B2 : Rep R G} (f : B1 ⟶ B2) :
    H0 A ◁ map (MonoidHom.id G) f 0 ≫ (cup0NatTransLeft A).app B2 =
    (cup0NatTransLeft A).app B1 ≫ map (.id G) (A ◁ f) 0 := by
  rw [← cup0Left_map, cup0NatTransLeft A|>.naturality, cup0Left_map']

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma groupCohomology.map_id_comp_H0Iso_inv {M N : Rep R G} (f : M ⟶ N) :
    (H0Iso M).inv ≫ map (MonoidHom.id G) f 0 = (Rep.invariantsFunctor R G).map f ≫
    (H0Iso N).inv := by
  apply_fun ((H0Iso M).hom ≫ · ≫ (H0Iso N).hom) using by aesop_cat
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  exact map_id_comp_H0Iso_hom _

lemma groupCohomology.map_id_comp_H0Iso_inv_apply {M N : Rep R G} (f : M ⟶ N) (x : M.ρ.invariants) :
    (map (MonoidHom.id G) f 0).hom ((H0Iso M).inv.hom x) =
    ((H0Iso N).inv.hom (((Rep.invariantsFunctor R G).map f).hom x)) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
  rw [groupCohomology.map_id_comp_H0Iso_inv]
  rfl

set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
lemma cup0Left_unitor {X : Rep R G} : (cup0NatTransLeft (𝟙_ (Rep R G))).app X ≫
    groupCohomology.map (.id G) (λ_ X).hom 0 =
    (H0IsoOfIsTrivial (Rep.trivial R G R)).hom ▷ H0 X ≫ (λ_ <| H0 X).hom := by
  ext1
  simp only [Functor.curry_obj_obj_obj, Functor.comp_obj, Functor.prod_obj, functor_obj, tensor_obj,
    ModuleCat.MonoidalCategory.tensorObj_carrier, Functor.curry_map_app_app, cup0NatTrans', cup0',
    ModuleCat.hom_comp, ModuleCat.hom_ofHom, H0IsoOfIsTrivial_hom, shortComplexH0,
    comp_whiskerRight, Category.assoc, ModuleCat.hom_hom_leftUnitor, ModuleCat.hom_whiskerRight]
  ext r x
  simp only [AlgebraTensorModule.curry_apply, restrictScalars_self, curry_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe]
  choose r' hr' using (LinearEquiv.surjective (H0Iso (Rep.trivial R G R)).symm.toLinearEquiv :
    Function.Surjective (H0Iso (Rep.trivial R G R)).inv.hom) r
  rw [← hr']
  erw [lift.tmul]
  conv_lhs => enter [2]; erw [cup0_apply]
  conv_rhs => enter [2, 2]; erw [rTensor_tmul, Iso.inv_hom_id_apply]
  conv_rhs => enter [2]; erw [rTensor_tmul]
  rw [lid_tmul, Submodule.subtype_apply]
  conv_lhs => enter [2, 2, 1, 2]; erw [Iso.inv_hom_id_apply]
  rw [map_id_comp_H0Iso_inv_apply (λ_ X).hom]
  apply_fun (fun x ↦ (H0Iso X).hom.hom x) using
    ConcreteCategory.injective_of_mono_of_preservesPullback _
  simp only
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.inv_hom_id,
    ModuleCat.hom_id, LinearMap.id_apply]
  ext1
  simp [Rep.invariantsFunctor]

abbrev cup0NatTransRight :=
  ((CategoryTheory.flipFunctor _ _ _).map (cup0NatTrans R G)).app B

lemma cup0Right_map {X Y : Rep R G} (f : X ⟶ Y) :
    (((flipFunctor (Rep R G) (Rep R G) (ModuleCat R)).obj (Functor.curry.obj
    ((functor R G 0).prod (functor R G 0) ⋙ tensor (ModuleCat R)))).obj B).map f =
    map (MonoidHom.id G) f 0 ▷ H0 B := by
  simp

lemma cup0Right_map' {X Y : Rep R G} (f : X ⟶ Y) :
    (((flipFunctor (Rep R G) (Rep R G) (ModuleCat R)).obj (Functor.curry.obj
    (tensor (Rep R G) ⋙ functor R G 0))).obj B).map f =
    map (.id G) (f ▷ B) 0 := by
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma cup0Right_naturality {A1 A2 : Rep R G} (f : A1 ⟶ A2) :
    map (.id G) f 0 ▷ H0 B ≫ (cup0NatTransRight B).app A2 =
    (cup0NatTransRight B).app A1 ≫ map (.id G) (f ▷ B) 0 := by
  rw [← cup0Right_map, cup0NatTransRight B|>.naturality, cup0Right_map']

lemma cup0Right_app_eq {A B : Rep R G} : (cup0NatTransRight B).app A =
  ((cup0NatTrans R G).app A).app B := rfl

lemma braiding_cup0Left (X Y : Rep R G) : (β_ (H0 X) (H0 Y)).hom ≫ (cup0NatTransLeft Y).app X =
    (cup0NatTransRight Y).app X ≫ map (.id G) (β_ X Y).hom 0 := by
  ext1
  simp only [ModuleCat.MonoidalCategory.tensorObj_carrier, Functor.curry_obj_obj_obj,
    Functor.comp_obj, tensor_obj, functor_obj, Functor.curry_map_app_app, cup0NatTrans', cup0',
    ModuleCat.hom_comp, flipFunctor_obj, Functor.flip_obj_obj,
    Functor.prod_obj, flipFunctor_map_app_app]
  ext x y
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, restrictScalars_self,
    TensorProduct.curry_apply, LinearMap.coe_comp, Function.comp_apply]
  change cup0 Y X y x = (map _ _ _).hom ((cup0 X Y) x y)
  conv_rhs => rw [cup0_apply]
  rw [cup0_apply, map_id_comp_H0Iso_inv_apply]
  congr 1

set_option backward.isDefEq.respectTransparency false in
lemma cup0Right_unitor {X : Rep R G} : H0 X ◁ (H0IsoOfIsTrivial (Rep.trivial R G R)).hom ≫
    (ρ_ (H0 X)).hom = (cup0NatTransRight (𝟙_ (Rep R G))).app X ≫
    groupCohomology.map (.id G) (ρ_ X).hom 0 := by
  have : H0 X ◁ (H0IsoOfIsTrivial (Rep.trivial R G R)).hom ≫ (ρ_ (H0 X)).hom =
    (β_ _ _).hom ≫ (H0IsoOfIsTrivial (Rep.trivial R G R)).hom ▷ H0 X ≫ (λ_ <| H0 X).hom := by
    rw [← BraidedCategory.braiding_naturality_right_assoc, ← braiding_leftUnitor]
    rfl
  rw [this, ← cup0Left_unitor, ← Category.assoc]
  erw [braiding_cup0Left X (Rep.trivial R G R)] -- `erw?` gives nothing
  rw [Category.assoc]
  erw [← groupCohomology.map_id_comp (β_ X _).hom (λ_ X).hom 0] -- `erw?` gives nothing here either
  rw [braiding_leftUnitor]
  rfl

open TensorProduct

theorem cup0_assoc (X Y Z : Rep R G) :
    ((cup0NatTrans R G).app X).app Y ▷ (functor R G 0).obj Z ≫
      ((cup0NatTrans R G).app (X ⊗ Y)).app Z ≫ (functor R G 0).map (α_ X Y Z).hom =
    (α_ ((functor R G 0).obj X) ((functor R G 0).obj Y) ((functor R G 0).obj Z)).hom ≫
      (functor R G 0).obj X ◁ ((cup0NatTrans R G).app Y).app Z ≫
      ((cup0NatTrans R G).app X).app (Y ⊗ Z) := by
  ext1
  simp only [Functor.curry_obj_obj_obj, Functor.comp_obj, Functor.prod_obj, functor_obj, tensor_obj,
    ModuleCat.MonoidalCategory.tensorObj_carrier, Functor.curry_map_app_app, cup0NatTrans', cup0',
    functor_map, ModuleCat.hom_comp, ModuleCat.hom_whiskerRight, ModuleCat.hom_whiskerLeft,
    ModuleCat.hom_hom_associator]
  conv_rhs =>
    erw [TensorProduct.lift_comp_map, LinearMap.comp_id]
  conv_lhs =>
    rw [LinearMap.comp_assoc]
    erw [TensorProduct.lift_comp_map, LinearMap.compl₂_id]
  refine TensorProduct.ext_threefold fun x y z ↦ ?_
  simp only [ModuleCat.MonoidalCategory.tensorObj_carrier, coe_comp, Function.comp_apply, lift.tmul,
    cup0_apply, Rep.tensor_V, Rep.tensor_ρ, LinearEquiv.coe_coe, assoc_tmul, compl₂_apply]
  erw [lift.tmul, lift.tmul]
  apply_fun (H0Iso (X ⊗ Y ⊗ Z)).hom.hom using (H0Iso (X ⊗ Y ⊗ Z)).toLinearEquiv.injective
  conv_rhs => erw [Iso.inv_hom_id_apply]
  simp only [Rep.tensor_V, Rep.tensor_ρ, Subtype.ext_iff]
  erw [groupCohomology.map_id_comp_H0Iso_hom_apply]
  change (_ ∘ₗ _) (((H0Iso ((X ⊗ Y) ⊗ Z)).inv ≫ (H0Iso ((X ⊗ Y) ⊗ Z)).hom).hom _) = _
  rw [Iso.inv_hom_id, ModuleCat.hom_id, LinearMap.id_apply, LinearMap.comp_apply,
    Submodule.subtype_apply]
  simp only [Rep.tensor_V, Rep.tensor_ρ, Rep.hom_hom_associator,
    Representation.TensorProduct.toLinearMap_assoc, LinearEquiv.coe_coe]
  erw [H0Iso_hom_cup0_coe, assoc_tmul]
  congr 1
  exact H0Iso_hom_cup0_coe _ _ _ _ |>.symm

set_option backward.isDefEq.respectTransparency false in
instance : Functor.LaxBraided (functor R G 0) where
  ε := H0IsoOfIsTrivial (Rep.trivial R G R) |>.inv
  μ A B := cup0NatTrans R G|>.app A|>.app B
  μ_natural_left f A := by
    simp only [functor_map, functor_obj]
    rw [← cup0Right_app_eq, cup0Right_naturality, cup0Right_app_eq]
  μ_natural_right {X Y} B f := by
    simp only [functor_map, functor_obj]
    rw [cup0Left_naturality]
  associativity X Y Z := cup0_assoc X Y Z
  left_unitality X := by
    simp only [functor_obj, functor_map]
    rw [cup0Left_unitor, ← comp_whiskerRight_assoc, Iso.inv_hom_id,
      id_whiskerRight, Category.id_comp]
  right_unitality X := by
    simp only [functor_obj, functor_map]
    rw [← cup0Right_app_eq, ← cup0Right_unitor, ← whiskerLeft_comp_assoc,
      Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
  braided X Y := by
    simp only [functor_obj, functor_map]
    rw [braiding_cup0Left X Y, ← cup0Right_app_eq]
