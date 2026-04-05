import CupProduct.Cohomology.AugmentationModule
import CupProduct.Cohomology.Functors.UpDown
-- import CupProduct.groupCoh.Rep
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

open CategoryTheory Rep.leftRegular MonoidalCategory

universe u

variable (R G : Type u) [CommRing R] [Group G]

noncomputable section

@[simps]
def upSES₀ [Fintype G] : ShortComplex (Rep R G) where
  X₁ := Rep.trivial R G R
  X₂ := Rep.leftRegular R G
  X₃ := coaug R G
  f := μ R G
  g := Limits.cokernel.π _
  zero := CategoryTheory.Limits.cokernel.condition _

lemma shortExact_upSES₀ [Fintype G] : (upSES₀ R G).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := Rep.mono_iff_injective (μ R G) |>.2 fun x y h ↦ by
    dsimp [μ] at x y h
    simpa using Finsupp.ext_iff.1 h 1
  epi_g := Limits.coequalizer.π_epi

@[simps]
def upSES₀_retract [Fintype G] : (G →₀ R) →ₗ[R] R where
  toFun f := f 1
  map_add' := by simp
  map_smul' := by simp

set_option backward.isDefEq.respectTransparency false in
def split_upSES₀_forget [Fintype G] : ((upSES₀ R G).map (forget₂ (Rep R G)
    (ModuleCat R))).Splitting :=
  .ofExactOfRetraction _ (.map (shortExact_upSES₀ R G).1 _)
    (ModuleCat.ofHom <| upSES₀_retract R G) (by ext; simp [upSES₀, μ]) <| by
  haveI := (shortExact_upSES₀ R G).3
  -- infer_instance
  -- simpa using Rep.instEpiModuleCatHom _
  sorry

open ShortComplex

def split_upSES' [Fintype G] : (((upSES₀ R G).map (tensorRight A)).map (forget₂ (Rep R G)
    (ModuleCat R))).Splitting := by
  rw [← map_comp, show (upSES₀ R G).map ((tensorRight A) ⋙ (forget₂ (Rep R G) (ModuleCat R))) =
    ((upSES₀ R G).map (forget₂ (Rep R G) (ModuleCat R))).map
    (tensorRight (ModuleCat.of R A.V)) by rfl]
  exact .map (split_upSES₀_forget R G) _

lemma exact_upSES' [Fintype G] : ((upSES₀ R G).map (tensorRight A)).Exact :=
  -- exact_iff_exact_map_forget₂ _|>.2 <| by
  -- change (((upSES₀ R G).map _).map (_ ⋙ _)).Exact
  -- rw [map_comp, ← exact_iff_exact_map_forget₂]
  -- exact split_upSES' R G |>.exact
  sorry

lemma shortExact_upSES' [Fintype G] : ((upSES₀ R G).map (tensorRight A)).ShortExact where
  exact := exact_upSES' R G
  mono_f := Functor.ReflectsMonomorphisms.reflects (F := (forget₂ (Rep R G) (ModuleCat R))) _
    (split_upSES' R G (A := A)).shortExact.mono_f
  epi_g := Functor.ReflectsEpimorphisms.reflects (F := (forget₂ (Rep.{u} R G) (ModuleCat R))) _
    (split_upSES' R G (A := A)).shortExact.epi_g

open Rep TensorProduct Limits Rep.dimensionShift

variable {R G}

@[simps]
def mapToTensorLinear {R G M : Type*} [CommRing R] [Group G] [Fintype G] [AddCommGroup M]
    [Module R M] : (G → M) →ₗ[R] (G →₀ R) ⊗[R] M where
  toFun f := ∑ g, Finsupp.single g⁻¹ 1 ⊗ₜ[R] f g
  map_add' := by simp [tmul_add, Finset.sum_add_distrib]
  map_smul' := by simp [Finset.smul_sum]

-- lemma mapToTensorLinear_coind [Fintype G] (A : Rep R G) (f : G → A.V) (g : G) :
--     mapToTensorLinear A (A.ρ.coind₁' g f) = ∑ x, Submodule.Quotient.mk
--       (leftRegular.of x) ⊗ₜ[R] (A.ρ g) (f (x * g)) := by
--   simp [mapToTensorLinear, Representation.coind₁']

set_option backward.isDefEq.respectTransparency false in
lemma π_comp_forgetCokernelIso {A B : Rep R G} (f : A ⟶ B) :
    cokernel.π f.toModuleCatHom ≫ (forgetCokernelIso f).inv = (cokernel.π f).toModuleCatHom := by
  simp [forgetCokernelIso]

@[simps! toLinearMap]
def Representation.mapToTensor {G : Type v} [Group G] {M : Type w} [AddCommGroup M] [Module R M]
    [Fintype G] (ρ : Representation R G M) :
    ρ.coind₁'.IntertwiningMap (Representation.leftRegular R G |>.tprod ρ) where
  __ := mapToTensorLinear
  isIntertwining' g := by ext; simpa using Finset.sum_equiv (Equiv.mulRight g) (by simp) (by simp)

abbrev mapToTensor [Fintype G] (A : Rep R G) : coind₁'.obj A ⟶ Rep.leftRegular R G ⊗ A :=
  Rep.ofHom A.ρ.mapToTensor

def upToTensor [Fintype G] (A : Rep R G) : up.obj A ⟶ coaug R G ⊗ A :=
  haveI : Epi (upSES A).g := coequalizer.π_epi
  (shortExact_upSES A).1.desc (mapToTensor A ≫ (cokernel.π _ ▷ A)) <| by
  ext m
  simp only [tensor_V, upSES_X₁, tensor_ρ, upSES_X₂, coind₁'_obj, upSES_f, coind₁'_ι_app,
    Rep.hom_comp, hom_whiskerRight, hom_ofHom, Representation.IntertwiningMap.comp_toLinearMap,
    Representation.IntertwiningMap.toLinearMap_rTensor, Representation.mapToTensor_toLinearMap,
    LinearMap.coe_comp, Function.comp_apply, mapToTensorLinear_apply,
    Representation.coind₁'_ι_apply, Function.const_apply, ← sum_tmul, LinearMap.rTensor_tmul,
    Representation.IntertwiningMap.coe_toLinearMap, zero_hom,
    Representation.IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply]
  rw [← one_smul R (∑ a, Finsupp.single a⁻¹ (1 : R))]
  rw [← Finset.sum_equiv (Equiv.inv G) (f := fun i ↦ Finsupp.single i 1)
    (g := fun i ↦ Finsupp.single i⁻¹ 1) (s := Finset.univ) (t := Finset.univ) (by simp) (by simp),
    ← μ_apply, cokernel.condition_apply]
  simp

@[simps]
def tensorToFun'' {R G : Type*} (M : Type*) [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    (f : G →₀ R) : M →ₗ[R] (G → M) where
  toFun a := fun g ↦ (f g⁻¹) • a
  map_add' := by simp [Pi.add_def]
  map_smul' := by simp [Pi.smul_def, ← smul_assoc, mul_comm]

@[simps]
def tensorToFun' {R G : Type*} (M : Type*) [CommRing R] [Group G] [AddCommGroup M] [Module R M] :
    (G →₀ R) →ₗ[R] M →ₗ[R] (G → M) where
  toFun := tensorToFun'' M
  map_add' _ _ := by ext; simp [add_smul]
  map_smul' _ _ := by ext; simp [mul_smul]

@[simps! toLinearMap]
def Representation.tensorToFun {R G M : Type*} [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    (ρ : Representation R G M) : (Representation.leftRegular R G |>.tprod ρ).IntertwiningMap
    ρ.coind₁' where
  __ := lift <| tensorToFun' M
  isIntertwining' g := by ext; simp [Finsupp.single]

abbrev tensorToFun (A : Rep R G) : leftRegular R G ⊗ A ⟶ coind₁'.obj A :=
  Rep.ofHom A.ρ.tensorToFun

-- instance [Fintype G] (C : Rep R G) : Epi ((upSES₀ R G).map (tensorRight C)).g := by
--   simp only [upSES₀, map_X₂, Functor.flip_obj_obj, curriedTensor_obj_obj, map_X₃, map_g,
--     Functor.flip_obj_map, curriedTensor_map_app, Rep.epi_iff_surjective, Action.tensorObj_V,
--     Action.whiskerRight_hom]
--   change Function.Surjective (ModuleCat.Hom.hom _)
--   rw [ModuleCat.hom_whiskerRight]
--   exact LinearMap.rTensor_surjective _ (Rep.epi_iff_surjective _|>.1 coequalizer.π_epi)

def coaugTensorToUp [Fintype G] (A : Rep R G) : coaug R G ⊗ A ⟶ up.obj A :=
  haveI : Epi ((upSES₀ R G).map (tensorRight A)).g := (shortExact_upSES' R G).3
  (exact_upSES' R G).desc (tensorToFun A ≫ cokernel.π _) <| by
  sorry
  -- ext : 2
  -- simp only [upSES₀, map_X₁, Functor.flip_obj_obj, curriedTensor_obj_obj, Action.tensorObj_V,
  --   up_obj, Functor.id_obj, coind₁'_obj, map_X₂, map_f, Functor.flip_obj_map, curriedTensor_map_app,
  --   Action.comp_hom, Action.whiskerRight_hom, ModuleCat.hom_comp, ModuleCat.hom_whiskerRight,
  --   Action.zero_hom, ModuleCat.hom_zero]
  -- apply TensorProduct.ext' fun (r : R) a ↦ ?_
  -- simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply]
  -- conv_lhs => enter [2, 2]; erw [LinearMap.rTensor_tmul]
  -- simp only [tensorToFun_hom, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
  --   Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.hom_ofHom]
  -- erw [lift.tmul]
  -- simp only [tensorToFun'_apply]
  -- rw [← π_comp_forgetCokernelIso]
  -- simp only [coind₁'_ι_app_hom, Functor.id_obj, coind₁'_obj,
  --   ← ModuleCat.range_mkQ_cokernelIsoRangeQuotient_inv, ModuleCat.hom_ofHom, Category.assoc,
  --   ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
  -- suffices @Submodule.Quotient.mk R (G → ↑A.V) _ _ _ Representation.coind₁'_ι.range
  --   ((tensorToFun'' A ((ModuleCat.Hom.hom (μ R G).hom) r)) a) = 0 by simp [this]
  -- simp only [μ, map_sum, LinearMap.lsmul_flip_apply, ModuleCat.hom_ofHom, LinearMap.coe_sum,
  --   Finset.sum_apply, LinearMap.toSpanSingleton_apply, Submodule.Quotient.mk_eq_zero,
  --   LinearMap.mem_range, funext_iff, Representation.coind₁'_ι_apply, Function.const_apply,
  --   tensorToFun''_apply, Finsupp.coe_finset_sum, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  -- exact ⟨r • a, fun g ↦ by simp [← Finset.mul_sum, leftRegular.of]⟩

lemma tensorToFun_mapToTensor [Fintype G] (A : Rep R G) : mapToTensor A ≫ tensorToFun A = 𝟙 _ := by
  -- ext : 2
  -- simp only [coind₁'_obj, Action.comp_hom, Action.tensorObj_V, mapToTensor_hom,
  --   Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
  --   Action.FunctorCategoryEquivalence.functor_obj_obj, tensorToFun_hom, ModuleCat.hom_comp,
  --   ModuleCat.hom_ofHom, Action.id_hom, ModuleCat.hom_id,
  --   ModuleCat.MonoidalCategory.tensorObj_carrier]
  -- ext f i
  -- simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
  --   (mapToTensorLinear_apply), map_sum, lift.tmul, tensorToFun'_apply,
  --   Finset.sum_apply, tensorToFun''_apply]
  -- classical
  -- conv_lhs => enter [2, x]; rw [leftRegular.of_apply]
  -- simp
  sorry

lemma upToTensor_comp_inv [Fintype G] (A : Rep R G) : upToTensor A ≫ coaugTensorToUp A = 𝟙 _ := by
  -- simp only [up_obj, Functor.id_obj, coind₁'_obj, upToTensor, coaugTensorToUp, map_X₂,
  --   Functor.flip_obj_obj, curriedTensor_obj_obj]
  -- rw [← cancel_epi (up.π A), ← Category.assoc]
  -- change ((upSES A).g ≫ _) ≫ _ = _
  -- rw [Exact.g_desc]
  -- simp only [upSES_X₂, coind₁'_obj, Category.assoc, up_obj, Functor.id_obj, coequalizer_as_cokernel,
  --   Category.comp_id]
  -- rw [show cokernel.π (μ R G) ▷ A = ((upSES₀ R G).map (tensorRight A)).g by rfl, Exact.g_desc,
  --   ← Category.assoc, tensorToFun_mapToTensor]
  -- simp
  sorry

lemma mapToTensor_tensorToFun [Fintype G] (A : Rep R G) : tensorToFun A ≫ mapToTensor A = 𝟙 _ := by
  -- ext : 2
  -- simp only [Action.tensorObj_V, coind₁'_obj, Action.comp_hom, tensorToFun_hom,
  --   Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
  --   Action.FunctorCategoryEquivalence.functor_obj_obj, mapToTensor_hom, ModuleCat.hom_comp,
  --   ModuleCat.hom_ofHom, Action.id_hom, ModuleCat.hom_id]
  -- refine TensorProduct.ext' fun (f : G →₀ R) a ↦ ?_
  -- simp only [LinearMap.coe_comp, Function.comp_apply, lift.tmul, tensorToFun'_apply]
  -- erw [mapToTensorLinear_apply]
  -- classical
  -- simp only [tensorToFun''_apply, tmul_smul, smul_tmul', ← sum_tmul]
  -- rw [Finset.sum_equiv (Equiv.inv G) (t := Finset.univ) (g := fun g ↦ (f g) • leftRegular.of g)
  --   (by simp) (by simp)]
  -- simp [of_def, LinearMap.id]
  sorry

@[simps]
def coindIsoTensor [Fintype G] (A : Rep R G) : coind₁'.obj A ≅ leftRegular R G ⊗ A where
  hom := mapToTensor A
  inv := tensorToFun A
  hom_inv_id := tensorToFun_mapToTensor A
  inv_hom_id := mapToTensor_tensorToFun A

def coindIsoTensorFunctor [Fintype G] : coind₁' ≅ tensorLeft (leftRegular R G) :=
  NatIso.ofComponents coindIsoTensor fun {X Y} f ↦ by
    simp only [coind₁'_obj, curriedTensor_obj_obj, coindIsoTensor_hom, curriedTensor_obj_map]
    ext (x : G → X.V)
    simp [coind₁', ModuleCat.hom_whiskerLeft, ModuleCat.MonoidalCategory.tensorObj_carrier,
      (mapToTensorLinear_apply)]

@[reassoc]
lemma mapToTensor_naturality [Fintype G] {X Y : Rep R G} (f : X ⟶ Y) :
    coind₁'.map f ≫ mapToTensor Y = mapToTensor X ≫ leftRegular R G ◁ f :=
  @coindIsoTensorFunctor R G _ _ _ |>.hom.naturality f

set_option linter.unusedFintypeInType false

@[reassoc]
lemma tensorToFun_naturality [Fintype G] {X Y : Rep R G} (f : X ⟶ Y) :
    leftRegular R G ◁ f ≫ tensorToFun Y = tensorToFun X ≫ coind₁'.map f :=
  @coindIsoTensorFunctor R G _ _ _ |>.inv.naturality f

lemma inv_comp_upToTensor [Fintype G] (A : Rep R G) : coaugTensorToUp A ≫ upToTensor A = 𝟙 _ := by
  -- haveI : Epi ((upSES₀ R G).map (tensorRight A)).g := (shortExact_upSES' R G).3
  -- simp only [up_obj, Functor.id_obj, coind₁'_obj, coaugTensorToUp, map_X₂, Functor.flip_obj_obj,
  --   curriedTensor_obj_obj, upToTensor, upSES_X₂]
  -- rw [← cancel_epi ((upSES₀ R G).map (tensorRight A)).g, ← Category.assoc, Exact.g_desc]
  -- simp only [map_X₂, Functor.flip_obj_obj, curriedTensor_obj_obj, Category.assoc, map_X₃, map_g,
  --   Functor.flip_obj_map, curriedTensor_map_app]
  -- change _ ≫ (upSES A).g ≫ _ = _
  -- rw [Exact.g_desc]
  -- simp only [upSES_X₂, coind₁'_obj, ← Category.assoc, mapToTensor_tensorToFun, upSES₀_X₃, upSES₀_g,
  --   Category.comp_id]
  -- rfl
  sorry

@[simps]
def upIsoCoaugTensor [Fintype G] (A : Rep R G) : up.obj A ≅ coaug R G ⊗ A where
  hom := upToTensor A
  inv := coaugTensorToUp A
  hom_inv_id := upToTensor_comp_inv A
  inv_hom_id := inv_comp_upToTensor A

def upIsoCoaugTensorFunctor [Fintype G] : up ≅ tensorLeft (coaug R G) :=
  NatIso.ofComponents upIsoCoaugTensor fun {X Y} f ↦ by
    simp only [curriedTensor_obj_obj, up_map, upIsoCoaugTensor_hom,
      upToTensor, upSES_X₂, curriedTensor_obj_map]
    rw [← cancel_epi (up.π X), cokernel.π_desc_assoc, Category.assoc]
    change _ ≫ (upSES Y).g ≫ _ = (upSES X).g ≫ _
    rw [Exact.g_desc, Exact.g_desc_assoc, mapToTensor_naturality_assoc,
      Category.assoc, whisker_exchange]

@[reassoc]
lemma upToTensor_naturality [Fintype G] {X Y : Rep R G} (f : X ⟶ Y) :
    up.map f ≫ upToTensor Y = upToTensor X ≫ coaug R G ◁ f :=
  upIsoCoaugTensorFunctor (R := R) (G := G)|>.hom.naturality f

@[reassoc]
lemma coaugTensorToUp_naturality [Fintype G] {X Y : Rep R G} (f : X ⟶ Y) :
    (coaug R G) ◁ f ≫ coaugTensorToUp Y = coaugTensorToUp X ≫ up.map f :=
  upIsoCoaugTensorFunctor (R := R) (G := G)|>.inv.naturality f

def coindTensor [Fintype G] (A B : Rep R G) : coind₁'.obj A ⊗ B ≅ coind₁'.obj (A ⊗ B) :=
  MonoidalCategory.whiskerRightIso (coindIsoTensor A) _ ≪≫ α_ _ _ _ ≪≫
    (coindIsoTensor (A ⊗ B)).symm

set_option backward.isDefEq.respectTransparency false in
def coindTensorFunc [Fintype G] (B : Rep R G) :
    coind₁' ⋙ tensorRight B ≅ tensorRight B ⋙ coind₁' :=
  NatIso.ofComponents (fun A ↦ coindTensor A B) fun {X Y} f ↦ by
    dsimp [coindTensor]
    rw [← comp_whiskerRight_assoc, mapToTensor_naturality f, comp_whiskerRight_assoc,
      associator_naturality_middle_assoc, tensorToFun_naturality,
      Category.assoc, Category.assoc]

@[reassoc]
lemma coindTensor_naturality [Fintype G] (B : Rep R G) {X Y : Rep R G} (f : X ⟶ Y) :
    coind₁'.map f ▷ B ≫ (coindTensor Y B).hom = (coindTensor X B).hom ≫ coind₁'.map (f ▷ B) :=
  coindTensorFunc B|>.hom.naturality f

abbrev coindTensor' [Fintype G] (A B : Rep R G) : A ⊗ coind₁'.obj B ≅ coind₁'.obj (A ⊗ B) :=
  (β_ _ _) ≪≫ coindTensor B A ≪≫ coind₁'.mapIso (β_ _ _)

def upTensor [Fintype G] (A B : Rep R G) : up.obj A ⊗ B ≅ up.obj (A ⊗ B) :=
  MonoidalCategory.whiskerRightIso (upIsoCoaugTensor A) _ ≪≫ α_ _ _ _ ≪≫
    (upIsoCoaugTensor (A ⊗ B)).symm

def upTensorFunc [Fintype G] (B : Rep R G) : up ⋙ tensorRight B ≅ tensorRight B ⋙ up :=
  NatIso.ofComponents (fun A ↦ upTensor A B) fun {X Y} f ↦ by
    dsimp [-up_obj, -up_map, upTensor]
    rw [← comp_whiskerRight_assoc, upToTensor_naturality, comp_whiskerRight_assoc,
      associator_naturality_middle_assoc, coaugTensorToUp_naturality,
      Category.assoc, Category.assoc]

lemma upTensor_naturality [Fintype G] (B : Rep R G) {X Y : Rep R G} (f : X ⟶ Y) :
    up.map f ▷ B ≫ (upTensor Y B).hom = (upTensor X B).hom ≫ up.map (f ▷ B) :=
  upTensorFunc B|>.hom.naturality f

abbrev upTensor' [Fintype G] (A B : Rep R G) : A ⊗ up.obj B ≅ up.obj (A ⊗ B) :=
  (β_ _ _) ≪≫ upTensor B A ≪≫ up.mapIso (β_ _ _)

@[reassoc]
lemma upTensor_coind_comm [Fintype G] (A B : Rep R G) :
     up.π A ▷ B ≫ (upTensor A B).hom = (coindTensor A B).hom ≫ up.π (A ⊗ B) := by
  -- simp only [coequalizer_as_cokernel, Functor.id_obj, upTensor, Iso.trans_hom, whiskerRightIso_hom,
  --   upIsoCoaugTensor_hom, Iso.symm_hom, upIsoCoaugTensor_inv, coindTensor, coindIsoTensor_hom,
  --   coindIsoTensor_inv, Category.assoc]
  -- rw [← comp_whiskerRight_assoc, upToTensor]
  -- change ((upSES A).g ≫ _) ▷ B ≫ _ = _
  -- rw [Exact.g_desc, comp_whiskerRight_assoc]
  -- nth_rw 2 [← Category.assoc]
  -- rw [associator_naturality_left, Category.assoc, coaugTensorToUp]
  -- change _ ≫ _ ≫ ((upSES₀ R G).map (tensorRight (A ⊗ B))).g ≫ _ = _
  -- rw [Exact.g_desc]
  sorry

lemma upTensor_coind_comm' [Fintype G] (A B : Rep R G) :
    A ◁ up.π B ≫ (upTensor' A B).hom = (coindTensor' A B).hom ≫ up.π (A ⊗ B) := by
  dsimp only [upTensor', coindTensor', Iso.trans_hom]
  rw [BraidedCategory.braiding_naturality_right_assoc, upTensor_coind_comm_assoc]
  simp

-- TODO : make a shortcomplex iso between upSES (functor version) and (upSES₀ functor)
