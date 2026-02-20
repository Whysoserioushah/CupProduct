import CupProduct.Cohomology.AugmentationModule
import CupProduct.Cohomology.Functors.UpDown
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
  zero := by ext1; simp

lemma shortExact_upSES₀ [Fintype G] : (upSES₀ R G).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := Rep.mono_iff_injective (μ R G) |>.2 fun x y h ↦ by
    dsimp [μ] at x y h
    simpa [of] using Finsupp.ext_iff.1 h 1
  epi_g := Limits.coequalizer.π_epi

@[simps]
def upSES₀_retract [Fintype G] : (G →₀ R) →ₗ[R] R where
  toFun f := f 1
  map_add' := by simp
  map_smul' := by simp

def split_upSES₀_forget [Fintype G] : ((upSES₀ R G).map (forget₂ (Rep R G)
    (ModuleCat R))).Splitting :=
  .ofExactOfRetraction _ (.map (shortExact_upSES₀ R G).1 _)
    (ModuleCat.ofHom <| upSES₀_retract R G) (by ext; simp [upSES₀, μ, of]) <| by
  haveI := (shortExact_upSES₀ R G).3
  simpa using Rep.instEpiModuleCatHom _

instance : HasForget₂ (Rep R G) Ab := .trans (Rep R G) (ModuleCat R) Ab

instance : (forget₂ (Rep R G) Ab).Additive :=
  inferInstanceAs (_ ⋙ _).Additive

instance : (forget₂ (Rep R G) Ab).PreservesHomology :=
  { preservesKernels _ _ _ := Limits.comp_preservesLimit _ _
    preservesCokernels _ _ _:= Limits.comp_preservesColimit _ _ }

variable (A : Rep R G) in
#synth (tensorRight A).Additive
open ShortComplex

def split_upSES' [Fintype G] : (((upSES₀ R G).map (tensorRight A)).map (forget₂ (Rep R G)
    (ModuleCat R))).Splitting := by
  rw [← map_comp, show (upSES₀ R G).map ((tensorRight A) ⋙ (forget₂ (Rep R G) (ModuleCat R))) =
    ((upSES₀ R G).map (forget₂ (Rep R G) (ModuleCat R))).map (tensorRight A.V) by rfl]
  exact .map (split_upSES₀_forget R G) _

lemma exact_upSES' [Fintype G] : ((upSES₀ R G).map (tensorRight A)).Exact :=
  exact_iff_exact_map_forget₂ _|>.2 <| by
  change (((upSES₀ R G).map _).map (_ ⋙ _)).Exact
  rw [map_comp, ← exact_iff_exact_map_forget₂]
  exact split_upSES' R G |>.exact

lemma shortExact_upSES' [Fintype G] : ((upSES₀ R G).map (tensorRight A)).ShortExact where
  exact := exact_upSES' R G
  mono_f := Functor.ReflectsMonomorphisms.reflects (F := (forget₂ (Rep R G) (ModuleCat R))) _
    (split_upSES' R G (A := A)).shortExact.mono_f
  epi_g := Functor.ReflectsEpimorphisms.reflects (F := (forget₂ (Rep R G) (ModuleCat R))) _
    (split_upSES' R G (A := A)).shortExact.epi_g

open Rep TensorProduct Limits Rep.dimensionShift

variable {R G}

@[simps]
def mapToTensorLinear [Fintype G] (A : Rep R G) : (G → A.V) →ₗ[R]
    (leftRegular R G).V ⊗[R] A.V where
  toFun f := ∑ g, (leftRegular.of g⁻¹) ⊗ₜ f g
  map_add' := by simp [tmul_add, Finset.sum_add_distrib]
  map_smul' := by simp [Finset.smul_sum]

-- lemma mapToTensorLinear_coind [Fintype G] (A : Rep R G) (f : G → A.V) (g : G) :
--     mapToTensorLinear A (A.ρ.coind₁' g f) = ∑ x, Submodule.Quotient.mk
--       (leftRegular.of x) ⊗ₜ[R] (A.ρ g) (f (x * g)) := by
--   simp [mapToTensorLinear, Representation.coind₁']

lemma π_comp_forgetCokernelIso {A B : Rep R G} (f : A ⟶ B) :
    cokernel.π f.hom ≫ (forgetCokernelIso f).inv = (cokernel.π f).hom := by
  simp [forgetCokernelIso]

@[simps]
def mapToTensor [Fintype G] (A : Rep R G) : coind₁'.obj A ⟶ Rep.leftRegular R G ⊗ A where
  hom := ModuleCat.ofHom (mapToTensorLinear A) --≫ ((cokernel.π (μ R G)).hom ⊗ₘ 𝟙 A.V)
  comm g := by
    ext : 1
    simp only [coind₁'_obj, Action.tensorObj_V, RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe,
      Function.comp_apply, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    ext f
    simp only [ModuleCat.MonoidalCategory.tensorObj_carrier, LinearMap.coe_comp,
      Function.comp_apply, (mapToTensorLinear_apply), map_sum, ModuleCat.endRingEquiv,
      RingEquiv.symm_mk, RingEquiv.coe_mk, Equiv.coe_fn_mk, ModuleCat.hom_ofHom,
      Representation.coind₁'_apply_apply]
    rw [Action.tensor_ρ, ModuleCat.hom_tensorHom]
    simp only [ModuleCat.endRingEquiv, RingEquiv.symm_mk, RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe,
      RingEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply, ModuleCat.hom_ofHom, ρ_hom,
      map_tmul, of_def, Representation.ofMulAction_single]
    change ∑ x, leftRegular.of _ ⊗ₜ _ = ∑ x, leftRegular.of _ ⊗ₜ[R] (A.ρ g) (f x)
    simp only [smul_eq_mul]
    conv_lhs => enter [2, x] ; rw [show x⁻¹ = ((x * g) * g⁻¹)⁻¹ by group]
    rw [Finset.sum_equiv (s := Finset.univ) (t := Finset.univ)
      (g := fun x ↦ (leftRegular.of (x * g⁻¹)⁻¹) ⊗ₜ[R] (A.ρ g) (f x)) (Equiv.mulRight g) (by
      simp) (fun i _ ↦ by simp)]
    simp

lemma mapToLinear_apply [Fintype G] (A : Rep R G) (f : G → A.V) :
    mapToTensorLinear A f = ∑ x, (leftRegular.of x⁻¹) ⊗ₜ[R] f x := by
  simp [mapToTensorLinear]

def upToTensor [Fintype G] (A : Rep R G) : up.obj A ⟶ coaug R G ⊗ A :=
  haveI : Epi (upSES A).g := coequalizer.π_epi
  (shortExact_upSES A).1.desc (mapToTensor A ≫ (cokernel.π _ ▷ A)) <| by
  ext : 2
  simp only [upSES_X₁, Action.tensorObj_V, upSES_X₂, coind₁'_obj, upSES_f, Action.comp_hom,
    coind₁'_ι_app_hom, Functor.id_obj, mapToTensor_hom, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Action.whiskerRight_hom, ModuleCat.hom_comp, ModuleCat.hom_ofHom, Action.zero_hom,
    ModuleCat.hom_zero, ModuleCat.MonoidalCategory.tensorObj_carrier]
  ext a
  simp only [ModuleCat.hom_whiskerRight, Representation.coind₁'_ι, LinearMap.coe_comp,
    LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  change LinearMap.rTensor _ _ (∑ _, _) = _
  simp only [Function.const_apply, map_sum, LinearMap.rTensor_tmul]
  rw [← sum_tmul, ← map_sum]
  convert zero_tmul (coaug R G).V a using 2
  rw [← π_comp_forgetCokernelIso]
  simp only [← ModuleCat.range_mkQ_cokernelIsoRangeQuotient_inv,
    Category.assoc, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
  suffices @Submodule.Quotient.mk R (G →₀ R) _ _ _ (μ R G).hom.hom.range
    (∑ x, leftRegular.of x⁻¹) = 0 by simp [this]
  rw [Finset.sum_equiv (Equiv.inv G) (t := Finset.univ)
    (g := fun g ↦ leftRegular.of g) (by simp) (by simp)]
  simpa using ⟨1, μ_one R G⟩

@[simps]
def tensorToFun'' (A : Rep R G) (f : G →₀ R) : A →ₗ[R] (G → A.V) where
  toFun a := fun g ↦ (f g⁻¹) • a
  map_add' := by simp [Pi.add_def]
  map_smul' := by simp [Pi.smul_def, ← smul_assoc, mul_comm]

@[simps]
def tensorToFun' (A : Rep R G) : (G →₀ R) →ₗ[R] A →ₗ[R] (G → A.V) where
  toFun := tensorToFun'' A
  map_add' _ _ := by ext; simp [add_smul]
  map_smul' _ _ := by ext; simp [mul_smul]

@[simps]
def tensorToFun (A : Rep R G) : leftRegular R G ⊗ A ⟶ coind₁'.obj A where
  hom := ModuleCat.ofHom <| lift (tensorToFun' A)
  comm g := by
    ext1
    simp only [Action.tensorObj_V, coind₁'_obj, Equivalence.symm_inverse,
      Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom, RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe,
      Function.comp_apply]
    rw [Action.tensor_ρ, ModuleCat.hom_tensorHom]
    simp only [ModuleCat.endRingEquiv, RingEquiv.symm_mk, RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe,
      RingEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply, ModuleCat.hom_ofHom, ρ_hom]
    refine TensorProduct.ext' fun f a ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, lift.tmul, tensorToFun'_apply]

    conv_lhs => enter [2]; erw [map_tmul]
    erw [lift.tmul]
    ext
    simp

instance [Fintype G] (C : Rep R G) : Epi ((upSES₀ R G).map (tensorRight C)).g := by
  simp only [upSES₀, map_X₂, Functor.flip_obj_obj, curriedTensor_obj_obj, map_X₃, map_g,
    Functor.flip_obj_map, curriedTensor_map_app, Rep.epi_iff_surjective, Action.tensorObj_V,
    Action.whiskerRight_hom]
  change Function.Surjective (ModuleCat.Hom.hom _)
  rw [ModuleCat.hom_whiskerRight]
  exact LinearMap.rTensor_surjective _ (Rep.epi_iff_surjective _|>.1 coequalizer.π_epi)

def coaugTensorToUp [Fintype G] (A : Rep R G) : coaug R G ⊗ A ⟶ up.obj A :=
  (exact_upSES' R G).desc (tensorToFun A ≫ cokernel.π _) <| by
  ext : 2
  simp only [upSES₀, map_X₁, Functor.flip_obj_obj, curriedTensor_obj_obj, Action.tensorObj_V,
    up_obj, Functor.id_obj, coind₁'_obj, map_X₂, map_f, Functor.flip_obj_map, curriedTensor_map_app,
    Action.comp_hom, Action.whiskerRight_hom, ModuleCat.hom_comp, ModuleCat.hom_whiskerRight,
    Action.zero_hom, ModuleCat.hom_zero]
  apply TensorProduct.ext' fun (r : R) a ↦ ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply]
  conv_lhs => enter [2, 2]; erw [LinearMap.rTensor_tmul]
  simp only [tensorToFun_hom, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.hom_ofHom]
  erw [lift.tmul]
  simp only [tensorToFun'_apply]
  rw [← π_comp_forgetCokernelIso]
  simp only [coind₁'_ι_app_hom, Functor.id_obj, coind₁'_obj,
    ← ModuleCat.range_mkQ_cokernelIsoRangeQuotient_inv, ModuleCat.hom_ofHom, Category.assoc,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
  suffices @Submodule.Quotient.mk R (G → ↑A.V) _ _ _ Representation.coind₁'_ι.range
    ((tensorToFun'' A ((ModuleCat.Hom.hom (μ R G).hom) r)) a) = 0 by simp [this]
  simp only [μ, map_sum, LinearMap.lsmul_flip_apply, ModuleCat.hom_ofHom, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.toSpanSingleton_apply, Submodule.Quotient.mk_eq_zero,
    LinearMap.mem_range, funext_iff, Representation.coind₁'_ι_apply, Function.const_apply,
    tensorToFun''_apply, Finsupp.coe_finset_sum, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  exact ⟨r • a, fun g ↦ by simp [← Finset.mul_sum, leftRegular.of]⟩

lemma tensorToFun_mapToTensor [Fintype G] (A : Rep R G) : mapToTensor A ≫ tensorToFun A = 𝟙 _ := by
  ext : 2
  simp only [coind₁'_obj, Action.comp_hom, Action.tensorObj_V, mapToTensor_hom,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, tensorToFun_hom, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom, Action.id_hom, ModuleCat.hom_id,
    ModuleCat.MonoidalCategory.tensorObj_carrier]
  ext f i
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
    (mapToTensorLinear_apply), map_sum, lift.tmul, tensorToFun'_apply,
    Finset.sum_apply, tensorToFun''_apply]
  classical
  conv_lhs => enter [2, x]; rw [leftRegular.of_apply]
  simp

lemma upToTensor_comp_inv [Fintype G] (A : Rep R G) : upToTensor A ≫ coaugTensorToUp A = 𝟙 _ := by
  simp only [up_obj, Functor.id_obj, coind₁'_obj, upToTensor, coaugTensorToUp, map_X₂,
    Functor.flip_obj_obj, curriedTensor_obj_obj]
  rw [← cancel_epi (up.π A), ← Category.assoc]
  change ((upSES A).g ≫ _) ≫ _ = _
  rw [Exact.g_desc]
  simp only [upSES_X₂, coind₁'_obj, Category.assoc, up_obj, Functor.id_obj, coequalizer_as_cokernel,
    Category.comp_id]
  rw [show cokernel.π (μ R G) ▷ A = ((upSES₀ R G).map (tensorRight A)).g by rfl, Exact.g_desc,
    ← Category.assoc, tensorToFun_mapToTensor]
  simp

lemma mapToTensor_tensorToFun [Fintype G] (A : Rep R G) : tensorToFun A ≫ mapToTensor A = 𝟙 _ := by
  ext : 2
  simp only [Action.tensorObj_V, coind₁'_obj, Action.comp_hom, tensorToFun_hom,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, mapToTensor_hom, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom, Action.id_hom, ModuleCat.hom_id]
  refine TensorProduct.ext' fun (f : G →₀ R) a ↦ ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, lift.tmul, tensorToFun'_apply]
  erw [mapToTensorLinear_apply]
  classical
  simp only [tensorToFun''_apply, tmul_smul, smul_tmul', ← sum_tmul]
  rw [Finset.sum_equiv (Equiv.inv G) (t := Finset.univ) (g := fun g ↦ (f g) • leftRegular.of g)
    (by simp) (by simp)]
  simp [of_def, LinearMap.id]

@[simps]
def coindIsoTensor [Fintype G] (A : Rep R G) : coind₁'.obj A ≅ leftRegular R G ⊗ A where
  hom := mapToTensor A
  inv := tensorToFun A
  hom_inv_id := tensorToFun_mapToTensor A
  inv_hom_id := mapToTensor_tensorToFun A

lemma inv_comp_upToTensor [Fintype G] (A : Rep R G) : coaugTensorToUp A ≫ upToTensor A = 𝟙 _ := by
  haveI : Epi ((upSES₀ R G).map (tensorRight A)).g := by
    simp only [upSES₀, map_X₂, Functor.flip_obj_obj, curriedTensor_obj_obj, map_X₃, map_g,
      Functor.flip_obj_map, curriedTensor_map_app, Rep.epi_iff_surjective, Action.tensorObj_V,
      Action.whiskerRight_hom]
    change Function.Surjective (ModuleCat.Hom.hom _)
    rw [ModuleCat.hom_whiskerRight]
    exact LinearMap.rTensor_surjective _ (Rep.epi_iff_surjective _|>.1 coequalizer.π_epi)
  simp only [up_obj, Functor.id_obj, coind₁'_obj, coaugTensorToUp, map_X₂, Functor.flip_obj_obj,
    curriedTensor_obj_obj, upToTensor, upSES_X₂]
  rw [← cancel_epi ((upSES₀ R G).map (tensorRight A)).g, ← Category.assoc, Exact.g_desc]
  simp only [map_X₂, Functor.flip_obj_obj, curriedTensor_obj_obj, Category.assoc, map_X₃, map_g,
    Functor.flip_obj_map, curriedTensor_map_app]
  change _ ≫ (upSES A).g ≫ _ = _
  rw [Exact.g_desc]
  simp only [upSES_X₂, coind₁'_obj, ← Category.assoc, mapToTensor_tensorToFun, upSES₀_X₃, upSES₀_g,
    Category.comp_id]
  rfl

@[simps]
def upIsoCoaugTensor [Fintype G] (A : Rep R G) : up.obj A ≅ coaug R G ⊗ A where
  hom := upToTensor A
  inv := coaugTensorToUp A
  hom_inv_id := upToTensor_comp_inv A
  inv_hom_id := inv_comp_upToTensor A

def coindTensor [Fintype G] (A B : Rep R G) : coind₁'.obj A ⊗ B ≅ coind₁'.obj (A ⊗ B) :=
  MonoidalCategory.whiskerRightIso (coindIsoTensor A) _ ≪≫ α_ _ _ _ ≪≫
    (coindIsoTensor (A ⊗ B)).symm

abbrev coindTensor' [Fintype G] (A B : Rep R G) : A ⊗ coind₁'.obj B ≅ coind₁'.obj (A ⊗ B) :=
  (β_ _ _) ≪≫ coindTensor B A ≪≫ coind₁'.mapIso (β_ _ _)

def upTensor [Fintype G] (A B : Rep R G) : up.obj A ⊗ B ≅ up.obj (A ⊗ B) :=
  MonoidalCategory.whiskerRightIso (upIsoCoaugTensor A) _ ≪≫ α_ _ _ _ ≪≫
    (upIsoCoaugTensor (A ⊗ B)).symm

abbrev upTensor' [Fintype G] (A B : Rep R G) : A ⊗ up.obj B ≅ up.obj (A ⊗ B) :=
  (β_ _ _) ≪≫ upTensor B A ≪≫ up.mapIso (β_ _ _)

@[reassoc]
lemma upTensor_coind_comm [Fintype G] (A B : Rep R G) :
     up.π A ▷ B ≫ (upTensor A B).hom = (coindTensor A B).hom ≫ up.π (A ⊗ B) := by
  simp only [coequalizer_as_cokernel, Functor.id_obj, upTensor, Iso.trans_hom, whiskerRightIso_hom,
    upIsoCoaugTensor_hom, Iso.symm_hom, upIsoCoaugTensor_inv, coindTensor, coindIsoTensor_hom,
    coindIsoTensor_inv, Category.assoc]
  rw [← Category.assoc, ← comp_whiskerRight, upToTensor]
  change ((upSES A).g ≫ _) ▷ B ≫ _ = _
  rw [Exact.g_desc, comp_whiskerRight, Category.assoc]
  nth_rw 2 [← Category.assoc]
  unfold coaug
  rw [associator_naturality_left, Category.assoc, coaugTensorToUp]
  change _ ≫ _ ≫ ((upSES₀ R G).map (tensorRight (A ⊗ B))).g ≫ _ = _
  rw [Exact.g_desc]

lemma upTensor_coind_comm' [Fintype G] (A B : Rep R G) :
    A ◁ up.π B ≫ (upTensor' A B).hom = (coindTensor' A B).hom ≫ up.π (A ⊗ B) := by
  dsimp only [upTensor', coindTensor', Iso.trans_hom]
  rw [BraidedCategory.braiding_naturality_right_assoc, upTensor_coind_comm_assoc]
  simp
