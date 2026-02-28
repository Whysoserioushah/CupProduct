import Mathlib
import CupProduct.groupCoh.Rep
import CupProduct.Cohomology.Functors.UpDown
import CupProduct.Cohomology.AugmentationModule

universe u

variable (R G : Type u) [CommRing R] [Group G]

open CategoryTheory groupCohomology MonoidalCategory Rep.aug ShortComplex

noncomputable section

-- weird morphism I cook up with
def aug_shortExactSequence_split [Fintype G] : ((aug_shortExactSequence R G).map
    (forget₂ (Rep R G) (ModuleCat R))).Splitting :=
  .ofExactOfSection _ ((aug_isShortExact R G).1.map _) (ModuleCat.ofHom
    ((LinearMap.lsmul R (Rep.leftRegular R G)).flip (Rep.leftRegular.of 1)))
    (by ext; simp [Rep.leftRegular.ε, Rep.leftRegular.of]) <|
    (forget₂ (Rep R G) (ModuleCat R)).map_mono (ι R G)

def split_downSES' [Fintype G] (A : Rep R G) : (((aug_shortExactSequence R G).map
    (tensorRight A)).map (forget₂ (Rep R G) (ModuleCat R))).Splitting := by
  rw [← ShortComplex.map_comp, show (aug_shortExactSequence R G).map ((tensorRight A) ⋙
    (forget₂ (Rep R G) (ModuleCat R))) = ((aug_shortExactSequence R G).map
    (forget₂ (Rep R G) (ModuleCat R))).map (tensorRight A.V) by rfl]
  exact .map (aug_shortExactSequence_split R G) _

set_option linter.unusedFintypeInType false in
lemma exact_downSES' [Fintype G] (A : Rep R G) : ((aug_shortExactSequence R G).map
    (tensorRight A)).Exact := exact_iff_exact_map_forget₂ _ |>.2 <|
    show Exact (((aug_shortExactSequence R G).map (tensorRight A)).map (_ ⋙ _)) by
  rw [ShortComplex.map_comp, ← exact_iff_exact_map_forget₂]
  exact (split_downSES' R G A).exact

set_option linter.unusedFintypeInType false in
lemma shortExact_downSES' [Fintype G] (A : Rep R G) : ((aug_shortExactSequence R G).map
    (tensorRight A)).ShortExact where
  exact := exact_downSES' R G A
  mono_f := Functor.ReflectsMonomorphisms.reflects (F := forget₂ (Rep R G) (ModuleCat R)) _ <|
    (split_downSES' R G A).shortExact.mono_f
  epi_g := Functor.ReflectsEpimorphisms.reflects (F := forget₂ (Rep R G) (ModuleCat R)) _ <|
    (split_downSES' R G A).shortExact.epi_g

open Rep.dimensionShift Limits TensorProduct

variable {R G}

@[simps]
def tensorToIndAux (A : Rep R G) (f : G →₀ R) : A.V →ₗ[R] (G →₀ A.V) where
  toFun a := f.sum (fun g r ↦ Finsupp.lsingle (R := R) g⁻¹ (r • a))
  map_add' := by simp
  map_smul' r a := by
    conv_lhs => enter [2, g, r']; rw [← smul_comm, map_smul]
    rw [Finsupp.smul_sum, RingHom.id_apply]

@[simps]
def tensorToIndLinear (A : Rep R G) : (G →₀ R) →ₗ[R] A.V →ₗ[R] (G →₀ A.V) where
  toFun f := tensorToIndAux A f
  map_add' f1 f2 := by
    classical
    ext1 a
    simp only [tensorToIndAux_apply, map_smul, Finsupp.lsingle_apply,
      Finsupp.smul_single, LinearMap.add_apply]
    rw [Finsupp.sum_add_index (by simp) (fun g' hg' r1 r2 ↦ by simp [add_smul])]
  map_smul' r f := by
    ext1 a
    simp only [tensorToIndAux_apply, map_smul, Finsupp.lsingle_apply, Finsupp.smul_single,
      RingHom.id_apply, LinearMap.smul_apply, Finsupp.smul_sum, Finsupp.smul_single,
      ← smul_assoc, smul_eq_mul]
    exact Finsupp.sum_smul_index (by simp)

open Rep

@[simps]
def tensorToInd (A : Rep R G) : leftRegular R G ⊗ A ⟶ ind₁'.obj A where
  hom := ModuleCat.ofHom <| TensorProduct.lift (tensorToIndLinear A)
  comm g := by
    ext1
    simp only [Action.tensorObj_V, ModuleCat.MonoidalCategory.tensorObj_carrier, ind₁'_obj,
      Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      ModuleCat.endRingEquiv, RingEquiv.symm_mk, RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe,
      RingEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply, Representation.ind₁'_apply,
      ModuleCat.ofHom_comp]
    ext h a i
    rw [Action.tensor_ρ]
    simp [ModuleCat.endRingEquiv, ModuleCat.hom_tensorHom]

@[simps]
def tensorToIndNatTrans : tensorLeft (leftRegular R G) ⟶ ind₁' where
  app A := tensorToInd A
  naturality {X Y} f := by
    ext : 2
    simp only [curriedTensor_obj_obj, Action.tensorObj_V,
      ModuleCat.MonoidalCategory.tensorObj_carrier, ind₁'_obj, curriedTensor_obj_map,
      Action.comp_hom, Action.whiskerLeft_hom, tensorToInd_hom, Equivalence.symm_inverse,
      Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_whiskerLeft]
    ext g x h
    simp [ind₁']

@[simps]
def indToTensorLinear [Fintype G] (A : Rep R G) : (G →₀ A.V) →ₗ[R] (G →₀ R) ⊗[R] A where
  toFun f := ∑ g : G, (leftRegular.of g⁻¹) ⊗ₜ f g
  map_add' := by simp [tmul_add, Finset.sum_add_distrib]
  map_smul' := by simp [Finset.smul_sum]

@[simps]
def indToTensor [Fintype G] (A : Rep R G) : ind₁'.obj A ⟶ leftRegular R G ⊗ A where
  hom := ModuleCat.ofHom <| indToTensorLinear A
  comm g := by
    ext1
    simp only [ind₁'_obj, Action.tensorObj_V, ModuleCat.MonoidalCategory.tensorObj_carrier,
      ModuleCat.endRingEquiv, RingEquiv.symm_mk, RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe,
      RingEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply, Representation.ind₁'_apply,
      ModuleCat.ofHom_comp, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, Category.assoc, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom]
    ext h a
    rw [Action.tensor_ρ]
    simp only [LinearMap.coe_comp, Finsupp.coe_lmapDomain, Function.comp_apply,
      Finsupp.lsingle_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      Finsupp.mapDomain_single, indToTensorLinear_apply, ModuleCat.endRingEquiv, RingEquiv.symm_mk,
      RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe,
      RingHom.coe_coe, RingEquiv.coe_mk, Equiv.coe_fn_mk, ModuleCat.hom_tensorHom,
      ModuleCat.hom_ofHom, ρ_hom, map_sum, map_tmul]
    change ∑ y, _ = ∑ x, ((leftRegular R G).ρ g (leftRegular.of x⁻¹)) ⊗ₜ _
    conv_rhs => enter [2, x]; rw [leftRegular.ρ_apply_of]
    conv_lhs => rw [Finset.sum_equiv (t := Finset.univ) (g := fun y ↦ leftRegular.of (g * y⁻¹)
      ⊗ₜ[R] (fun₀ | h * g⁻¹ => (A.ρ g) a) (y * g⁻¹)) (Equiv.mulRight g) (by simp) (by simp)]
    classical
    congr!
    simp only [Finsupp.single_apply, mul_left_inj]
    split_ifs <;> simp

@[simps]
def indToTensorNatTrans [Fintype G] : ind₁' ⟶ tensorLeft (leftRegular R G) where
  app A := indToTensor A
  naturality {X Y} f := by
    classical
    ext : 2
    simp only [ind₁'_obj, curriedTensor_obj_obj, Action.tensorObj_V,
      ModuleCat.MonoidalCategory.tensorObj_carrier, Action.comp_hom, indToTensor_hom,
      Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      curriedTensor_obj_map, Action.whiskerLeft_hom, ModuleCat.hom_whiskerLeft]
    ext g x
    simp only [ind₁', ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
      Finsupp.lsingle_apply, Finsupp.mapRange.linearMap_apply, coe_hom, Finsupp.mapRange_single,
      indToTensorLinear_apply, Finsupp.single_apply, map_sum, LinearMap.lTensor_tmul, hom_apply]
    congr!
    split_ifs <;> simp

lemma indToTensorLienar_comp_inv [Fintype G] (A : Rep R G) :
    lift (tensorToIndLinear A) ∘ₗ indToTensorLinear A = LinearMap.id := by
  ext g a : 2
  simp [leftRegular.of]

lemma indToTensorLinear_inv_comp [Fintype G] (A : Rep R G) :
    indToTensorLinear A ∘ₗ lift (tensorToIndLinear A) = LinearMap.id := by
  classical
  ext g a
  simp [leftRegular.of, Finsupp.single_apply, tmul_ite]

@[simps]
def indIsoTensor [Fintype G] : ind₁' ≅ tensorLeft (leftRegular R G) where
  hom := indToTensorNatTrans
  inv := tensorToIndNatTrans
  hom_inv_id := by ext; simp [(indToTensorLienar_comp_inv)]
  inv_hom_id := by ext; simp [(indToTensorLinear_inv_comp)]

abbrev Rep.trivialTensorIso : 𝟭 (Rep R G) ≅ tensorLeft (Rep.trivial R G R) :=
  leftUnitorNatIso _|>.symm

open Rep.leftRegular ModuleCat
abbrev tensorToDown [Fintype G] (A : Rep R G) : aug R G ⊗ A ⟶ down.obj A :=
  haveI : Mono (downSES A).f := (shortExact_downSES A).mono_f
  (shortExact_downSES A).1.lift ((ι R G ▷ A) ≫ tensorToInd A) <| by
  ext1
  simp only [Action.tensorObj_V, downSES_X₃, downSES_X₂, ind₁'_obj, equalizer_as_kernel, downSES_g,
    Category.assoc, Action.comp_hom, Action.whiskerRight_hom, tensorToInd_hom,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, ind₁'_π_app_hom, Action.zero_hom]
  apply_fun ((((kernelIsoKer _).inv ≫ (forgetKernelIso (ε R G)).inv) ▷ A.V) ≫ ·)
  · simp only [← comp_whiskerRight_assoc, Category.assoc]
    rw [forgetKernelIso_inv_comp_kernel_ι, kernelIsoKer_inv_kernel_ι]
    ext1
    simp only [MonoidalCategory.tensorObj_carrier, ModuleCat.hom_comp, hom_ofHom, hom_whiskerRight,
      comp_whiskerRight, comp_zero, hom_zero]
    ext ⟨x, hx⟩ a
    classical
    simp only [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self, curry_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply,
      lift.tmul, tensorToIndLinear_apply, tensorToIndAux_apply, map_smul, Finsupp.lsingle_apply,
      Finsupp.smul_single, Representation.ind₁'_π_apply, LinearMap.zero_apply]
    rw [Finsupp.sum_sum_index (by simp) (by simp)]
    simp only [Module.End.one_apply, Finsupp.sum_single_index, map_smul, LinearMap.mem_ker] at hx ⊢
    rw [ε_eq_sum'] at hx
    simp [Finsupp.sum, ← Finset.sum_smul, hx]
  exact fun _ _ h ↦ (cancel_epi _).mp h

@[simps]
def tensorToDownFunc [Fintype G] : tensorLeft (aug R G) ⟶ down where
  app := tensorToDown
  naturality {X Y} f := by
    haveI := (shortExact_downSES Y).mono_f
    rw [← cancel_mono (downSES Y).f, Category.assoc, Exact.lift_f, Category.assoc, downSES_f,
      down_map, kernel.lift_ι]
    change _ = _ ≫ (downSES X).f ≫ _
    rw [Exact.lift_f_assoc, Category.assoc, ← tensorToIndNatTrans_app X,
      ← tensorToIndNatTrans.naturality]
    simp [whisker_exchange_assoc]

abbrev downToTensor [Fintype G] (A : Rep R G) : down.obj A ⟶ aug R G ⊗ A :=
  haveI : Mono ((aug_shortExactSequence R G).map (tensorRight A)).f := (shortExact_downSES' R G A).2
  (shortExact_downSES' R G A).1.lift (down.ι A ≫ indToTensor A) <| by
  ext1
  simp only [down_obj, ind₁'_obj, Functor.id_obj, map_X₃, Functor.flip_obj_obj,
    curriedTensor_obj_obj, Action.tensorObj_V, map_X₂, equalizer_as_kernel, map_g,
    Functor.flip_obj_map, curriedTensor_map_app, Category.assoc, Action.comp_hom, indToTensor_hom,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, Action.whiskerRight_hom, Action.zero_hom]
  apply_fun (((kernelIsoKer _).inv ≫ (forgetKernelIso (ind₁'_π.app A)).inv) ≫ ·) using
    fun _ _ ↦ cancel_epi _|>.1
  simp only [Category.assoc, comp_zero]
  rw [forgetKernelIso_inv_comp_kernel_ι_assoc, ← Category.assoc, kernelIsoKer_inv_kernel_ι]
  ext1
  simp only [ind₁'_obj, Functor.id_obj, ind₁'_π_app_hom, hom_ofHom,
    MonoidalCategory.tensorObj_carrier, ModuleCat.hom_comp, hom_whiskerRight, hom_zero]
  ext ⟨x, hx⟩
  simp only [LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply,
    indToTensorLinear_apply, map_sum, LinearMap.rTensor_tmul]
  conv_lhs => enter [2, g]; rw [ε_of]
  rw [← tmul_sum]
  simp only [LinearMap.mem_ker, Representation.ind₁'_π_apply, Finsupp.sum] at hx
  rw [← finsum_eq_sum_of_support_subset (α := G) _ (by simp), finsum_eq_sum_of_fintype] at hx
  erw [LinearMap.zero_apply] -- this error is weird I can't remove it by simp [tensorObj_carrier]
  simp_all

@[simps]
def downToTensorFunc [Fintype G] : down ⟶ tensorLeft (aug R G) where
  app := downToTensor
  naturality {X Y} f := by
    haveI := (shortExact_downSES' R G Y).2
    rw [← cancel_mono ((aug_shortExactSequence R G).map (tensorRight Y)).f, Category.assoc,
      Exact.lift_f, down_map, kernel.lift_ι_assoc]
    simp only [down_obj, ind₁'_obj, Functor.id_obj, map_X₂, Functor.flip_obj_obj,
      curriedTensor_obj_obj, Category.assoc, map_X₁, curriedTensor_obj_map, map_f,
      equalizer_as_kernel, Functor.flip_obj_map, curriedTensor_map_app]
    rw [whisker_exchange]
    change _ = _ ≫ ((aug_shortExactSequence R G).map (tensorRight X)).f ≫ _
    rw [Exact.lift_f_assoc, ← indToTensorNatTrans_app Y, indToTensorNatTrans.naturality]
    simp

@[simps]
def downIso [Fintype G] (A : Rep R G) : down.obj A ≅ aug R G ⊗ A where
  hom := downToTensor A
  inv := tensorToDown A
  hom_inv_id := by
    haveI := (shortExact_downSES A).mono_f
    rw [← cancel_mono (downSES A).f]
    simp only [tensorToDown, Category.assoc, Exact.lift_f, downToTensor]
    change _ ≫ ((aug_shortExactSequence R G).map (tensorRight A)).f ≫ _ = _
    simp only [Exact.lift_f_assoc, Category.id_comp, Category.assoc, downSES_f]
    convert Category.comp_id (down.ι A)
    ext : 2
    simp [(indToTensorLienar_comp_inv)]
  inv_hom_id := by
    haveI := (shortExact_downSES' R G A).2
    rw [← cancel_mono ((aug_shortExactSequence R G).map (tensorRight A)).f]
    simp only [downToTensor, Category.assoc, Exact.lift_f, tensorToDown]
    change _ ≫ (downSES A).f ≫ _ = _
    simp only [Exact.lift_f_assoc, Category.id_comp, Category.assoc]
    ext : 2
    simp [(indToTensorLinear_inv_comp)]

@[simps]
def downNatIso [Fintype G] : down ≅ tensorLeft (aug R G) where
  hom := downToTensorFunc
  inv := tensorToDownFunc
  hom_inv_id := by
    ext X : 2
    simp only [down_obj, ind₁'_obj, Functor.id_obj, NatTrans.comp_app, curriedTensor_obj_obj,
      downToTensorFunc_app, tensorToDownFunc_app, NatTrans.id_app]
    rw [← downIso_hom, ← downIso_inv, Iso.hom_inv_id]
  inv_hom_id := by
    ext X : 2
    simp only [down_obj, ind₁'_obj, Functor.id_obj, NatTrans.comp_app, downToTensorFunc_app,
      tensorToDownFunc_app, NatTrans.id_app]
    rw [← downIso_hom, ← downIso_inv, Iso.inv_hom_id]

abbrev downTensorIso [Fintype G] (A B : Rep R G) : down.obj A ⊗ B ≅ down.obj (A ⊗ B) :=
  (tensorRight B).mapIso (downIso A) ≪≫ α_ _ _ _ ≪≫ (downIso (A ⊗ B)).symm

@[simps! hom_app inv_app]
def downTensorNatIso [Fintype G] (B : Rep R G) : down ⋙ tensorRight B ≅ tensorRight B ⋙ down :=
  NatIso.ofComponents (downTensorIso · B) <| fun {X Y} f ↦ by
    simp only [Functor.comp_map, downTensorIso, Iso.trans_hom, Category.assoc,
      Functor.mapIso_hom, Iso.symm_hom, downIso_inv, ← tensorToDownFunc_app,
      ← tensorToDownFunc.naturality, curriedTensor_obj_map, Functor.flip_obj_map,
      curriedTensor_map_app, ← associator_naturality_middle_assoc, downIso_hom,
      ← comp_whiskerRight_assoc]
    rw [← downToTensorFunc_app X, ← curriedTensor_obj_map, ← downToTensorFunc.naturality]
    simp

abbrev downTensorNatIso' [Fintype G] (A : Rep R G) : down ⋙ tensorLeft A ≅ tensorLeft A ⋙ down :=
  down.isoWhiskerLeft (BraidedCategory.tensorLeftIsoTensorRight A) ≪≫ downTensorNatIso A ≪≫
    Functor.isoWhiskerRight (BraidedCategory.tensorLeftIsoTensorRight A).symm _
