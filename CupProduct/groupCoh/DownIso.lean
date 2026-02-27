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
def tensorToIndHom (A : Rep R G) : leftRegular R G ⊗ A ⟶ ind₁'.obj A where
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
  app A := tensorToIndHom A
  naturality {X Y} f := by
    ext : 2
    simp only [curriedTensor_obj_obj, Action.tensorObj_V,
      ModuleCat.MonoidalCategory.tensorObj_carrier, ind₁'_obj, curriedTensor_obj_map,
      Action.comp_hom, Action.whiskerLeft_hom, tensorToIndHom_hom, Equivalence.symm_inverse,
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

open Rep.leftRegular ModuleCat

def trivialTensorToInd [Fintype G] (A : Rep R G) : trivial R G R ⊗ A ⟶ ind₁'.obj A :=
  haveI : Epi ((aug_shortExactSequence R G).map (tensorRight A)).g := (shortExact_downSES' R G A).3
  (exact_downSES' R G A).desc (tensorToIndHom A) <| by
  ext1
  simp only [map_X₁, Functor.flip_obj_obj, curriedTensor_obj_obj, Action.tensorObj_V, ind₁'_obj,
    map_X₂, map_f, equalizer_as_kernel, Functor.flip_obj_map, curriedTensor_map_app,
    Action.comp_hom, Action.whiskerRight_hom, tensorToIndHom_hom, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Action.zero_hom]
  apply_fun ((((ModuleCat.kernelIsoKer (ε R G).hom).inv ≫
    (forgetKernelIso (ε R G)).inv) ▷ A.V) ≫ ·)
  · simp only [comp_zero]
    rw [← comp_whiskerRight_assoc, Category.assoc, forgetKernelIso_inv_comp_kernel_ι,
      kernelIsoKer_inv_kernel_ι]
    ext1
    simp only [MonoidalCategory.tensorObj_carrier, ModuleCat.hom_comp, hom_ofHom, hom_zero]
    ext ⟨x, hx⟩ a g
    classical
    simp only [hom_whiskerRight, hom_ofHom, AlgebraTensorModule.curry_apply,
      LinearMap.restrictScalars_self, curry_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.rTensor_tmul, Submodule.subtype_apply, lift.tmul, tensorToIndLinear_apply,
      tensorToIndAux_apply, map_smul, Finsupp.lsingle_apply, Finsupp.smul_single, Finsupp.sum_apply,
      LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply]
    classical
    simp only [LinearMap.mem_ker] at hx
    rw [ε_eq_sum] at hx
    -- simp only [map_smul, smul_eq_mul] at hx
    -- conv_lhs at hx => enter [2, y]; rw [leftRegular.ε_of, mul_one]
    simp [Finsupp.sum, Finsupp.single_apply, inv_eq_iff_eq_inv] -- is this true?
    -- simp? [Finsupp.sum]
    -- simp only [hom_whiskerRight, hom_ofHom, AlgebraTensorModule.curry_apply,
    --   LinearMap.restrictScalars_self, curry_apply, LinearMap.coe_comp, Function.comp_apply,
    --   LinearMap.rTensor_tmul, Submodule.subtype_apply, lift.tmul, tensorToIndLinear_apply,
    --   tensorToIndAux_apply, Finsupp.sum, map_smul, Finsupp.lsingle_apply, Finsupp.smul_single,
    --   Finsupp.coe_finset_sum, Finset.sum_apply, LinearMap.zero_apply, Finsupp.coe_zero,
    --   Pi.zero_apply]
    -- simp only [Finsupp.single_apply]
    -- rw [Finset.sum_ite_eq]
    -- change ∑ i ∈ x.support, leftRegular.of
    sorry



  -- ext : 2
  -- simp only [map_X₁, Functor.flip_obj_obj, curriedTensor_obj_obj, Action.tensorObj_V,
  --   ModuleCat.MonoidalCategory.tensorObj_carrier, ind₁'_obj, map_X₂, map_f, equalizer_as_kernel,
  --   Functor.flip_obj_map, curriedTensor_map_app, Action.comp_hom, Action.whiskerRight_hom,
  --   tensorToIndHom_hom, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
  --   Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
  --   ModuleCat.hom_whiskerRight, Action.zero_hom, ModuleCat.hom_zero]
  -- have hM : Mono ((aug_shortExactSequence R G).map (tensorRight A)).f :=
  --   (shortExact_downSES' R G A).2
  -- rw [Rep.mono_iff_injective] at hM
  -- change Function.Injective (LinearMap.rTensor A.V (kernel.ι (ε R G)).hom.hom) at hM

  stop
  ext x a g
  simp only [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self, curry_apply,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.rTensor_tmul, lift.tmul,
    tensorToIndLinear_apply, tensorToIndAux_apply, map_smul, Finsupp.lsingle_apply,
    Finsupp.smul_single, Finsupp.sum_apply, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply]
  rw [← kernel_ι_comp_forgetKernelIso, ← ModuleCat.kernelIsoKer_hom_ker_subtype]
  simp
  sorry

#check leftRegular.ε_of
abbrev downToTensor [Fintype G] (A : Rep R G) : trivial R G R ⊗ A ⟶ down.obj A :=
  haveI : Epi ((aug_shortExactSequence R G).map (tensorRight A)).g := (shortExact_downSES' R G A).3
  haveI : Mono (downSES A).f := (shortExact_downSES A).2
  (shortExact_downSES A).1.lift ((exact_downSES' R G A).desc (tensorToIndHom A)
  (by simp; sorry) : _ ⟶ ind₁'.obj A) sorry
  --down.ι _ ≫ indToTensor A

#check ShortComplex.Exact.lift
