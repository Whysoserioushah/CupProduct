import Mathlib
import CupProduct.groupCoh.Rep
import CupProduct.Cohomology.Functors.UpDown
import CupProduct.Cohomology.AugmentationModule
import CupProduct.Mathlib.Algebra.Homology.ShortComplex.Rep

universe u

variable (R G : Type u) [CommRing R] [Group G]

open CategoryTheory groupCohomology MonoidalCategory Rep.aug ShortComplex

noncomputable section

-- weird morphism I cook up with
set_option backward.isDefEq.respectTransparency false in
def aug_shortExactSequence_split : ((aug_shortExactSequence R G).map
    (forget₂ (Rep R G) (ModuleCat R))).Splitting :=
  .ofExactOfSection _ ((aug_isShortExact R G).1.map _) (ModuleCat.ofHom
    ((LinearMap.lsmul R (Rep.leftRegular R G)).flip (.single 1 1)))
    (by ext; simp) <|
    (forget₂ (Rep R G) (ModuleCat R)).map_mono (ι R G)

def split_downSES' (A : Rep R G) : (((aug_shortExactSequence R G).map
    (tensorRight A)).map (forget₂ (Rep R G) (ModuleCat R))).Splitting := by
  rw [← ShortComplex.map_comp, show (aug_shortExactSequence R G).map ((tensorRight A) ⋙
    (forget₂ (Rep R G) (ModuleCat R))) = ((aug_shortExactSequence R G).map
    (forget₂ (Rep R G) (ModuleCat R))).map (tensorRight (ModuleCat.of R A.V)) by rfl]
  exact .map (aug_shortExactSequence_split R G) _

set_option linter.unusedFintypeInType false in
lemma exact_downSES' (A : Rep R G) : ((aug_shortExactSequence R G).map
    (tensorRight A)).Exact :=
  (exact_map_iff_of_faithful _ _).1 (split_downSES' R G A).exact

set_option linter.unusedFintypeInType false in
lemma shortExact_downSES' (A : Rep R G) : ((aug_shortExactSequence R G).map
    (tensorRight A)).ShortExact where
  exact := exact_downSES' R G A
  mono_f := Functor.ReflectsMonomorphisms.reflects (F := forget₂ (Rep R G) (ModuleCat R)) _ <|
    (split_downSES' R G A).shortExact.mono_f
  epi_g := Functor.ReflectsEpimorphisms.reflects (F := forget₂ (Rep.{u} R G) (ModuleCat R)) _ <|
    (split_downSES' R G A).shortExact.epi_g

open Rep.dimensionShift Limits TensorProduct

variable {R G}

@[simps]
def tensorToIndAux {R G : Type*} (M : Type*) [CommRing R] [Group G] [AddCommGroup M]
    [Module R M] (f : G →₀ R) : M →ₗ[R] (G →₀ M) where
  toFun a := f.sum (fun g r ↦ Finsupp.lsingle (R := R) g⁻¹ (r • a))
  map_add' := by simp
  map_smul' r a := by
    conv_lhs => enter [2, g, r']; rw [← smul_comm, map_smul]
    rw [Finsupp.smul_sum, RingHom.id_apply]

@[simps]
def tensorToIndLinear {R G : Type*} (M : Type*) [CommRing R] [Group G] [AddCommGroup M]
    [Module R M] : (G →₀ R) →ₗ[R] M →ₗ[R] (G →₀ M) where
  toFun f := tensorToIndAux M f
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

set_option backward.isDefEq.respectTransparency false in
@[simps! toLinearMap]
def Representation.tensorToInd {R G M : Type*} [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    (ρ : Representation R G M) : ((leftRegular R G).tprod ρ).IntertwiningMap ρ.ind₁' where
  __ := lift <| tensorToIndLinear M
  isIntertwining' g := by ext; simp

abbrev tensorToInd (A : Rep R G) : leftRegular R G ⊗ A ⟶ ind₁'.obj A :=
  ofHom A.ρ.tensorToInd

@[simps]
def tensorToIndNatTrans : tensorLeft (leftRegular R G) ⟶ ind₁' where
  app A := tensorToInd A
  naturality {X Y} f := by
    ext : 2
    simp only [curriedTensor_obj_obj, tensor_V, ind₁', tensor_ρ, curriedTensor_obj_map,
      Rep.hom_comp, hom_ofHom, hom_whiskerLeft, Representation.IntertwiningMap.comp_toLinearMap,
      Representation.tensorToInd_toLinearMap, Representation.IntertwiningMap.toLinearMap_lTensor]
    ext; simp

@[simps]
def indToTensorLinear {R G : Type*} (M : Type*) [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    [Fintype G] : (G →₀ M) →ₗ[R] (G →₀ R) ⊗[R] M where
  toFun f := ∑ g : G, (.single g⁻¹ 1) ⊗ₜ f g
  map_add' := by simp [tmul_add, Finset.sum_add_distrib]
  map_smul' := by simp [Finset.smul_sum]

@[simps! toLinearMap]
def Representation.indToTensor {R G M : Type*} [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    [Fintype G] (ρ : Representation R G M) :
    ρ.ind₁'.IntertwiningMap ((leftRegular R G).tprod ρ) where
  __ := indToTensorLinear M
  isIntertwining' g := LinearMap.ext fun f ↦ by
    simp only [LinearMap.coe_comp, Function.comp_apply, indToTensorLinear_apply, ind₁'_apply₂,
      tprod_apply, map_sum, map_tmul, ofMulAction_single, smul_eq_mul]
    exact Finset.sum_equiv (Equiv.mulRight g) (by simp) (by simp)

abbrev indToTensor [Fintype G] (A : Rep R G) : ind₁'.obj A ⟶ leftRegular R G ⊗ A :=
  ofHom A.ρ.indToTensor

@[simps]
def indToTensorNatTrans [Fintype G] : ind₁' ⟶ tensorLeft (leftRegular R G) where
  app A := indToTensor A
  naturality {X Y} f := by
    ext : 2
    simp only [ind₁', curriedTensor_obj_obj, tensor_V, tensor_ρ, Rep.hom_comp, hom_ofHom,
      Representation.IntertwiningMap.comp_toLinearMap, Representation.indToTensor_toLinearMap,
      curriedTensor_obj_map, hom_whiskerLeft, Representation.IntertwiningMap.toLinearMap_lTensor]
    ext g x
    classical simp [Finsupp.single]

lemma indToTensorLienar_comp_inv {R G : Type*} (M : Type*) [CommRing R] [Group G] [AddCommGroup M]
    [Module R M] [Fintype G] : lift (tensorToIndLinear (R := R) (G := G) M) ∘ₗ
    indToTensorLinear M = LinearMap.id := by
  ext g a : 2
  simp

lemma indToTensorLinear_inv_comp {R G : Type*} (M : Type*) [CommRing R] [Group G] [AddCommGroup M]
    [Module R M] [Fintype G] :
    indToTensorLinear (R := R) (G := G) M ∘ₗ lift (tensorToIndLinear M) = LinearMap.id := by
  ext g a
  classical simp [Finsupp.single_apply, tmul_ite]

@[simps]
def indIsoTensor [Fintype G] : ind₁' ≅ tensorLeft (leftRegular R G) where
  hom := indToTensorNatTrans
  inv := tensorToIndNatTrans
  hom_inv_id := by ext; simp [indToTensorLienar_comp_inv]
  inv_hom_id := by ext; simp [indToTensorLinear_inv_comp]

abbrev Rep.trivialTensorIso : 𝟭 (Rep R G) ≅ tensorLeft (Rep.trivial R G R) :=
  leftUnitorNatIso _|>.symm

open Rep.leftRegular ModuleCat

set_option backward.isDefEq.respectTransparency false in
abbrev tensorToDown [Fintype G] (A : Rep R G) : aug R G ⊗ A ⟶ down.obj A :=
  haveI : Mono (downSES A).f := (shortExact_downSES A).mono_f
  (shortExact_downSES A).1.lift ((ι R G ▷ A) ≫ tensorToInd A) <| by
  dsimp
  rw [Category.assoc, show tensorToInd A ≫ ind₁'_π.app A = ε R G ▷ A ≫ (λ_ A).hom by
    ext1; dsimp; ext; simp [ind₁'_π], ← Category.assoc]
  simp [← comp_whiskerRight]

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
abbrev downToTensor [Fintype G] (A : Rep R G) : down.obj A ⟶ aug R G ⊗ A :=
  haveI : Mono ((aug_shortExactSequence R G).map (tensorRight A)).f := (shortExact_downSES' R G A).2
  (shortExact_downSES' R G A).1.lift (down.ι A ≫ indToTensor A) <| by
  dsimp
  have : indToTensor A ≫ ε R G ▷ A = ind₁'_π.app A ≫ (λ_ A).inv := by
    ext1; dsimp; ext
    classical simp [ind₁'_π, Finsupp.single_apply, tmul_ite]
  rw [Category.assoc, this, ← Category.assoc, kernel.condition, zero_comp]

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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
    simp [indToTensorLinear_inv_comp]

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

set_option backward.isDefEq.respectTransparency false in
@[simps! hom_app inv_app]
def downTensorNatIso [Fintype G] (B : Rep R G) : down ⋙ tensorRight B ≅ tensorRight B ⋙ down :=
  NatIso.ofComponents (downTensorIso · B) <| fun {X Y} f ↦ by
    simp only [Functor.comp_obj, down_obj, ind₁'_obj, Functor.id_obj, Functor.flip_obj_obj,
      curriedTensor_obj_obj, tensor_V, tensor_ρ, Functor.comp_map, Functor.flip_obj_map,
      curriedTensor_map_app, Iso.trans_hom, Functor.mapIso_hom, downIso_hom, Iso.symm_hom,
      downIso_inv, Category.assoc]
    rw [← tensorToDownFunc_app, ← tensorToDownFunc_app, ← tensorToDownFunc.naturality,
      ← comp_whiskerRight_assoc, curriedTensor_obj_map, ← associator_naturality_middle_assoc,
      ← comp_whiskerRight_assoc, ← downToTensorFunc_app, downToTensorFunc.naturality]
    simp

abbrev downTensorNatIso' [Fintype G] (A : Rep R G) : down ⋙ tensorLeft A ≅ tensorLeft A ⋙ down :=
  down.isoWhiskerLeft (BraidedCategory.tensorLeftIsoTensorRight A) ≪≫ downTensorNatIso A ≪≫
    Functor.isoWhiskerRight (BraidedCategory.tensorLeftIsoTensorRight A).symm _

abbrev downTensorIso' [Fintype G] (A B : Rep R G) : A ⊗ down.obj B ≅ down.obj (A ⊗ B) :=
  downTensorNatIso' A|>.app B

@[simps]
def downSES₀ShortComplex : Rep R G ⥤ ShortComplex (Rep R G) where
  obj A := (aug_shortExactSequence R G).map (tensorRight A)
  map {A B} f := {
    τ₁ := _ ◁ f
    τ₂ := _ ◁ f
    τ₃ := _ ◁ f}
  map_id A := by ext <;> simp
  map_comp f g := by ext1 <;> simp

@[simps! hom_τ₁ hom_τ₂ hom_τ₃]
def downSESIsodownSES₀ (A) [Fintype G] : downSES A ≅
    (aug_shortExactSequence R G).map (tensorRight A) :=
  ShortComplex.isoMk (downNatIso.app A) (indIsoTensor.app A) ((ρ_ A).symm ≪≫ β_ _ _)
    (by
      dsimp [-down_map, -down_obj, -ind₁'_obj, downToTensor, -ShortComplex.map_f]
      have := (shortExact_downSES' R G A).2
      exact Exact.lift_f _ _ _) <| by
    ext : 2
    simp only [downSES_X₂, ind₁'_obj, map_X₃, Functor.flip_obj_obj, curriedTensor_obj_obj, tensor_V,
      tensor_ρ, map_X₂, Iso.app_hom, indIsoTensor_hom, indToTensorNatTrans_app, map_g,
      Functor.flip_obj_map, curriedTensor_map_app, Rep.hom_comp, Rep.hom_whiskerRight,
      Rep.hom_ofHom, Representation.isTrivial_def, LinearMap.id_coe, id_eq,
      Representation.IntertwiningMap.comp_toLinearMap,
      Representation.IntertwiningMap.toLinearMap_rTensor, Representation.indToTensor_toLinearMap,
      downSES_X₃, downSES_g, ind₁'_π, Iso.trans_hom, Iso.symm_hom, braiding_tensorUnit_right,
      Iso.inv_hom_id_assoc, Rep.hom_inv_leftUnitor]
    ext g a
    simp [Finset.sum_eq_single_of_mem (f := fun x ↦ (1 : R) ⊗ₜ (Finsupp.single g a x)) g
      (Finset.mem_univ g) (by simp +contextual)]

def downSESIsodownSES₀Functor [Fintype G] :
    downShortComplex (G := G) ≅ downSES₀ShortComplex (R := R) :=
  NatIso.ofComponents (fun A ↦ downSESIsodownSES₀ A) fun {X Y} f ↦ by
    ext1
    · exact downToTensorFunc.naturality f
    · exact indToTensorNatTrans.naturality f
    · ext : 2;
      exact LinearMap.ext_iff.mpr (congrFun rfl)

set_option linter.unusedFintypeInType false in
lemma shortExact_downSESTensorRight [Fintype G] (A B : Rep R G) :
    ((downSES A).map (tensorRight B)).ShortExact :=
  have e := (tensorRight B).mapShortComplex.mapIso
    (downSESIsodownSES₀ A) ≪≫ (aug_shortExactSequence R G).mapNatIso (tensorRightTensor A B).symm
  ShortComplex.shortExact_iff_of_iso e|>.2 <| shortExact_downSES' R G (A := A ⊗ B)

set_option linter.unusedFintypeInType false in
lemma shortExact_downSESTensorLeft [Fintype G] (A B : Rep R G) :
    ((downSES A).map (tensorLeft B)).ShortExact :=
  ShortComplex.shortExact_iff_of_iso ((downSES A).mapNatIso
    (BraidedCategory.tensorLeftIsoTensorRight B))|>.2 <|
    shortExact_downSESTensorRight A B
