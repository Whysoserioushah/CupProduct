import CupProduct.Cohomology.AugmentationModule
import CupProduct.Cohomology.Functors.UpDown
import Mathlib
import CupProduct.Mathlib.Algebra.Homology.ShortComplex.Rep

open CategoryTheory Rep.leftRegular MonoidalCategory

universe w u

variable (R G : Type u) [CommRing R] [Group G]

noncomputable section

abbrev upSES₀ [Fintype G] : ShortComplex (Rep R G) where
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
    (ModuleCat.ofHom <| upSES₀_retract R G) (by ext; simp [upSES₀, μ]) <|
    Functor.PreservesEpimorphisms.preserves (F := forget₂ _ _) (upSES₀ R G).g

open ShortComplex

def split_upSES' [Fintype G] : (((upSES₀ R G).map (tensorRight A)).map (forget₂ (Rep R G)
    (ModuleCat R))).Splitting := by
  rw [← map_comp, show (upSES₀ R G).map ((tensorRight A) ⋙ (forget₂ (Rep R G) (ModuleCat R))) =
    ((upSES₀ R G).map (forget₂ (Rep R G) (ModuleCat R))).map
    (tensorRight (ModuleCat.of R A.V)) by rfl]
  exact .map (split_upSES₀_forget R G) _

lemma shortExact_upSES' [Fintype G] : ((upSES₀ R G).map (tensorRight A)).ShortExact where
  exact := (exact_map_iff_of_faithful _ _).1 (split_upSES' R G (A := A)).exact
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
--   simp [mapToTensorinear, Representation.coind₁']

set_option backward.isDefEq.respectTransparency false in
lemma π_comp_forgetCokernelIso {A B : Rep.{u} R G} (f : A ⟶ B) :
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
  rw [← Category.assoc]
  have : (upSES A).f ≫ mapToTensor A = (λ_ _).inv ≫ μ R G ▷ A := by
    ext a
    simp [μ_apply _, sum_tmul, Finset.sum_equiv (Equiv.inv G)
      (f := fun i ↦ .single i⁻¹ (1 : R) ⊗ₜ a) (g := fun i ↦ (Finsupp.single i (1 : R) ⊗ₜ a))
      (s := Finset.univ) (t := Finset.univ) (by simp) (by simp)]
  rw [this, Category.assoc, ← comp_whiskerRight, cokernel.condition,
    MonoidalPreadditive.zero_whiskerRight, comp_zero]

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

set_option backward.isDefEq.respectTransparency false in
def coaugTensorToUp [Fintype G] (A : Rep R G) : coaug R G ⊗ A ⟶ up.obj A :=
  haveI : Epi ((upSES₀ R G).map (tensorRight A)).g := (shortExact_upSES' R G).3
  (shortExact_upSES' R G).1.desc (tensorToFun A ≫ cokernel.π _) <| by
  rw [← Category.assoc]
  have : ((upSES₀ R G).map (tensorRight A)).f ≫ tensorToFun A =
    (ofHom <| (Representation.TensorProduct.lid _ A.ρ).toIntertwiningMap) ≫ coind₁'_ι.app A := by
    ext : 2
    simp only [map_X₁, Functor.flip_obj_obj, curriedTensor_obj_obj, tensor_V, coind₁'_obj, tensor_ρ,
      map_X₂, map_f, Functor.flip_obj_map, curriedTensor_map_app, Rep.hom_comp, hom_ofHom,
      hom_whiskerRight, Representation.IntertwiningMap.comp_toLinearMap,
      Representation.tensorToFun_toLinearMap, Representation.IntertwiningMap.toLinearMap_rTensor,
      of_tensor, of_ρ', coind₁'_ι_app, Representation.TensorProduct.toLinearMap_lid]
    ext a g
    classical simp [μ_one _, Finsupp.single_apply]
      -- this is a counterexample where `(μ_one)` wouldn't work but `μ_one _` works
  rw [this, Category.assoc, cokernel.condition, comp_zero]

lemma tensorToFun'_mapToTensorLinear {R G : Type*} (M : Type*) [CommRing R] [Group G]
    [AddCommGroup M] [Module R M] [Fintype G] :
    lift (tensorToFun' (R := R) (G := G) M) ∘ₗ mapToTensorLinear = LinearMap.id := by
  ext; classical simp [Finsupp.single_apply]

lemma tensorToFun_mapToTensor [Fintype G] (A : Rep R G) : mapToTensor A ≫ tensorToFun A = 𝟙 _ := by
  ext : 2
  simp [tensorToFun'_mapToTensorLinear]

set_option backward.isDefEq.respectTransparency false in
lemma upToTensor_comp_inv [Fintype G] (A : Rep R G) : upToTensor A ≫ coaugTensorToUp A = 𝟙 _ := by
  have _ : Epi (upSES A).g := coequalizer.π_epi
  have _ : Epi ((upSES₀ R G).map (tensorRight A)).g := (shortExact_upSES' R G).3
  rw [← cancel_epi (upSES A).g, ← Category.assoc]
  change (_ ≫ Exact.desc _ _ _) ≫ (shortExact_upSES' R G).1.desc _ _ = _
  rw [Exact.g_desc, show cokernel.π (μ R G) ▷ A = ((upSES₀ R G).map (tensorRight A)).g by rfl,
    Category.assoc, Exact.g_desc, ← Category.assoc]
  simp [tensorToFun_mapToTensor]

lemma mapToTensorLinear_tensorToFun' {R G : Type*} (M : Type*) [CommRing R] [Group G]
    [AddCommGroup M] [Module R M] [Fintype G] :
    mapToTensorLinear (G := G) ∘ₗ lift (tensorToFun' (R := R) M) = LinearMap.id := by
  ext g m
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
    AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self, curry_apply, lift.tmul,
    tensorToFun'_apply, mapToTensorLinear_apply, tensorToFun''_apply, tmul_smul, LinearMap.id_coe]
  rw [id_eq, Finset.sum_eq_single_of_mem g⁻¹ (Finset.mem_univ _) (by
    simp +contextual [← inv_eq_iff_eq_inv (a := g), eq_comm]), inv_inv,
    Finsupp.single_eq_same, one_smul]

lemma mapToTensor_tensorToFun [Fintype G] (A : Rep R G) : tensorToFun A ≫ mapToTensor A = 𝟙 _ := by
  ext : 2
  simp [mapToTensorLinear_tensorToFun']

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
    simp [coind₁', mapToTensorLinear_apply]

@[reassoc]
lemma mapToTensor_naturality [Fintype G] {X Y : Rep R G} (f : X ⟶ Y) :
    coind₁'.map f ≫ mapToTensor Y = mapToTensor X ≫ leftRegular R G ◁ f :=
  @coindIsoTensorFunctor R G _ _ _ |>.hom.naturality f

set_option linter.unusedFintypeInType false

@[reassoc]
lemma tensorToFun_naturality [Fintype G] {X Y : Rep R G} (f : X ⟶ Y) :
    leftRegular R G ◁ f ≫ tensorToFun Y = tensorToFun X ≫ coind₁'.map f :=
  @coindIsoTensorFunctor R G _ _ _ |>.inv.naturality f

set_option backward.isDefEq.respectTransparency false in
lemma inv_comp_upToTensor [Fintype G] (A : Rep R G) : coaugTensorToUp A ≫ upToTensor A = 𝟙 _ := by
  haveI : Epi ((upSES₀ R G).map (tensorRight A)).g := (shortExact_upSES' R G).3
  simp only [up_obj, Functor.id_obj, coind₁'_obj, coaugTensorToUp, map_X₂, Functor.flip_obj_obj,
    curriedTensor_obj_obj, upToTensor, upSES_X₂]
  rw [← cancel_epi ((upSES₀ R G).map (tensorRight A)).g, ← Category.assoc, Exact.g_desc]
  simp only [map_X₂, Functor.flip_obj_obj, curriedTensor_obj_obj, Category.assoc, map_X₃, map_g,
    Functor.flip_obj_map, curriedTensor_map_app]
  change _ ≫ (upSES A).g ≫ _ = _
  rw [Exact.g_desc]
  simp [← Category.assoc, mapToTensor_tensorToFun]

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
  simp only [coequalizer_as_cokernel, Functor.id_obj, upTensor, Iso.trans_hom, whiskerRightIso_hom,
    upIsoCoaugTensor_hom, Iso.symm_hom, upIsoCoaugTensor_inv, coindTensor, coindIsoTensor_hom,
    coindIsoTensor_inv, Category.assoc]
  rw [← comp_whiskerRight_assoc, upToTensor]
  change ((upSES A).g ≫ _) ▷ B ≫ _ = _
  rw [Exact.g_desc, comp_whiskerRight_assoc]
  nth_rw 2 [← Category.assoc]
  rw [associator_naturality_left, Category.assoc, coaugTensorToUp]
  change _ ≫ _ ≫ ((upSES₀ R G).map (tensorRight (A ⊗ B))).g ≫ _ = _
  rw [Exact.g_desc]
  rfl

lemma upTensor_coind_comm' [Fintype G] (A B : Rep R G) :
    A ◁ up.π B ≫ (upTensor' A B).hom = (coindTensor' A B).hom ≫ up.π (A ⊗ B) := by
  dsimp only [upTensor', coindTensor', Iso.trans_hom]
  rw [BraidedCategory.braiding_naturality_right_assoc, upTensor_coind_comm_assoc]
  simp

-- TODO : make a shortcomplex iso between upSES (functor version) and (upSES₀ functor)

lemma exp {R : Type*} [CommSemiring R] {M N P Q : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N] [Module R P] [Module R Q]
    (ρ : Representation R G M) (σ : Representation R G N) (τ : Representation R G P)
    (υ : Representation R G Q) (f : ρ.IntertwiningMap τ) (g : σ.IntertwiningMap υ) :
    (f.rTensor υ).comp (g.lTensor ρ) = f.tensor g := by
  ext1; simp

-- this is now in mathlib and should be bumped away
lemma exp' {R : Type*} [CommSemiring R] {M N P Q : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N] [Module R P] [Module R Q]
    (ρ : Representation R G M) (σ : Representation R G N) (τ : Representation R G P)
    (υ : Representation R G Q) (f : ρ.IntertwiningMap τ) (g : σ.IntertwiningMap υ) :
    (g.lTensor τ).comp (f.rTensor σ) = f.tensor g := by
  ext1; simp

-- TODO : write `lTensor_comp` for `IntertwiningMap`
@[simps]
def upSES₀ShortComplex [Fintype G] : Rep R G ⥤ ShortComplex (Rep R G) where
  obj A := (upSES₀ R G).map (tensorRight A)
  map {A B} f := {
    τ₁ := _ ◁ f
    τ₂ := _ ◁ f
    τ₃ := _ ◁ f}
  map_id A := by ext <;> simp
  map_comp f g := by ext1 <;> simp

@[simps! hom_τ₁ hom_τ₂ hom_τ₃]
def upSESIsoupSES₀ [Fintype G] (A : Rep R G) :
    upSES A ≅ (upSES₀ R G).map (tensorRight A) :=
  ShortComplex.isoMk (mkIso (Representation.TensorProduct.lid _ A.ρ).symm) (coindIsoTensor A)
    (upIsoCoaugTensor A) (by
      ext : 2
      simp only [upSES_X₁, map_X₂, Functor.flip_obj_obj, curriedTensor_obj_obj, tensor_V, tensor_ρ,
        map_X₁, map_f, Functor.flip_obj_map, curriedTensor_map_app, Rep.hom_comp, hom_whiskerRight,
        mkIso_hom_hom, Representation.IntertwiningMap.comp_toLinearMap,
        Representation.IntertwiningMap.toLinearMap_rTensor, upSES_X₂, coind₁'_obj, upSES_f,
        coind₁'_ι_app, coindIsoTensor_hom, hom_ofHom, Representation.mapToTensor_toLinearMap]
      ext
      simp only [LinearMap.coe_comp, Representation.IntertwiningMap.coe_toLinearMap,
        Representation.Equiv.coe_toIntertwiningMap, Function.comp_apply,
        Representation.TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, μ_apply _, one_smul,
        mapToTensorLinear_apply, Representation.coind₁'_ι_apply, Function.const_apply, ← sum_tmul]
      rw [Finset.sum_equiv (f := fun i ↦ Finsupp.single i 1) (g := fun i ↦ Finsupp.single i⁻¹ 1)
        (t := Finset.univ) (Equiv.inv G) (by simp) (by simp)]) <| by
      dsimp [-coind₁'_ι_app, upToTensor, -upSES_g]
      haveI : Epi (upSES A).g := coequalizer.π_epi
      exact ((shortExact_upSES A).1.g_desc _ _ ).symm

set_option backward.isDefEq.respectTransparency false in
def upSESIsoupSES₀Functor [Fintype G] :
    upShortComplex (G := G) ≅ upSES₀ShortComplex (R := R) :=
  NatIso.ofComponents upSESIsoupSES₀ fun {X Y} f ↦ by
    ext1
    · ext; simp
    · exact mapToTensor_naturality f
    · exact upToTensor_naturality f

lemma shortExact_upSESTensorRight [Fintype G] (A B : Rep R G) :
    ((upSES B).map (tensorRight A)).ShortExact :=
  have e := (tensorRight A).mapShortComplex.mapIso (upSESIsoupSES₀ B)
    ≪≫ (upSES₀ R G).mapNatIso (tensorRightTensor _ _).symm
  ShortComplex.shortExact_iff_of_iso e|>.2 <| shortExact_upSES' R G (A := B ⊗ A)

lemma shortExact_upSESTensorLeft [Fintype G] (A B : Rep R G) :
    ((upSES B).map (tensorLeft A)).ShortExact :=
  ShortComplex.shortExact_iff_of_iso ((upSES B).mapNatIso
    (BraidedCategory.tensorLeftIsoTensorRight _))|>.2 <|
    shortExact_upSESTensorRight A B

instance [Fintype G] (A B : Rep R G) : TrivialTateCohomology ((upSES B).map (tensorRight A)).X₂ :=
  TrivialTateCohomology.of_iso (coindTensor B A : _ ≅ coind₁'.obj (B ⊗ A))

instance [Fintype G] (A B : Rep R G) {n : ℤ} : IsIso (groupCohomology.TateCohomology.δ
    (shortExact_upSESTensorRight A B) n) :=
  ShortComplex.ShortExact.isIso_δ _ _ _ _
    isZero_of_trivialTateCohomology isZero_of_trivialTateCohomology

@[simps! hom]
def δUpIsoTateTensorRight [Fintype G] (A B : Rep R G) {n : ℤ} :
    (groupCohomology.tateCohomology n).obj ((up.{u, u}.obj B) ⊗ A) ≅
    (groupCohomology.tateCohomology (n + 1)).obj (B ⊗ A) :=
  @asIso _ _ _ _ (groupCohomology.TateCohomology.δ
    (shortExact_upSESTensorRight A B) n) <| instIsIsoModuleCatδ A B (n := n)

instance up_preservesEpi : (up (R := R) (G := G)).PreservesEpimorphisms where
  preserves f hf :=
    haveI : Epi (coind₁'.map f) := Rep.epi_iff_surjective _|>.2 fun y ↦
      ⟨(Function.surjInv (Rep.epi_iff_surjective _|>.1 hf)) ∘ y, by
        funext g
        change (_ ∘ _) g = _
        simp [Function.surjInv_eq]⟩
    cokernel.desc_epi _ _ _

instance up_preservesMono [Fintype G] :
    Functor.PreservesMonomorphisms (up.{u, u} (R := R) (G := G)) :=
  haveI : (tensorLeft (coaug R G)).PreservesMonomorphisms := ⟨fun f hf ↦
    Rep.mono_iff_injective _ |>.2 <| Module.Flat.lTensor_preserves_injective_linearMap
      f.hom.toLinearMap (Rep.mono_iff_injective _|>.1 hf)⟩
  CategoryTheory.Functor.preservesMonomorphisms.of_iso
    (upIsoCoaugTensorFunctor (R := R) (G := G)).symm

instance : coind₁' (R := R) (G := G).PreservesZeroMorphisms := ⟨fun _ ↦ congrFun rfl⟩

instance : (up (R := R) (G := G)).PreservesZeroMorphisms := ⟨fun X Y ↦ by
  simp only [up_obj, Functor.id_obj, coind₁'_obj, coind₁'_ι_app, up_map, Functor.map_zero]
  convert cokernel.desc_zero (coind₁'_ι.app X)
  · exact zero_comp
  · exact comp_zero⟩

instance up_preservesHomology [Fintype G] : (up.{u, u} (R := R) (G := G)).PreservesHomology :=
    up.preservesHomology_of_map_exact fun S hS ↦ by
  have := S.mapNatIso upIsoCoaugTensorFunctor
  refine ShortComplex.exact_of_iso (S.mapNatIso upIsoCoaugTensorFunctor).symm ?_
  refine ((S.map (tensorLeft _)).exact_map_iff_of_faithful
    (F := forget₂ (Rep R G) (ModuleCat R))).1 ?_
  change ((S.map (forget₂ (Rep R G) _)).map (tensorLeft (ModuleCat.of R (coaug R G).V))).Exact
  exact Module.Flat.lTensor_shortComplex_exact (ModuleCat.of R (coaug R G).V) _
      (hS.map_of_preservesLeftHomologyOf _)

set_option backward.isDefEq.respectTransparency false in
instance : coind₁' (R := R) (G := G).Additive where
  map_add {_ _ _ _} := by
    ext : 2
    simp [coind₁', Rep.add_hom]
    -- TODO : add lemma to `LinearMap.compLeft`
    rfl

instance : up (R := R) (G := G).Additive where
  map_add {X Y f g} := by
    rw [← cancel_epi (cokernel.π (coind₁'_ι.app X)), up_map, cokernel.π_desc,
      up_map, up_map, comp_add, cokernel.π_desc, cokernel.π_desc, coind₁'.map_add, add_comp]

lemma map_up_shortExact [Fintype G] (S : ShortComplex (Rep R G)) (hS : S.ShortExact) :
    (S.map up.{u, u}).ShortExact where
  exact := by
    have := ((up (R := R) (G := G)).exact_tfae.out 1 2|>.2 up_preservesHomology)
    exact this _ hS.1
  mono_f :=
    have := hS.2
    up_preservesMono.preserves S.f
  epi_g :=
    have := hS.3
    up_preservesEpi.preserves _
