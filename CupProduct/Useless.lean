import Mathlib
import CupProduct.Cohomology.AugmentationModule
import CupProduct.Cohomology.Functors.UpDown

open CategoryTheory

variable {R G : Type u} [CommRing R] [Group G] (A : Rep R G)

noncomputable def groupCohomology.cast {n m} (h : n = m) :
  groupCohomology A n ≅ groupCohomology A m := h ▸ Iso.refl _

noncomputable def Representation.coind₁'_ι_range_iso_A [h : Nonempty G] [Fintype G] (A : Rep R G) :
    A ≃ₗ[R] (Representation.coind₁'_ι (R := R) (G := G) (V := A)).range where
  toFun a := ⟨Function.const G a, by simp [coind₁'_ι]⟩
  map_add' := by simp
  map_smul' := by simp
  invFun f := f.1 h.some
  left_inv x := by simp
  right_inv := fun ⟨x, ⟨f, hf⟩⟩ ↦ by simp [← hf, coind₁'_ι]

@[simps]
def Submodule.const {R M ι : Type*} [h : Nonempty ι] [Semiring R] [AddCommMonoid M] [Module R M] :
    Submodule R (ι → M) where
  carrier := Set.range (Function.const ι)
  add_mem' {f1 f2} h1 h2 := ⟨f1 h.some + f2 h.some, by aesop⟩
  zero_mem' := by simp
  smul_mem' := by simp

lemma Representation.coind₁'_ι_range [h : Nonempty G] (A : Rep R G) :
    Representation.coind₁'_ι (R := R) (G := G) (V := A).range = Submodule.const := by
  ext; simp  [coind₁'_ι, Submodule.const]

lemma Submodule.equiv_const {R M ι ι' : Type*} [h : Nonempty ι] [h' : Nonempty ι']
    [Semiring R] [AddCommMonoid M] [Module R M] (e : ι ≃ ι') :
    Submodule.const.map (LinearEquiv.funCongrLeft R M e.symm).toLinearMap =
    Submodule.const := by
  ext f
  simp [const, ← Function.const_comp (α := ι) (f := e), LinearMap.funLeft, ← Equiv.comp_symm_eq,
    Function.comp_assoc, Equiv.self_comp_symm, -Function.const_comp]

noncomputable section

open MonoidalCategory

def Rep.trivialTensorIso (A : Rep R G) : A ≅ Rep.trivial R G R ⊗ A :=
  mkIso _ _ (LinearEquiv.toModuleIso (TensorProduct.lid R A).symm) fun g x ↦ by
  simp only [Action.tensorObj_V, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom, tensor_ρ, of_ρ]
  erw [TensorProduct.lid_symm_apply]

lemma ModuleCat.of_tensor {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M]
    [Module R N] : ModuleCat.of R (TensorProduct R M N) =
    (ModuleCat.of R M) ⊗ (ModuleCat.of R N) := by rfl

lemma ModuleCat.of_carrier {R M} [Ring R] [AddCommGroup M] [Module R M] :
    (ModuleCat.of R M) = M := rfl

open TensorProduct in
@[simps!]
def Rep.coindIsoTensor [Fintype G] (A : Rep R G) :
    Rep.leftRegular R G ⊗ A ≅ Rep.coind₁'.obj A  :=
  open scoped Classical in
  mkIso _ _ (finsuppScalarLeft R A G ≪≫ₗ Finsupp.mapDomain.linearEquiv A.V R (Equiv.inv G) ≪≫ₗ
    Finsupp.linearEquivFunOnFinite R A G).toModuleIso fun g x ↦ by
  dsimp at x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f y =>
    change G →₀ R at f
    simp only [coind₁'_obj, Action.tensorObj_V, LinearEquiv.toModuleIso_hom,
      ModuleCat.hom_ofHom, tensor_ρ, of_ρ, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      Finsupp.mapDomain.coe_linearEquiv, Equiv.inv_apply]
    ext i
    simp only [Finsupp.linearEquivFunOnFinite_apply, Representation.coind₁'_apply_apply]
    rw [← inv_inv (i * g), ← inv_inv i, Finsupp.mapDomain_apply inv_injective,
      Finsupp.mapDomain_apply inv_injective]
    classical
    erw [Representation.tprod_apply, TensorProduct.map_tmul,
      finsuppScalarLeft_apply_tmul_apply, finsuppScalarLeft_apply_tmul_apply]
    simp
  | add x y h1 h2 =>
    dsimp at h1 h2 ⊢
    simp [h1, h2, Finsupp.mapDomain_add]

open TensorProduct in
def Rep.coindIsoTensorFunctor [Fintype G] :
    MonoidalCategory.tensorLeft (Rep.leftRegular R G) ≅ Rep.coind₁' :=
  NatIso.ofComponents Rep.coindIsoTensor <| fun {X Y} f ↦ by
  ext : 2
  simp only [curriedTensor_obj_obj, Action.tensorObj_V, coind₁'_obj, curriedTensor_obj_map,
    coindIsoTensor, Action.comp_hom, Action.whiskerLeft_hom, mkIso_hom_hom,
    LinearEquiv.toModuleIso_hom, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
  ext1 fx
  induction fx using TensorProduct.induction_on with
  | zero => simp
  | tmul f' x =>
    simp only [ModuleCat.hom_whiskerLeft, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.trans_apply, Finsupp.mapDomain.coe_linearEquiv,
      Equiv.inv_apply, coind₁', ModuleCat.hom_ofHom]
    ext i
    simp only [Finsupp.linearEquivFunOnFinite_apply, LinearMap.compLeft, coe_hom, LinearMap.coe_mk,
      AddHom.coe_mk, Function.comp_apply]
    rw [← inv_inv i, Finsupp.mapDomain_apply inv_injective, Finsupp.mapDomain_apply inv_injective]
    classical
    erw [finsuppScalarLeft_apply_tmul_apply, finsuppScalarLeft_apply_tmul_apply]
    simp
  | add x y h1 h2 =>
    dsimp at h1 h2 ⊢
    simp [map_add, Finsupp.mapDomain_add, h1, h2]

open Limits Rep.dimensionShift

def upIsoCokernelrTensor [Fintype G] (A : Rep R G) : up.obj A ≅
    cokernel (Rep.leftRegular.μ R G ⊗ₘ 𝟙 A) :=
  cokernel.mapIso _ _ (Rep.trivialTensorIso A) (Rep.coindIsoTensor A).symm <| by
  classical
  rw [Iso.symm_hom]
  apply_fun (· ≫ A.coindIsoTensor.hom) using (by aesop_cat)
  simp only [Functor.id_obj, Rep.coind₁'_obj, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    tensorHom_id]
  ext : 2
  simp only [Functor.id_obj, Rep.coind₁'_obj, Rep.coind₁'_ι_app_hom, ModuleCat.hom_ofHom,
    Rep.trivialTensorIso, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, Action.comp_hom, Action.tensorObj_V,
    Rep.mkIso_hom_hom, LinearEquiv.toModuleIso_hom, Action.whiskerRight_hom, ModuleCat.hom_comp]
  apply_fun (· ∘ₗ (TensorProduct.lid R ↑A.V).toLinearMap) using
    (fun _ _ ↦ LinearEquiv.eq_comp_toLinearMap_iff _ _|>.1)
  simp only [LinearMap.comp_assoc, LinearEquiv.symm_comp, LinearMap.comp_id,
    ModuleCat.hom_whiskerRight]
  ext a : 3
  simp only [Representation.coind₁'_ι, TensorProduct.AlgebraTensorModule.curry_apply,
    LinearMap.restrictScalars_self, TensorProduct.curry_apply, LinearMap.coe_comp,
    LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.lid_tmul, one_smul, Rep.coindIsoTensor,
    Rep.coind₁'_obj, Rep.mkIso_hom_hom, Action.tensorObj_V, LinearEquiv.toModuleIso_hom,
    ModuleCat.hom_ofHom, LinearEquiv.trans_apply, Finsupp.mapDomain.coe_linearEquiv,
    Equiv.inv_apply]
  erw [LinearMap.rTensor_tmul]
  ext i
  simp only [Function.const_apply, Rep.leftRegular.μ, map_sum, LinearMap.lsmul_flip_apply,
    ModuleCat.hom_ofHom, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.toSpanSingleton_apply, one_smul,
    Finsupp.linearEquivFunOnFinite_apply]
  rw [← inv_inv i, Finsupp.mapDomain_apply inv_injective]
  erw [TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  simp [Rep.leftRegular.of]
