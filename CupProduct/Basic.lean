import Mathlib
import CupProduct.UpIso

open CategoryTheory groupCohomology Rep.dimensionShift

universe u

variable (R G : Type u) [CommRing R] [Group G] (A B : Rep R G)

open MonoidalCategory

variable {R G}

lemma mem_tensorInvariants (a : A.ρ.invariants) (b : B.ρ.invariants) :
  ∀ g : G, ((A ⊗ B).ρ g) (a.1 ⊗ₜ b.1) = a.1 ⊗ₜ b.1 := by
  intro g
  simp only [Action.tensorObj_V, Rep.tensor_ρ, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj]
  erw [Representation.tprod_apply, TensorProduct.map_tmul]
  rw [a.2, b.2]

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

noncomputable def cup0' : H0 A ⊗ H0 B ⟶ H0 (A ⊗ B) :=
  ModuleCat.ofHom <| TensorProduct.lift (cup0 A B)

@[simp]
lemma cup0_apply (a : H0 A) (b : H0 B) : cup0 A B a b = (H0Iso (A ⊗ B)).inv
  ⟨((H0Iso A).hom.hom a).1 ⊗ₜ ((H0Iso B).hom b).1, mem_tensorInvariants A B
    (H0Iso A|>.hom.hom a) (H0Iso B|>.hom.hom b)⟩ := rfl

structure IsCupProduct (map : (p q r : ℕ) → (h : r = p + q) → (A B : Rep R G) →
    groupCohomology A p ⊗ groupCohomology B q ⟶ groupCohomology (A ⊗ B) r) : Prop where
  zero : map 0 0 0 rfl = cup0'
  commSq1 (p q : ℕ) (S1 : ShortComplex (Rep R G)) (h1 : S1.ShortExact)
    (h2 : (S1.map (tensorRight B)).ShortExact) :
    map p q (p + q) rfl S1.X₃ B ≫ δ h2 (p + q) (p + q + 1) rfl =
    (δ h1 p (p + 1) rfl ⊗ₘ 𝟙 _) ≫ map (p + 1) q (p + q + 1) (by omega) S1.X₁ B
  commSq2 (p q : ℕ) (S2 : ShortComplex (Rep R G)) (h1 : S2.ShortExact)
    (h2 : (S2.map (tensorLeft A)).ShortExact) :
    map p q (p + q) rfl A S2.X₃ ≫ δ h2 (p + q) (p + q + 1) rfl =
    (-1 : R) ^ p • (𝟙 _ ⊗ₘ δ h1 q (q + 1) rfl) ≫ map p (q + 1) (p + q + 1) (by omega) A S2.X₁

noncomputable section

open Limits

lemma commSq11 (σ : H0 B) : @groupCohomology.map R G G _ _ _ (Rep.of A.ρ.coind₁') (up.obj A)
    (MonoidHom.id G) (up.π A) 0 ≫ ModuleCat.ofHom ((cup0 (up.obj A) B).flip σ) =
    ModuleCat.ofHom ((cup0 (Rep.coind₁'.obj A) B).flip σ) ≫ (functor R G 0).map
    (cokernel.π _ ▷ B) := by
  apply_fun (fun f ↦ (H0Iso (Rep.coind₁'.obj A)).inv ≫ f ≫ (H0Iso (up.obj A ⊗ B)).hom) using
    (by aesop_cat)
  simp only [Category.assoc]
  ext1
  simp only [Rep.coind₁'_obj, Rep.of_ρ, up_obj, Functor.id_obj, Action.tensorObj_V, Rep.tensor_ρ,
    coequalizer_as_cokernel, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.of_coe, functor_map,
    map_id_comp_H0Iso_hom, Rep.invariantsFunctor_map_hom, Action.whiskerRight_hom, comp_codRestrict]
  ext ⟨a, ha⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, flip_apply, cup0_apply, Action.tensorObj_V,
    Rep.tensor_ρ, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, map_id_comp_H0Iso_hom_apply, Rep.of_ρ,
    Iso.inv_hom_id_apply, codRestrict_apply, Submodule.coe_subtype, ToType]
  simp only [Rep.invariantsFunctor, Rep.of_ρ]
  change (Subtype.val (((H0Iso (Rep.of A.ρ.coind₁')).hom ≫ (ModuleCat.ofHom _)).hom _)) ⊗ₜ[R] _ = _
  simp only [Rep.of_ρ, ModuleCat.hom_comp, ModuleCat.hom_ofHom, comp_codRestrict, codRestrict_apply,
    LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply, Iso.inv_hom_id_apply,
    ModuleCat.hom_whiskerRight]
  erw [rTensor_tmul]

variable [Fintype G]

open Rep.leftRegular

lemma commSq12 : (functor R G 0).map (up.π A ▷ B) ≫ groupCohomology.map (MonoidHom.id G)
    (upTensor A B).hom 0 = ((functor R G 0).mapIso (coindTensor A B)).hom ≫
    (functor R G 0).map (up.π (A ⊗ B)) := by
  simp only [Rep.coind₁'_obj, functor_obj, up_obj, Functor.id_obj, Action.tensorObj_V, Rep.tensor_ρ,
    coequalizer_as_cokernel, functor_map, Functor.mapIso_hom, ← map_comp]
  congr 1
  simp only [upTensor, up_obj, Functor.id_obj, Rep.coind₁'_obj, Action.tensorObj_V, Rep.tensor_ρ,
    Iso.trans_hom, whiskerRightIso_hom, upIsoCoaugTensor_hom, upToTensor, upSES_X₂, Iso.symm_hom,
    upIsoCoaugTensor_inv, coaugTensorToUp, ShortComplex.map_X₂, Functor.flip_obj_obj,
    curriedTensor_obj_obj]
  change (up.π A ▷ B) ≫ _ = (coindTensor A B).hom ≫ _
  simp only [Rep.coind₁'_obj, up_obj, Functor.id_obj, coequalizer_as_cokernel, Action.tensorObj_V,
    Rep.tensor_ρ, coindTensor, Iso.trans_hom, whiskerRightIso_hom, coindIsoTensor_hom, Iso.symm_hom,
    coindIsoTensor_inv, Category.assoc]
  rw [← Category.assoc, ← comp_whiskerRight]
  change ((upSES A).g ≫ _) ▷ _ ≫ _ = _
  rw [ShortComplex.Exact.g_desc]
  simp only [upSES_X₂, Rep.coind₁'_obj, comp_whiskerRight, Category.assoc]
  nth_rw 2 [← Category.assoc]
  have : ((upSES₀ R G).map (tensorRight (A ⊗ B))).g =
    (α_ _ A B).inv ≫ (cokernel.π (μ R G)) ▷ A ▷ B ≫
    (α_ (Rep.leftRegular.coaug R G) A B).hom := by simp [upSES₀]
  rw [← Category.id_comp (cokernel.π (μ R G) ▷ A ▷ B),
    ← comp_inv_eq_id (α_ (Rep.leftRegular R G) A B).hom|>.2 rfl]
  simp only [IsIso.Iso.inv_hom, Category.assoc]
  nth_rw 3 [← Category.assoc, ← Category.assoc]
  erw [← this]
  rw [ShortComplex.Exact.g_desc]

def cup1aux (σ : H0 B) : H1 A ⟶ H1 (A ⊗ B) := by
  haveI : Epi (mapShortComplex₃ (shortExact_upSES A) (Nat.zero_add 1)).g :=
    δ_up_zero_epi A
  refine (mapShortComplex₃_exact (shortExact_upSES A) (Nat.zero_add 1)).desc
    ((ModuleCat.ofHom ((cup0 (up.obj A) B).flip σ)) ≫
    ((groupCohomology.functor R G _).mapIso (upTensor A B)).hom ≫
    (δ (shortExact_upSES (A ⊗ B)) 0 1 rfl : _ ⟶ H1 (A ⊗ B))) ?_
  -- dsimp
  change groupCohomology.map _ _ 0 ≫ _ = 0
  dsimp [-up_obj]
  rw [← Category.assoc, commSq11, ← Category.assoc]
  nth_rw 2 [Category.assoc]
  rw [commSq12]
  simp only [up_obj, Functor.id_obj, Rep.coind₁'_obj, Action.tensorObj_V, Rep.tensor_ρ,
    ModuleCat.of_coe, functor_obj, Functor.mapIso_hom, functor_map, coequalizer_as_cokernel,
    Category.assoc]
  sorry

noncomputable def CupProduct [Fintype G] (p q r : ℕ) (h : r = p + q) (A B : Rep R G) :
    -- do I want the aditional r = p + q condition?
    groupCohomology A p ⊗ groupCohomology B q ⟶ groupCohomology (A ⊗ B) r :=
  match p, q with
  | 0, 0 => cup0' A B ≫ eqToHom (by rw [h])
  | _, 1 => sorry--(sorry : _ ⟶ groupCohomology (A ⊗ B) 1) ≫ eqToHom _
  | 1, q => sorry
  | (n + 2), q => (δUpIso A n).inv ▷ (groupCohomology B q) ≫
    CupProduct (n + 1) q (n + q + 1) (by omega) (up.obj A) B ≫
    ((functor R G (n + q + 1)).mapIso (upTensor A B)).hom ≫
    (δUpIso (A ⊗ B) (n + q)).hom ≫ eqToHom (by rw [h, add_assoc, add_comm q, ← add_assoc])
  | p, (n + 2) => sorry
