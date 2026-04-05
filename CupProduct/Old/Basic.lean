import Mathlib

open CategoryTheory groupCohomology --Rep.dimensionShift

universe u

variable (R G : Type u) [CommRing R] [Group G] (A B : Rep R G)

open MonoidalCategory

variable {R G}

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

noncomputable def cup0' : H0 A ⊗ H0 B ⟶ H0 (A ⊗ B) :=
  ModuleCat.ofHom <| TensorProduct.lift (cup0 A B)

@[simp]
lemma cup0_apply (a : H0 A) (b : H0 B) : cup0 A B a b = (H0Iso (A ⊗ B)).inv.hom
  ⟨((H0Iso A).hom.hom a).1 ⊗ₜ ((H0Iso B).hom.hom b).1, mem_tensorInvariants A B
    (H0Iso A|>.hom.hom a) (H0Iso B|>.hom.hom b)⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
lemma map_id_tensor_comp_H0Iso_inv {M1 M2 N1 N2 : Rep R G} (f : M1 ⟶ M2) (g : N1 ⟶ N2) :
    (Rep.invariantsFunctor R G).map (f ⊗ₘ g) ≫ (H0Iso (M2 ⊗ N2)).inv =
    (H0Iso (M1 ⊗ N1)).inv ≫ map (MonoidHom.id G) (f ⊗ₘ g) 0 := by
  apply_fun (fun f ↦ (H0Iso (M1 ⊗ N1)).hom ≫ f ≫ (H0Iso (M2 ⊗ N2)).hom) using by aesop_cat
  simp only [← Category.assoc, (Iso.hom_comp_eq_id (H0Iso _)).2 rfl, Category.id_comp]
  rw [map_id_comp_H0Iso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

lemma map_id_tensor_comp_H0Iso_inv_apply {M1 M2 N1 N2 : Rep R G} (f : M1 ⟶ M2) (g : N1 ⟶ N2)
    (x : (M1 ⊗ N1).ρ.invariants) :
    ((H0Iso (M2 ⊗ N2)).inv.hom (((Rep.invariantsFunctor R G).map (f ⊗ₘ g)).hom x)) =
    (map (MonoidHom.id G) (f ⊗ₘ g) 0).hom ((H0Iso (M1 ⊗ N1)).inv.hom x) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← map_id_tensor_comp_H0Iso_inv]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma smallcommSq1 {M N : Rep R G} (φ : M ⟶ N) : (Rep.invariantsFunctor R G).map (A ◁ φ) ≫
    (H0Iso (A ⊗ N)).inv = (H0Iso (A ⊗ M)).inv ≫
    groupCohomology.map (MonoidHom.id G) (A ◁ φ) 0 := by
  apply_fun (fun f ↦ (H0Iso _).hom ≫ f ≫ (H0Iso _).hom) using by aesop_cat
  simp [map_id_comp_H0Iso_hom]

lemma smallcommSq1_apply {M N : Rep R G} (φ : M ⟶ N) (x : (A ⊗ M).ρ.invariants) :
    (H0Iso (A ⊗ N)).inv.hom (((Rep.invariantsFunctor R G).map (A ◁ φ)).hom x) =
    (groupCohomology.map (MonoidHom.id G) (A ◁ φ) 0).hom ((H0Iso (A ⊗ M)).inv.hom x) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← smallcommSq1]
  rfl

noncomputable section

set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
def cup0NatTrans' : .prod (functor R G 0) (functor R G 0) ⋙ tensor (ModuleCat R) ⟶
    tensor (Rep R G) ⋙ functor R G 0 where
  app MN := cup0' MN.1 MN.2
  naturality {MN MN'} := fun ⟨f1, f2⟩ ↦ by
    dsimp
    ext1
    simp only [ModuleCat.hom_comp, ModuleCat.hom_tensorHom]
    refine TensorProduct.ext' fun m n ↦ by
      simp only [ModuleCat.MonoidalCategory.tensorObj_carrier, cup0', ModuleCat.hom_ofHom, coe_comp,
        Function.comp_apply, map_tmul]
      conv_lhs =>
        tactic => with_reducible convert lift.tmul .. -- why would this work and `rw` doesn't?
      rw [cup0_apply]
      dsimp
      conv_rhs => enter [2]; tactic => with_reducible convert lift.tmul ..
      conv_rhs => rw [cup0_apply]
      conv_rhs => tactic => with_reducible
        convert (map_id_tensor_comp_H0Iso_inv_apply f1 f2 ..).symm
      congr 1
      ext1
      simp [Rep.invariantsFunctor]

variable (R G) in
abbrev cup0NatTrans :=
  Functor.curry.map <| @cup0NatTrans' R G _ _

abbrev cup0NatTransLeft := cup0NatTrans R G|>.app A

-- #check tensorLeft
-- lemma cup0Left_naturality {B1 B2 : Rep R G} (f : B1 ⟶ B2) (σ : H0 A) : ({
--   app B := ModuleCat.ofHom <| TensorProduct.mk _ _ _ σ
--   naturality X Y f := by ext; simp [ModuleCat.hom_whiskerLeft]; erw [TensorProduct.mk_apply]
-- } : functor R G 0 ⟶ _) ≫ (cup0NatTransLeft A) = _ := by sorry

-- @[simps! obj map_app_app]
-- def Functor.flipFunctor {C D E : Type*} [Category C] [Category D] [Category E] :
--     (C ⥤ D ⥤ E) ⥤ (D ⥤ C ⥤ E) where
--   obj F := F.flip
--   map {X Y} f := {
--     app M := {
--       app N := (f.app N).app M
--       naturality {X' Y'} f' := by
--         dsimp
--         rw [← NatTrans.comp_app, ← NatTrans.comp_app]
--         congr 1
--         exact f.naturality _
--     }
--     naturality {X' Y'} f' := by
--       ext M
--       dsimp [NatTrans.comp_app]
--       exact (f.app M).naturality _
--   }

abbrev cup0NatTransRight := (CategoryTheory.flipFunctor _ _ _).map (cup0NatTrans R G)

lemma cup0_naturality {M1 M2 N1 N2 : Rep R G} (f : M1 ⟶ N1) (g : M2 ⟶ N2) :
    (groupCohomology.map (MonoidHom.id G) f 0 ⊗ₘ groupCohomology.map (MonoidHom.id G) g 0) ≫
    (cup0NatTrans R G|>.app N1).app N2 = (cup0NatTrans R G|>.app M1).app M2 ≫
    groupCohomology.map (MonoidHom.id G) (f ⊗ₘ g) 0 := by
  -- have := ((cup0NatTrans.app M1).app M2)  --⟨M1, M2⟩ ⟨N1, N2⟩ ⟨f, g⟩
  -- dsimp at this
  sorry

-- lemma cup0_naturality_left {M N P : Rep R G} (f : M ⟶ N) :
--     (groupCohomology.map (MonoidHom.id G) f 0 ▷ H0 P) ≫ cup0NatTrans.app (N, P) =
--     cup0NatTrans.app (M, P) ≫ groupCohomology.map (MonoidHom.id G) (f ▷ P) 0 := by
--   convert cup0_naturality f (𝟙 _)
--   simp
#exit
-- def ModuleCat.tensorRightHom {X Y : ModuleCat R} (x : X) :
--     Y ⟶ X ⊗ Y := ModuleCat.ofHom (TensorProduct.mk R X Y x)

-- noncomputable abbrev cup0NatTransLeft (σ : H0 A) :
--     functor R G 0 ⟶ tensorLeft A ⋙ functor R G 0 := sorry
--   -- ModuleCat.ofHom (TensorProduct.mk _ _ _ σ) ≫ (cup0NatTrans.app ⟨A, B⟩ : H0 A ⊗ H0 B ⟶ _)

-- noncomputable abbrev cup0NatTransRight (σ : H0 B) :
--     functor R G 0 ⟶ tensorRight B ⋙ functor R G 0 := sorry

-- -- #check .prod ()
--   -- ModuleCat.ofHom (flip (TensorProduct.mk _ _ _ σ)) ≫ (cup0NatTrans.app ⟨A, B⟩ : H0 A ⊗ H0 B ⟶ _)

-- #exit
-- noncomputable def cup0NatTrans (σ : H0 A) : functor R G 0 ⟶ tensorLeft A ⋙ functor R G 0 where
--   app B := ModuleCat.ofHom <| cup0 A B σ
--   naturality {M N} φ := by
--     dsimp
--     ext x
--     simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
--       cup0_apply, Action.tensorObj_V, Rep.tensor_ρ, Equivalence.symm_inverse,
--       Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
--       ]
--     conv_rhs => erw [← smallcommSq1_apply A φ]
--     congr 1
--     ext1
--     simp only [map_id_comp_H0Iso_hom_apply, Rep.invariantsFunctor_map_hom, Action.tensorObj_V,
--       Rep.tensor_ρ, Action.whiskerLeft_hom]
--     conv_rhs => erw [codRestrict_apply]
--     rw [LinearMap.comp_apply]
--     erw [Submodule.subtype_apply]
--     simp only [ModuleCat.MonoidalCategory.whiskerLeft_apply, Rep.hom_apply]
--     congr 1

-- noncomputable def cup0NatTrans' (σ : H0 B) : functor R G 0 ⟶ tensorRight B ⋙ functor R G 0 where
--   app A := ModuleCat.ofHom <| flip (cup0 A B) σ
--   naturality {M N} φ := by
--     dsimp
--     ext x
--     simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
--       flip_apply, cup0_apply, Action.tensorObj_V, Rep.tensor_ρ, Equivalence.symm_inverse,
--       Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
--       map_id_comp_H0Iso_hom_apply]
--     -- need a right version of smallcommSq1
--     -- conv_rhs => erw [← smallcommSq1_apply B φ]
--     -- congr 1
--     -- ext1
--     -- simp only [map_id_comp_H0Iso_hom_apply, Rep.invariantsFunctor_map_hom, Action.tensorObj_V,
--     --   Rep.tensor_ρ, Action.whiskerLeft_hom]
--     -- conv_rhs => erw [codRestrict_apply]
--     -- rw [LinearMap.comp_apply]
--     -- erw [Submodule.subtype_apply]
--     -- simp only [ModuleCat.MonoidalCategory.whiskerRight_apply, Rep.hom_apply]
--     -- congr 1
--     sorry

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

variable [Fintype G]

open Rep.leftRegular

lemma commSq12 : (functor R G 0).map (up.π A ▷ B) ≫ (functor R G 0).map
    (upTensor A B).hom = ((functor R G 0).mapIso (coindTensor A B)).hom ≫
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

lemma ModuleCat.ofHom_add {M N : ModuleCat R} (f g : M →ₗ[R] N) :
    ModuleCat.ofHom (f + g) = ModuleCat.ofHom f + ModuleCat.ofHom g := rfl

lemma ModuleCat.ofHom_smul (r : R) {M N : ModuleCat R} (f : M →ₗ[R] N) :
  ModuleCat.ofHom (r • f) = r • ModuleCat.ofHom f := rfl

def cup1Aux0 (σ : H0 B) : H1 A ⟶ H1 (A ⊗ B) := by
  haveI : Epi (mapShortComplex₃ (shortExact_upSES A) (Nat.zero_add 1)).g :=
    δ_up_zero_epi A
  refine (mapShortComplex₃_exact (shortExact_upSES A) (Nat.zero_add 1)).desc
    ((ModuleCat.ofHom <| (TensorProduct.mk R (H0 (up.obj A)) _).flip σ) ≫
      (cup0NatTrans.app ⟨up.obj A, B⟩) ≫ map (MonoidHom.id G) (upTensor A B).hom _
      ≫ δ (shortExact_upSES (A ⊗ B)) 0 1 rfl) ?_
  change (functor R G 0).map (up.π _) ≫ _ = 0
  rw [← Category.assoc, show (functor R G 0).map (up.π A) ≫ ModuleCat.ofHom
    ((TensorProduct.mk R ↑(H0 (up.obj A)) ↑(H0 B)).flip σ) = (ModuleCat.ofHom <|
    (TensorProduct.mk R (H0 (Rep.coind₁'.obj A)) (H0 B)).flip σ) ≫
    groupCohomology.map (MonoidHom.id G) (up.π A) 0 ▷ H0 B by rfl,
    Category.assoc]
  nth_rw 2 [← Category.assoc]
  rw [cup0_naturality_left (P := B) (up.π A), Category.assoc]
  nth_rw 3 [← Category.assoc]
  rw [← map_id_comp, upTensor_coind_comm, map_id_comp, Category.assoc]
  have : groupCohomology.map (MonoidHom.id G) _ 0 ≫ δ (shortExact_upSES (A ⊗ B)) 0 1 _ = 0 :=
    (mapShortComplex₃ (shortExact_upSES (A ⊗ B)) (Nat.zero_add 1)).zero
  simp_all

lemma cup1Aux0_add (σ1 σ2 : H0 B) : cup1Aux0 A B (σ1 + σ2) =
    cup1Aux0 A B σ1 + cup1Aux0 A B σ2 := by
  haveI : Epi (mapShortComplex₃ (shortExact_upSES A) (Nat.zero_add 1)).g :=
    δ_up_zero_epi A
  rw [← cancel_epi (mapShortComplex₃ (shortExact_upSES A) (Nat.zero_add 1)).g]
  simp only [cup1Aux0, Preadditive.comp_add, ShortComplex.Exact.g_desc]
  rw [map_add, @ModuleCat.ofHom_add R _ (H0 (up.obj A))
    (H0 (up.obj A) ⊗ H0 B), Preadditive.add_comp]

lemma cup1Aux0_smul (r : R) (σ : H0 B) : cup1Aux0 A B (r • σ) = r • cup1Aux0 A B σ := by
  haveI : Epi (mapShortComplex₃ (shortExact_upSES A) (Nat.zero_add 1)).g :=
    δ_up_zero_epi A
  rw [← cancel_epi (mapShortComplex₃ (shortExact_upSES A) (Nat.zero_add 1)).g]
  simp only [cup1Aux0, ShortComplex.Exact.g_desc, Linear.comp_smul]
  rw [map_smul, @ModuleCat.ofHom_smul R _ r (H0 (up.obj A)) (H0 (up.obj A) ⊗ _),
    Linear.smul_comp]

def cup1Aux : H0 B →ₗ[R] H1 A →ₗ[R] H1 (A ⊗ B) where
  toFun σ := (cup1Aux0 A B σ).hom
  map_add' := by simp [cup1Aux0_add]
  map_smul' := by simp [cup1Aux0_smul]

lemma cup1Aux_apply (σ : H0 B) : cup1Aux A B σ = (cup1Aux0 A B σ).hom := rfl

lemma cup1Aux_apply_apply (σ : H0 B) (x : H1 A) :
    cup1Aux A B σ x = (cup1Aux0 A B σ).hom x := rfl

abbrev cup1 : H1 A ⊗ H0 B ⟶ H1 (A ⊗ B) :=
  ModuleCat.ofHom <| TensorProduct.lift <| LinearMap.flip (cup1Aux A B)

abbrev map_upSES_ofMap {M N : Rep R G} (f : M ⟶ N) : upSES M ⟶ upSES N where
  τ₁ := f
  τ₂ := Rep.coind₁'.map f
  τ₃ := up.map f
  comm₁₂ := by
    ext
    simp only [upSES_X₂, Rep.coind₁', upSES_X₁, upSES_f, Action.comp_hom, Rep.coind₁'_ι_app_hom,
      Functor.id_obj, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Rep.coe_hom,
      Function.comp_apply]
    ext
    simp
  comm₂₃ := by ext; simp

def cup1NatTrans : .prod (functor R G 1) (functor R G 0) ⋙ tensor (ModuleCat R) ⟶
    tensor (Rep R G) ⋙ functor R G 1  where
  app AB := cup1 AB.1 AB.2
  naturality {M N} φ := by
    dsimp
    ext1
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_tensorHom]
    refine TensorProduct.ext' fun (m1 : H1 M.1) (m2 : H0 M.2) ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    erw [TensorProduct.lift.tmul, TensorProduct.lift.tmul]
    simp only [flip_apply]
    erw [cup1Aux_apply_apply]
    conv_rhs => enter [2]; erw [cup1Aux_apply_apply]
    simp only [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
    congr 2
    haveI : Epi (mapShortComplex₃ (shortExact_upSES M.1) (Nat.zero_add 1)).g :=
      δ_up_zero_epi M.1
    rw [← cancel_epi (mapShortComplex₃ (shortExact_upSES M.1) (Nat.zero_add 1)).g]
    conv_rhs => rw [cup1Aux0, ShortComplex.Exact.g_desc_assoc]
    dsimp
    change δ (shortExact_upSES M.1) 0 1 rfl ≫ _ = _
    have := groupCohomology.δ_naturality (shortExact_upSES M.1) (shortExact_upSES N.1)
      (map_upSES_ofMap φ.1) 0 1 rfl
    rw [← Category.assoc, this, Category.assoc]
    change _ ≫ (mapShortComplex₃ (shortExact_upSES N.1) (Nat.zero_add 1)).g ≫ _ = _
    rw [cup1Aux0, ShortComplex.Exact.g_desc]
    -- apply_fun ((δ (shortExact_upSES N.1) 0 1 rfl).hom ·) using by sorry
    -- simp [cup1Aux0]


    -- erw [TensorProduct.map_tmul]
    sorry


#exit
open TensorProduct in
lemma smallcommSq2 : up.obj A ◁ up.π B ≫ (upTensor A (up.obj B)).hom =
    (upTensor A _).hom ≫ up.map (A ◁ up.π B) := by
  simp only [coequalizer_as_cokernel, Functor.id_obj, upTensor, Iso.trans_hom,
    whiskerRightIso_hom, upIsoCoaugTensor_hom, Iso.symm_hom,
    upIsoCoaugTensor_inv, coaugTensorToUp, ShortComplex.map_X₂, Functor.flip_obj_obj,
    curriedTensor_obj_obj, up_map, Category.assoc]
  rw [← Category.assoc, ← MonoidalCategory.tensorHom_def', MonoidalCategory.tensorHom_def,
    Category.assoc]
  congr 1
  rw [associator_naturality_right_assoc]
  congr 1
  rw [← cancel_epi ((upSES₀ R G).map (tensorRight (A ⊗ Rep.coind₁'.obj B))).g,
    ShortComplex.Exact.g_desc_assoc, Category.assoc, cokernel.π_desc,
    ShortComplex.map_g, Functor.flip_obj_map, curriedTensor_map_app,
    ← Category.assoc, show ((upSES₀ R G).g ▷ (A ⊗ Rep.coind₁'.obj B) ≫
      coaug R G ◁ A ◁ cokernel.π (Rep.coind₁'_ι.app B)) = (_ ◁ _ ◁ up.π _) ≫
      ((upSES₀ R G).map (tensorRight (A ⊗ up.obj B))).g by
      ext : 2
      simp only [Rep.coind₁'_obj, Action.tensorObj_V, Functor.id_obj, upSES₀_X₃, upSES₀_g,
        whiskerRight_tensor, Category.assoc, Action.comp_hom, Action.associator_inv_hom,
        Action.whiskerRight_hom, Action.associator_hom_hom, Action.whiskerLeft_hom,
        ModuleCat.hom_comp, ModuleCat.hom_whiskerLeft, ModuleCat.hom_whiskerRight,
        upSES₀_X₂_V_carrier, upSES₀_X₂_V_isAddCommGroup, upSES₀_X₂_V_isModule, up_obj,
        ShortComplex.map_X₃, Functor.flip_obj_obj, curriedTensor_obj_obj, coequalizer_as_cokernel,
        ShortComplex.map_g, Functor.flip_obj_map, curriedTensor_map_app]
      refine TensorProduct.ext ?_
      ext1 (f : Rep.leftRegular R G)
      refine TensorProduct.ext ?_
      simp only [upSES₀_X₂_V_carrier, upSES₀_X₂_V_isAddCommGroup, upSES₀_X₂_V_isModule]
      ext a fb
      simp only [compr₂ₛₗ_apply, mk_apply]
      erw [compr₂ₛₗ_apply], Category.assoc, ShortComplex.Exact.g_desc]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  simp only [Rep.coind₁'_obj, ShortComplex.map_X₂, Functor.flip_obj_obj, curriedTensor_obj_obj,
    up_obj, Functor.id_obj, Action.tensorObj_V, Rep.tensor_ρ, coequalizer_as_cokernel, Rep.of_ρ]
  ext : 2
  simp only [Action.tensorObj_V, Action.comp_hom, Action.whiskerLeft_hom, tensorToFun_hom,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
  apply TensorProduct.ext
  ext1 (f : Rep.leftRegular R G)
  simp only [upSES₀_X₂_V_carrier, upSES₀_X₂_V_isAddCommGroup, upSES₀_X₂_V_isModule]
  apply TensorProduct.ext
  ext a (fb : G → B.V) : 2
  simp only [compr₂ₛₗ_apply, mk_apply]
  erw [compr₂ₛₗ_apply]

abbrev tensorShortComplexHom : (upSES (A ⊗ Rep.of B.ρ.coind₁')) ⟶ (upSES (A ⊗ up.obj B)) where
  τ₁ := A ◁ up.π B
  τ₂ := Rep.coind₁'.map (A ◁ up.π B)
  τ₃ := up.map (A ◁ up.π B)
  comm₁₂ := by
    ext : 2
    simp only [upSES_X₁, Action.tensorObj_V, up_obj, Functor.id_obj, Rep.coind₁', upSES_X₂,
      Rep.tensor_ρ, coequalizer_as_cokernel, upSES_f, Action.comp_hom, Action.whiskerLeft_hom,
      Rep.coind₁'_ι_app_hom, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_whiskerLeft,
      Rep.of_ρ]
    apply TensorProduct.ext'
    intro a (f : G → B.V)
    simp only [LinearMap.coe_comp, Function.comp_apply]
    erw [lTensor_tmul]
    simp only [LinearMap.compLeft, Rep.coe_hom, Representation.coind₁'_ι, coe_mk, AddHom.coe_mk,
      Function.comp_const, Function.const_inj]
    erw [lTensor_tmul]
  comm₂₃ := by simp

#exit
open TensorProduct in
set_option maxHeartbeats 400000 in -- richard did this
lemma commSq11' (σ : H1 A) : @groupCohomology.map R G G _ _ _ (Rep.of B.ρ.coind₁') (up.obj B)
    (MonoidHom.id G) (cokernel.π (Rep.coind₁'_ι.app B)) 0 ≫ ModuleCat.ofHom
    ((cup1Aux A (up.obj B)).flip σ) = ModuleCat.ofHom ((cup1Aux A (Rep.coind₁'.obj B)).flip σ) ≫
    (functor R G 1).map (A ◁ up.π B) := by
  apply_fun ((H0Iso _).inv ≫ · ) using by aesop_cat
  simp only
  ext1
  simp only [Rep.of_ρ, up_obj, Functor.id_obj, Rep.coind₁'_obj, ModuleCat.of_coe,
    ModuleCat.hom_comp, ModuleCat.hom_ofHom, functor_obj, coequalizer_as_cokernel, functor_map]
  ext ⟨b, hb⟩
  simp only [cup1Aux, cup1Aux0, ShortComplex.SnakeInput.L₁'_X₂,
    HomologicalComplex.HomologySequence.snakeInput_L₀, Functor.mapShortComplex_obj,
    ShortComplex.map_X₃, upSES_X₃, up_obj, Functor.id_obj, Rep.coind₁'_obj, cochainsFunctor_obj,
    HomologicalComplex.homologyFunctor_obj, ModuleCat.of_coe, Action.tensorObj_V, Rep.tensor_ρ,
    functor_obj, Functor.mapIso_hom, functor_map, LinearMap.coe_comp, Function.comp_apply,
    flip_apply, coe_mk, AddHom.coe_mk, Rep.of_ρ]
  simp only [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
  congr 2
  haveI : Epi (mapShortComplex₃ (shortExact_upSES A) (Nat.zero_add 1)).g :=
    δ_up_zero_epi A
  rw [← cancel_epi (mapShortComplex₃ (shortExact_upSES A) (Nat.zero_add 1)).g,
    ShortComplex.Exact.g_desc, ← Category.assoc (mapShortComplex₃ _ _).g,
    ShortComplex.Exact.g_desc]
  simp only [ShortComplex.SnakeInput.L₁'_X₂, HomologicalComplex.HomologySequence.snakeInput_L₀,
    Functor.mapShortComplex_obj, ShortComplex.map_X₃, upSES_X₃, up_obj, Functor.id_obj,
    Rep.coind₁'_obj, cochainsFunctor_obj, HomologicalComplex.homologyFunctor_obj,
    LinearMap.coe_comp, Function.comp_apply, Category.assoc]
  apply_fun ((H0Iso _).inv ≫ ·) using by aesop_cat
  ext1
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom]
  ext ⟨a, ha⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, flip_apply, cup0_apply, Action.tensorObj_V,
    Rep.tensor_ρ, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, Iso.inv_hom_id_apply,
    map_id_comp_H0Iso_hom_apply, Rep.of_ρ]
  conv_lhs => enter [2, 2, 2, 1]; change a ⊗ₜ[R] (@Subtype.val _ _
  (((H0Iso (Rep.of B.ρ.coind₁')).hom ≫ (Rep.invariantsFunctor R G).map
    (cokernel.π (Rep.coind₁'_ι.app B))).hom
    ((ModuleCat.Hom.hom (H0Iso (Rep.of B.ρ.coind₁')).inv) ⟨b, hb⟩)))
  simp only [Functor.id_obj, Rep.coind₁'_obj, Rep.of_ρ, ModuleCat.hom_comp,
    Rep.invariantsFunctor_map_hom, LinearMap.coe_comp, Function.comp_apply, Iso.inv_hom_id_apply]
  conv_lhs =>
    enter [2, 2, 2]
    change (ModuleCat.Hom.hom <| (Rep.invariantsFunctor R G).map
      ((up.obj A) ◁ (up.π B))) ⟨a ⊗ₜ b, fun g ↦ by
        simp only [Representation.mem_invariants, up_obj, Functor.id_obj, Rep.coind₁'_obj,
          Action.tensorObj_V, Rep.tensor_ρ, Rep.of_ρ, Equivalence.symm_inverse,
          Action.functorCategoryEquivalence_functor,
          Action.FunctorCategoryEquivalence.functor_obj_obj] at ha hb ⊢
        erw [Representation.tprod_apply, map_tmul]
        simp [ha, hb]⟩
  simp only [← LinearMap.comp_apply]
  erw [← LinearMap.comp_apply]
  congr 1
  rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, ← ModuleCat.hom_comp, ← ModuleCat.hom_comp,
    ← ModuleCat.hom_comp, ← ModuleCat.hom_comp]
  congr 1
  rw [Category.assoc, Category.assoc, ← Category.assoc]
  erw [smallcommSq1 (up.obj A) (up.π B)]
  rw [Category.assoc, Category.assoc]
  congr 1
  rw [← Category.assoc, ← map_id_comp]
  simp only [← up_obj]
  rw [smallcommSq2, map_id_comp, Category.assoc]
  congr 1
  rw [groupCohomology.δ_naturality (shortExact_upSES (A ⊗ Rep.of B.ρ.coind₁'))
    (shortExact_upSES (A ⊗ cokernel (Rep.coind₁'_ι.app B)))
    (tensorShortComplexHom A B) 0 1 rfl]

lemma commSq12' : @groupCohomology.map R G G _ _ _ (A ⊗ Rep.coind₁'.obj B)
    (A ⊗ up.obj B) (MonoidHom.id G) (A ◁ up.π B) 1 ≫
    ((functor R G 1).mapIso (upTensor' A B)).hom =
    ((functor R G 1).mapIso (coindTensor' A B)).hom ≫
    map (MonoidHom.id G) (up.π _) _ := by
  simp only [Functor.mapIso_hom, functor_map, ← map_id_comp]
  refine groupCohomology.map_congr rfl ?_ _
  congr 1
  simp only [Rep.coind₁'_obj, up_obj, Functor.id_obj, Action.tensorObj_V, Rep.tensor_ρ,
    coequalizer_as_cokernel, Iso.trans_hom, upTensor, Iso.trans_assoc, whiskerRightIso_hom,
    upIsoCoaugTensor_hom, Iso.symm_hom, upIsoCoaugTensor_inv, Functor.mapIso_hom, up_map,
    BraidedCategory.braiding_naturality_right_assoc, coindTensor, coindIsoTensor_hom,
    coindIsoTensor_inv, Category.assoc]

  sorry

def cup11Aux' (σ : H1 A) : H1 B ⟶ H2 (A ⊗ B) :=
  haveI : Epi (mapShortComplex₃ (shortExact_upSES B) (Nat.zero_add 1)).g :=
    δ_up_zero_epi B
  (mapShortComplex₃_exact (shortExact_upSES B) (Nat.zero_add 1)).desc
    (ModuleCat.ofHom ((cup1Aux A (up.obj B)).flip σ) ≫
    ((functor R G 1).mapIso (upTensor' A B)).hom ≫ (δUpIso (A ⊗ B) 0).hom) <| by
  change groupCohomology.map _ _ 0 ≫ _ = 0
  dsimp only [upSES_X₂, upSES_X₃, upSES_g, coequalizer_as_cokernel, Functor.id_obj,
    functor_map]
  rw [← Category.assoc, commSq11', Category.assoc, functor_map]
  nth_rw 2 [← Category.assoc]
  rw [commSq12']
  simp only [Rep.coind₁'_obj, ModuleCat.of_coe, up_obj, Functor.id_obj, Action.tensorObj_V,
    Rep.tensor_ρ, functor_obj, Functor.mapIso_trans, Iso.trans_hom, Functor.mapIso_hom, functor_map,
    coequalizer_as_cokernel, Category.assoc, Nat.reduceAdd, δUpIso_hom]
  have := (mapShortComplex₃ (shortExact_upSES (A ⊗ B)) (rfl : 1 + 1 = 2)).zero
  dsimp at this
  change map _ _ 1 ≫ δ (shortExact_upSES _) 1 2 rfl = 0 at this
  simp [this]

noncomputable def CupProduct [Fintype G] (p q r : ℕ) (h : r = p + q) (A B : Rep R G) :
    -- do I want the aditional r = p + q condition?
    -- how to add the neg condition?
    groupCohomology A p ⊗ groupCohomology B q ⟶ groupCohomology (A ⊗ B) r :=
  match p, q with
  | 0, 0 => cup0' A B ≫ eqToHom (by rw [h])
  | 0, 1 => sorry--(sorry : _ ⟶ groupCohomology (A ⊗ B) 1) ≫ eqToHom _
  | 1, 0 => cup1 A B ≫ eqToHom (by rw [h])
  | 1, 1 => sorry
  | (n + 2), q => (δUpIso A n).inv ▷ (groupCohomology B q) ≫
    CupProduct (n + 1) q (n + q + 1) (by omega) (up.obj A) B ≫
    ((functor R G (n + q + 1)).mapIso (upTensor A B)).hom ≫
    (δUpIso (A ⊗ B) (n + q)).hom ≫ eqToHom (by rw [h, add_assoc, add_comm q, ← add_assoc])
  | p, (n + 2) => sorry
