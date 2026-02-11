import Mathlib
import CupProduct.Cohomology.AugmentationModule
import CupProduct.Cohomology.Functors.UpDown

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
  toFun a := {
    toFun b := H0Iso (A ⊗ B)|>.inv (cup0Aux A B (H0Iso A|>.hom a) (H0Iso B|>.hom b))
    map_add' := by simp
    map_smul' := by simp
  }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

noncomputable def cup0' : H0 A ⊗ H0 B ⟶ H0 (A ⊗ B) :=
  ModuleCat.ofHom <| TensorProduct.lift (cup0 A B)
--   toFun ab := cup0 A B ab.1 ab.2
--   map_add' := by simp
--   map_smul' := sorry
-- }
  -- (AddMonoidHom.uncurry (cup0 A B))

-- how to do the product thing??? Is it just tensor???

@[simp]
lemma cup0_apply (a : H0 A) (b : H0 B) : cup0 A B a b = (H0Iso (A ⊗ B)).inv
  ⟨((H0Iso A).hom a).1 ⊗ₜ ((H0Iso B).hom b).1, mem_tensorInvariants A B
    (H0Iso A|>.hom.hom a) (H0Iso B|>.hom.hom b)⟩ := rfl

noncomputable def groupCohomology.cast {n m} (h : n = m) :
    groupCohomology A n ≅ groupCohomology A m := h ▸ Iso.refl _

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
  simp [const, ← Function.const_comp (α := ι) (f := e), funLeft, ← Equiv.comp_symm_eq,
    Function.comp_assoc, Equiv.self_comp_symm, -Function.const_comp]

noncomputable section

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
    simp only [Finsupp.linearEquivFunOnFinite_apply, LinearMap.compLeft, coe_hom, coe_mk,
      AddHom.coe_mk, Function.comp_apply]
    rw [← inv_inv i, Finsupp.mapDomain_apply inv_injective, Finsupp.mapDomain_apply inv_injective]
    classical
    erw [finsuppScalarLeft_apply_tmul_apply, finsuppScalarLeft_apply_tmul_apply]
    simp
  | add x y h1 h2 =>
    dsimp at h1 h2 ⊢
    simp [map_add, Finsupp.mapDomain_add, h1, h2]

open Limits

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
    restrictScalars_self, TensorProduct.curry_apply, LinearMap.coe_comp, coe_mk, AddHom.coe_mk,
    LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.lid_tmul, one_smul, Rep.coindIsoTensor,
    Rep.coind₁'_obj, Rep.mkIso_hom_hom, Action.tensorObj_V, LinearEquiv.toModuleIso_hom,
    ModuleCat.hom_ofHom, LinearEquiv.trans_apply, Finsupp.mapDomain.coe_linearEquiv,
    Equiv.inv_apply]
  erw [rTensor_tmul]
  ext i
  simp only [Function.const_apply, Rep.leftRegular.μ, map_sum, lsmul_flip_apply,
    ModuleCat.hom_ofHom, coe_sum, Finset.sum_apply, toSpanSingleton_apply, one_smul,
    Finsupp.linearEquivFunOnFinite_apply]
  rw [← inv_inv i, Finsupp.mapDomain_apply inv_injective]
  erw [TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  simp [Rep.leftRegular.of]


def MonoidalCategory.cokernellTensor {C} [Category C] [Preadditive C] [Balanced C] [MonoidalCategory C]
    [MonoidalPreadditive C] {X Y Z : C} (f : X ⟶ Y) [HasCokernel f] [HasCokernel (f ⊗ₘ 𝟙 Z)] :
    cokernel (f ⊗ₘ 𝟙 Z) ≅ cokernel f ⊗ Z :=
  sorry
  -- @asIso _ _ _ _ (cokernel.desc _ (cokernel.π f ⊗ₘ 𝟙 Z) (by
  --   simp [← CategoryTheory.MonoidalCategory.comp_whiskerRight])) <|
  -- @isIso_of_mono_of_epi _ _ _ _ _ _
  --   (ShortComplex.Exact.mono_cokernelDesc _) _
  -- hom := cokernel.desc _ (cokernel.π f ⊗ₘ 𝟙 Z) <| by
  --   simp [← CategoryTheory.MonoidalCategory.comp_whiskerRight]
  -- inv := sorry
  -- hom_inv_id := sorry
  -- inv_hom_id := sorry

def Rep.upIsoTensor [Fintype G] (A : Rep R G) : up.obj A ≅ leftRegular.coaug R G ⊗ A :=
  sorry

def upTensorIso (A B : Rep R G) : up.obj A ⊗ B ≅ up.obj (A ⊗ B) := sorry

def cup1aux (σ : H0 B) : H1 A ⟶ H1 (A ⊗ B) := by
  -- haveI := δ_up_zero_epi A
  haveI : Epi (mapShortComplex₃ (shortExact_upSES A) (Nat.zero_add 1)).g :=
    δ_up_zero_epi A
  refine (mapShortComplex₃_exact (shortExact_upSES A) (Nat.zero_add 1)).desc
    ((ModuleCat.ofHom ((cup0 (up.obj A) B).flip σ)) ≫
    (CategoryTheory.Functor.mapIso (groupCohomology.functor R G _) (upTensorIso A B)).hom ≫
    (δ (shortExact_upSES (A ⊗ B)) 0 1 rfl : _ ⟶ H1 (A ⊗ B))) ?_
  dsimp
  change groupCohomology.map _ _ _ ≫ _ = 0
  sorry
      --(cup0 (up.obj A) B).flip 0)) ?_

-- open Limits in
-- @[simps]
-- def CategoryTheory.isoCokernelOfIso {C : Type u} [Category.{v, u} C] [HasZeroMorphisms C]
--     {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W) (e1 : X ≅ Z) (e2 : Y ≅ W) (h : e1.hom ≫ g = f ≫ e2.hom)
--     [HasCokernel f] [HasCokernel g] : cokernel f ≅ cokernel g where
--   hom := cokernel.desc _ (e2.hom ≫ cokernel.π g) (by rw [← Category.assoc, ← h]; simp)
--   inv := cokernel.desc _ (e2.inv ≫ cokernel.π f) (by
--     apply_fun (e1.inv ≫ · ≫ e2.inv) at h
--     simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] at h
--     rw [← Category.assoc, h]
--     simp)

#check Limits.cokernel.mapIso

open Rep TensorProduct in
noncomputable def mapCoaugTensorLinear [Fintype G] (A : Rep R G) : @HasQuotient.Quotient (G → ↑A.V)
    (Submodule R (G → ↑A.V)) Submodule.hasQuotient Representation.coind₁'_ι.range ≃ₗ[R]
    (@HasQuotient.Quotient (G →₀ R) (Submodule R (G →₀ R)) Submodule.hasQuotient
    (leftRegular.μ R G).hom.hom.range) ⊗[R] A := by
  classical
  -- refine Submodule.quotEquivOfEq _ _ (Representation.coind₁'_ι_range A) ≪≫ₗ ?_
  -- obtain h := finite_iff_exists_equiv_fin.1 (Fintype.finite inferInstance : Finite G)
  -- choose n hn using h
  -- have e := hn.some
  -- haveI : Nonempty (Fin n) := e.symm.nonempty
  -- have := @Submodule.Quotient.equiv R (G → A.V) _ _ _ (Fin n → A.V) _ _
  --   Submodule.const Submodule.const (LinearEquiv.funCongrLeft _ _ e.symm)
  --   (Submodule.equiv_const e)
  refine Submodule.Quotient.equiv _ _ ((piScalarRight R R _ _).symm ≪≫ₗ
    TensorProduct.comm _ _ _) ?_ ≪≫ₗ rTensor.equiv A.V (exact_subtype_mkQ _) (Submodule.span R
    {∑ g : G, Pi.single g (1 : R)}).mkQ_surjective ≪≫ₗ
    congr ((Submodule.quotEquivOfEq _ _ (leftRegular.range_μ R G))
    ≪≫ₗ Submodule.Quotient.equiv (N := G → R) _ (Submodule.span R {∑ g, Pi.single g 1})
    (Finsupp.linearEquivFunOnFinite R _ _) (by
      ext;
      simp only [Finsupp.linearEquivFunOnFinite, Equiv.invFun_as_coe, Submodule.mem_map,
        Submodule.mem_span_singleton, coe_mk, AddHom.coe_mk, exists_exists_eq_and, Finsupp.coe_smul,
        Finsupp.coe_finset_sum]
      congr!)).symm (.refl _ _)
  ext x
  induction x with
  | zero => simp
  | tmul f a =>
    simp only [Representation.coind₁'_ι, Submodule.mem_map_equiv, LinearEquiv.trans_symm,
      comm_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply, comm_tmul, piScalarRight_apply,
      piScalarRightHom_tmul, mem_range, coe_mk, AddHom.coe_mk]
    constructor
    · rintro ⟨a', ha'⟩
      rw [Finset.univ_sum_single, show (fun g ↦ (1 : R)) = (1 : G → R) by rfl]
      replace ha' := funext_iff.1 ha'
      have (i j : G) : f i = f j := by
        have h1 := ha' i|>.symm.trans (ha' j)
        -- false goal ... :-(
        sorry
      sorry
    · sorry
  | add x y _ _ => sorry

def MonoidalCategory.tensorRightIso {C} [Category C] [MonoidalCategory C]
    {X Y : C} (Z : C) (e : X ≅ Y) : X ⊗ Z ≅ Y ⊗ Z where
  hom := e.hom ▷ Z
  inv := e.inv ▷ Z
  hom_inv_id := by simp
  inv_hom_id := by simp


-- #synth MonoidalCategory (ModuleCat R)

open Rep in
noncomputable def upIsoTensorCoaug [Fintype G] (A : Rep R G) :
    up.obj A ≅ Rep.leftRegular.coaug R G ⊗ A :=
  mkIso _ _ ((forgetCokernelIso _) ≪≫ (ModuleCat.cokernelIsoRangeQuotient _) ≪≫
    (mapCoaugTensorLinear A).toModuleIso ≪≫ eqToIso ModuleCat.of_tensor ≪≫
    MonoidalCategory.tensorRightIso _ (ModuleCat.cokernelIsoRangeQuotient _).symm ≪≫
    MonoidalCategory.tensorRightIso _ (forgetCokernelIso (leftRegular.μ R G)).symm
    ≪≫ eqToIso (Action.tensorObj_V (leftRegular.coaug R G) A).symm) <| fun g x ↦ by
  simp [mapCoaugTensorLinear, MonoidalCategory.tensorRightIso, Rep.forgetCokernelIso]
  -- a mess
  sorry



def upTensorIso' (A B : Rep R G) : A ⊗ up.obj B ≅ up.obj (A ⊗ B) := sorry

noncomputable def CupProduct (p q r : ℕ) (h : r = p + q) (A B : Rep R G) :
    -- do I want the aditional r = p + q condition?
    groupCohomology A p ⊗ groupCohomology B q ⟶ groupCohomology (A ⊗ B) r :=
  match p, q with
  | 0, 0 => cup0' A B ≫ eqToHom (by rw [h])
  | _, 1 => sorry--(sorry : _ ⟶ groupCohomology (A ⊗ B) 1) ≫ eqToHom _
  | 1, _ => sorry
  | (n + 2), _ => sorry
  | _, (n + 2) => sorry

  -- | 0 =>
  --   match q with
  --   | 0 => cup0' A B
  --   | 1 =>
  --     -- what to do with dim 1?
  --     sorry
  --   | (n + 2) =>
  --     (𝟙 _ ⊗ₘ (δUpIso B n).inv) ≫
  --       CupProduct 0 (n + 1) A (up.obj B) ≫ _
  --       -- ((groupCohomology.functor R G (n + 1)).mapIso (upTensorIso' A B) :
  --       --   groupCohomology (A ⊗ up.obj B) (n + 1) ≅ groupCohomology (up.obj (A ⊗ B)) (n + 1)).hom ≫ _
  -- | 1 => sorry
  -- | n + 2 => sorry

-- variable (n : Type*) [Fintype n] [DecidableEq n]
-- #synth IsTopologicalGroup (Matrix.GeneralLinearGroup n ℚ)
-- #check Submodule.eq_bot_iff
