import CupProduct.Cohomology.AugmentationModule
import CupProduct.Cohomology.Functors.UpDown
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

open CategoryTheory Rep.leftRegular MonoidalCategory groupCohomology

variable (R G : Type u) [CommRing R] [Group G]

instance : HasForget₂ (Rep R G) Ab := .trans (Rep R G) (ModuleCat R) Ab

instance : (forget₂ (Rep R G) Ab).Additive :=
  inferInstanceAs (_ ⋙ _).Additive

instance : (forget₂ (Rep R G) Ab).PreservesHomology :=
  { preservesKernels _ _ _ := Limits.comp_preservesLimit _ _
    preservesCokernels _ _ _:= Limits.comp_preservesColimit _ _ }

noncomputable section

open LinearMap

variable {R G} (A B : Rep R G)

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

@[simp]
lemma cup0_apply (a : H0 A) (b : H0 B) : cup0 A B a b = (H0Iso (A ⊗ B)).inv.hom
  ⟨((H0Iso A).hom.hom a).1 ⊗ₜ ((H0Iso B).hom.hom b).1, mem_tensorInvariants A B
    (H0Iso A|>.hom.hom a) (H0Iso B|>.hom.hom b)⟩ := rfl

noncomputable def cup0' : H0 A ⊗ H0 B ⟶ H0 (A ⊗ B) :=
  ModuleCat.ofHom <| TensorProduct.lift (cup0 A B)

-- def ModuleCat.tensorLeftNatTrans : ({
--   app B := ModuleCat.ofHom <| TensorProduct.mk _ _ _ σ
--   naturality X Y f := by ext; simp [ModuleCat.hom_whiskerLeft]; erw [TensorProduct.mk_apply]
-- } : functor R G 0 ⟶ _)

open TensorProduct

-- change this guy to LaxBraided
instance : Functor.LaxMonoidal (functor R G 0) where
  ε := H0IsoOfIsTrivial (Rep.trivial R G R) |>.inv
  μ := cup0'
  μ_natural_left {X Y} f A := by
    dsimp
    ext1
    dsimp [cup0', ModuleCat.hom_whiskerRight]
    --simp [ModuleCat.MonoidalCategory.tensorObj]
    refine TensorProduct.ext' fun x a ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    erw [lift.tmul]
    erw [cup0_apply]
    dsimp

    sorry
  μ_natural_right := sorry
  associativity X Y Z := by
    sorry
    -- this proof works but need to be pulled out and simplify
    -- ext1
    -- simp only [functor_obj, cup0', functor_map, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    -- apply TensorProduct.ext
    -- refine TensorProduct.ext' fun x y ↦ ?_
    -- ext
    -- simp only [compr₂ₛₗ_apply, LinearMap.coe_comp, Function.comp_apply]
    -- erw [mk_apply, mk_apply, mk_apply]
    -- simp only [ModuleCat.hom_ofHom, id_coe, id_eq]
    -- --erw [ModuleCat.hom_hom_associator]
    -- erw [lift.tmul, lift.tmul, lift.tmul, lift.tmul]
    -- conv_lhs =>
    --   enter [2]; erw [cup0_apply]
    --   enter [2, 1, 2]; erw [cup0_apply]
    -- conv_lhs => enter [2, 2, 1]; rw [Iso.inv_hom_id_apply]
    -- conv_rhs => enter [2]; erw [cup0_apply]
    -- conv_rhs => erw [cup0_apply]
    -- have : (H0Iso ((X ⊗ Y) ⊗ Z)).inv ≫ groupCohomology.map (MonoidHom.id G) (α_ X Y Z).hom 0 =
    --     (Rep.invariantsFunctor R G).map (α_ X Y Z).hom ≫ (H0Iso (X ⊗ Y ⊗ Z)).inv := by
    --   -- rw [← H0Iso.naturality_hom (α_ X Y Z).hom 0]
    --   -- simp only [id_coe, id_eq]
    --   apply_fun ((H0Iso _).hom ≫ · ≫ (H0Iso _).hom) using by aesop_cat
    --   simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.id_comp,
    --     Category.comp_id]
    --   exact groupCohomology.map_id_comp_H0Iso_hom _
    -- rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, this, ModuleCat.hom_comp,
    --   LinearMap.comp_apply]
    -- congr 1
    -- apply Subtype.ext
    -- simp only [Action.tensorObj_V, Rep.tensor_ρ, Rep.invariantsFunctor_map_hom,
    --   Action.associator_hom_hom, Equivalence.symm_inverse,
    --   Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    --   Iso.inv_hom_id_apply]
    -- rfl
  left_unitality := sorry
  right_unitality := sorry
