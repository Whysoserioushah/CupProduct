import CupProduct.Cohomology.TateCohomology
import CupProduct.Cohomology.Functors.UpDown
import CupProduct.groupCoh.UpIso
import CupProduct.groupCoh.degree0

open CategoryTheory groupCohomology MonoidalCategory Rep.dimensionShift

universe u

variable (R G : Type u) [CommRing R] [Group G] [Fintype G]

noncomputable section

namespace TateCohomology

variable {R G}

abbrev cup0Aux' (A B : Rep R G) (a : A.ρ.invariants) :
    B.ρ.invariants ⧸ (LinearMap.range B.ρ.norm).submoduleOf B.ρ.invariants →ₗ[R]
    (A ⊗ B).ρ.invariants ⧸ (LinearMap.range (A ⊗ B).ρ.norm).submoduleOf (A ⊗ B).ρ.invariants :=
  Submodule.mapQ (R₂ := R) (τ₁₂ := .id R) _ _ (_root_.cup0Aux' A B a) <| fun x hx ↦ by
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.mem_range, Action.tensorObj_V, Rep.tensor_ρ, _root_.cup0Aux',
      Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, LinearMap.coe_mk, AddHom.coe_mk] at hx ⊢
    obtain ⟨b, hb⟩ := hx
    use a ⊗ₜ b
    simp only [ModuleCat.MonoidalCategory.tensorObj_carrier, Representation.norm,
      Representation.tprod_apply, LinearMap.coe_sum, Finset.sum_apply, TensorProduct.map_tmul,
      ← hb, TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun g _ ↦ by rw [a.2 g]

@[simps]
def cup0AuxAux (A B : Rep R G) : A.ρ.invariants →ₗ[R] B.ρ.invariants ⧸
    (LinearMap.range B.ρ.norm).submoduleOf B.ρ.invariants →ₗ[R]
    (A ⊗ B).ρ.invariants ⧸ (LinearMap.range (A ⊗ B).ρ.norm).submoduleOf (A ⊗ B).ρ.invariants where
  toFun a := cup0Aux' A B a
  map_add' a1 a2 := by
    ext b
    simp only [Action.tensorObj_V, Rep.tensor_ρ, cup0Aux', LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.add_apply]
    change Submodule.Quotient.mk (cup0Aux A B (a1 + a2) b) = _
    rw [map_add, LinearMap.add_apply, Submodule.Quotient.mk_add]
    simp [cup0Aux]
  map_smul' r a := by
    ext b
    simp only [Action.tensorObj_V, Rep.tensor_ρ, cup0Aux', LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.mapQ_apply, RingHom.id_apply, LinearMap.smul_apply]
    change Submodule.Quotient.mk (cup0Aux _ _ _ _) = _
    rw [map_smul, LinearMap.smul_apply, Submodule.Quotient.mk_smul]
    simp [cup0Aux]

abbrev cup0Aux (A B : Rep R G) : A.ρ.invariants ⧸
    (LinearMap.range A.ρ.norm).submoduleOf A.ρ.invariants →ₗ[R] B.ρ.invariants ⧸
    (LinearMap.range B.ρ.norm).submoduleOf B.ρ.invariants →ₗ[R]
    (A ⊗ B).ρ.invariants ⧸ (LinearMap.range (A ⊗ B).ρ.norm).submoduleOf (A ⊗ B).ρ.invariants :=
  Submodule.liftQ _ (cup0AuxAux A B) <| fun a ha ↦ by
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.mem_range, Action.tensorObj_V, Rep.tensor_ρ, cup0AuxAux, cup0Aux',
      LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk] at ha ⊢
    ext b
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.zero_comp, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, LinearMap.mem_range]
    obtain ⟨a', ha'⟩ := ha
    use a' ⊗ₜ b.1
    simp only [ModuleCat.MonoidalCategory.tensorObj_carrier, Representation.norm,
      Representation.tprod_apply, LinearMap.coe_sum, Finset.sum_apply, TensorProduct.map_tmul,
      _root_.cup0Aux', Action.tensorObj_V, Rep.tensor_ρ, Equivalence.symm_inverse,
      Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
      ← ha', TensorProduct.sum_tmul, LinearMap.coe_mk, AddHom.coe_mk]
    exact Finset.sum_congr rfl fun g _ ↦ by rw [b.2 g]

def cup0 (A B : Rep R G) : (tateCohomology 0).obj A →ₗ[R] (tateCohomology 0).obj B →ₗ[R]
    (tateCohomology 0).obj (A ⊗ B) where
  toFun a := (TateCohomology.zeroIso (A ⊗ B)).inv.hom ∘ₗ
    cup0Aux A B (TateCohomology.zeroIso A|>.hom.hom a) ∘ₗ (TateCohomology.zeroIso B).hom.hom
  map_add' a1 a2 := by
    simp only [Action.tensorObj_V, ModuleCat.MonoidalCategory.tensorObj_carrier, Rep.tensor_ρ,
      map_add]
    rw [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' r a := by
    simp [ModuleCat.MonoidalCategory.tensorObj_carrier, LinearMap.smul_comp, LinearMap.comp_smul]

abbrev cup0' (A B : Rep R G) : (tateCohomology 0).obj A ⊗ (tateCohomology 0).obj B ⟶
    (tateCohomology 0).obj (A ⊗ B) :=
  ModuleCat.ofHom <| TensorProduct.lift <| cup0 A B

variable (R G) in
@[simps]
def Rep.invariantsQuotFunctor : Rep R G ⥤ ModuleCat R where
  obj A := ModuleCat.of R <| A.ρ.invariants ⧸ (LinearMap.range A.ρ.norm).submoduleOf A.ρ.invariants
  map {A B} f := ModuleCat.ofHom <| Submodule.mapQ _ _
      ((Rep.invariantsFunctor R G).map f).hom <| fun x hx ↦ by
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.mem_range, Rep.invariantsFunctor_map_hom, LinearMap.codRestrict_apply,
      LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply] at hx ⊢
    obtain ⟨a, ha⟩ := hx
    use f.hom.hom a
    simpa [← ha] using LinearMap.ext_iff.1 congr(ModuleCat.Hom.hom
      $(congr(Action.Hom.hom $(A.norm_comm f)))) a

#check δUpIsoTate

-- what is this error about termination??
unsafe def CupProduct (A B : Rep R G) (p q r : ℤ) (h : r = p + q) :
    (tateCohomology p).obj A ⊗ (tateCohomology q).obj B ⟶ (tateCohomology r).obj (A ⊗ B) :=
  match p, q with
  | 0, 0 => cup0' A B ≫ eqToHom (by rw [h, zero_add])
  | Nat.succ n, q => (δUpIsoTate A n).inv ▷ _ ≫ CupProduct (up.obj A) B n q (n + q) rfl ≫
      (tateCohomology (n + q)).map (upTensor A B).hom ≫ (δUpIsoTate (A ⊗ B) (n + q)).hom ≫
      eqToHom (by rw [h, add_assoc, add_comm q 1, ← add_assoc, Nat.cast_succ])
  | p, Nat.succ n => sorry
  | Int.negSucc n, q => sorry
  | _, Int.negSucc n => sorry
  -- decreasing_by
  --   sorry

#exit
abbrev TateCohomology.π (A : Rep R G) (n : ℕ) :
  (tateComplex A).cycles n ⟶ (tateCohomology n).obj A := (tateComplex A).homologyπ n

abbrev lift_subtype (A : Rep R G) : ModuleCat.of R (A.ρ.invariants ⧸
    (LinearMap.range A.ρ.norm).submoduleOf A.ρ.invariants) ⟶ A.V :=
  ModuleCat.ofHom <| Submodule.liftQ _ A.ρ.invariants.subtype <| fun x hx ↦ by
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    LinearMap.mem_range, Submodule.ker_subtype, Submodule.mem_bot] at hx ⊢
  obtain ⟨a, ha⟩ := hx

  sorry

-- lemma map_id_comp_zeroIso_f {A B : Rep R G} (f : A ⟶ B) : (tateCohomology 0).map f ≫
--     (TateCohomology.zeroIso B).hom ≫
--     (ModuleCat.ofHom (Submodule.liftQ _ B.ρ.invariants.subtype _) : _ ⟶ B.V) = _ := by

--   sorry

#check map_id_comp_H0Iso_hom
lemma map_id_comp_zeroIso {A B : Rep R G} (f : A ⟶ B) : (tateCohomology 0).map f ≫
    (TateCohomology.zeroIso B).hom = (TateCohomology.zeroIso A).hom ≫
    (Rep.invariantsQuotFunctor R G).map f := by
  ext a
  sorry

open TensorProduct

def cup0NatTrans : .prod (tateCohomology 0) (tateCohomology 0) ⋙ tensor (ModuleCat R) ⟶
    tensor (Rep R G) ⋙ tateCohomology 0 where
  app MN := cup0' MN.1 MN.2
  naturality := sorry

end TateCohomology

instance : (@tateCohomology R G _ _ _ 0).LaxBraided where
  ε := sorry
  μ := sorry
  μ_natural_left := sorry
  μ_natural_right := sorry
  associativity := sorry
  left_unitality := sorry
  right_unitality := sorry
  braided := sorry
