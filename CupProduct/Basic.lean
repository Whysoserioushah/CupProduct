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
    (𝟙 _ ⊗ₘ δ h1 q (q + 1) rfl) ≫ map p (q + 1) (p + q + 1) (by omega) A S2.X₁


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


-- #synth HasRankNullity ℤ
open Rep in
noncomputable def upIsoTensorCoaug [Fintype G] (A : Rep R G) :
    up.obj A ⟶ Rep.leftRegular.coaug R G ⊗ A where
  hom := (forgetCokernelIso _).hom ≫ (ModuleCat.cokernelIsoRangeQuotient _).hom ≫
    (ModuleCat.ofHom (by dsimp; sorry)) ≫
      ((ModuleCat.cokernelIsoRangeQuotient (leftRegular.μ R G).hom).inv ≫
      (forgetCokernelIso (leftRegular.μ R G)).inv) ▷ A.V ≫
      eqToHom (Action.tensorObj_V (leftRegular.coaug R G) A).symm
  comm := sorry

#check Rep.leftRegular.coaug

def upTensorIso (A B : Rep R G) : up.obj A ⊗ B ≅ up.obj (A ⊗ B) := sorry

def upTensorIso' (A B : Rep R G) : A ⊗ up.obj B ≅ up.obj (A ⊗ B) := sorry

noncomputable def CupProduct (p q r : ℕ) (h : r = p + q) (A B : Rep R G) :
    -- do I want the aditional r = p + q condition?
    groupCohomology A p ⊗ groupCohomology B q ⟶ groupCohomology (A ⊗ B) r :=
  match p, q with
  | 0, 0 => cup0' A B ≫ eqToHom (by rw [h])
  | 0, 1 => (sorry : _ ⟶ groupCohomology (A ⊗ B) 1) ≫ eqToHom (by rw [h])
  | 1, 0 => sorry
  | 1, 1 => sorry
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
