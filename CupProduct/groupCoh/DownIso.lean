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
