import CupProduct.Cohomology.Functors.Restriction
import CupProduct.Cohomology.IndCoind.TrivialCohomology
import CupProduct.Cohomology.LeftRegular
import CupProduct.Cohomology.TrivialCohomology
import CupProduct.Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Data.Finsupp.Pointwise

/-!
Let `R` be a commutative ring and `G` a group.
We define the augmentation module `aug R G : Rep R G` to be the kernel of
the augmentation map "ε : R[G] ⟶ R".

We construct the short exact sequence of `H`-modules for every subgroup `H` of `G`.

  `0 ⟶ aug R G ⟶ R[G] ⟶ R ⟶ 0`.

In the case that `G` is finite, the representation `R[G]` is coinduced, and so has
trivial cohomology (with respect to any subgroup `H`).
This implies that the connecting homomorphisms give isomorphisms for all `n > 0`

  `Hⁿ(H,R) ≅ Hⁿ⁺¹(H, aug R G)`.

We also have isomorphisms

  `H¹(H,aug R G) ≅ R ⧸ |H|R`,

  `H²(H, aug R G) ≅ 0`, assuming `IsAddTorsionFree R`.

-/

open
  Rep
  leftRegular
  CategoryTheory
  ConcreteCategory
  Limits
  groupCohomology
  BigOperators

universe u

variable (R G : Type u) [CommRing R] [Group G]

noncomputable section AugmentationModule

/--
The augmentation module `aug R G` is the kernel of the augmentation map
  `ε : leftRegular R G ⟶ trivial R G R`.
-/
abbrev Rep.aug : Rep R G := kernel (ε R G)

namespace Rep.aug

/--
The inclusion of `aug R G` in `leftRegular R G`.
-/
abbrev ι : aug R G ⟶ leftRegular R G := kernel.ι (ε R G)

lemma ε_comp_ι : ι R G ≫ ε R G = 0 := kernel.condition (ε R G)

lemma ε_apply_ι (v : aug R G) : (ε R G).hom (ι R G|>.hom v) = 0 := congr($(ε_comp_ι R G) v)

lemma sum_coeff_ι [Fintype G] (v : aug R G) : ∑ g : G, (ι R G).hom v g = 0 := by
  rw [← ε_apply_ι R G v, ε_eq_sum]

/--
There is an element of `aug R G` whose image in the left regular representation is `of g - of 1`.
-/
lemma exists_ofSubOfOne (g : G) : ∃ v : aug R G, (ι R G).hom v =
    Finsupp.single g 1 - Finsupp.single 1 1 := by
  apply exists_kernelι_eq
  rw [map_sub, ε_of, ε_of, sub_self]

/--
The element of `aug R G` whose image in `leftRegular R G` is `of g - of 1`.
-/
def ofSubOfOne (g : G) : aug R G := (exists_ofSubOfOne R G g).choose

@[simp] lemma ofSubOfOne_spec (g : G) :
    ι R G (ofSubOfOne R G g) = .single g 1 - .single 1 1 :=
  (exists_ofSubOfOne R G g).choose_spec

/-- The short exact sequence `0 ⟶ aug R G ⟶ R[G] ⟶ R ⟶ 0`. -/
abbrev aug_shortExactSequence : ShortComplex (Rep R G) where
  X₁ := aug R G
  X₂ := leftRegular R G
  X₃ := trivial R G R
  f := ι R G
  g := ε R G
  zero := ε_comp_ι R G

/--
The sequence in `Rep R G`:

  `0 ⟶ aug R G ⟶ R[G] ⟶ R ⟶ 0`

is a short exact sequence.
-/
lemma aug_isShortExact : (aug_shortExactSequence R G).ShortExact where
  exact := ShortComplex.exact_kernel _
  mono_f := equalizer.ι_mono
  epi_g := ε_epi

/--
The sequence

  `0 ⟶ aug R G ⟶ R[G] ⟶ R ⟶ 0`

is a short exact sequence of `H`-modules for any `H →* G`.
-/
lemma aug_isShortExact' {H : Type u} [Group H] (φ : H →* G) :
    ((aug_shortExactSequence R G).map (resFunctor φ)).ShortExact :=
  CategoryTheory.ShortComplex.ShortExact.map_of_exact (aug_isShortExact R G) _

open Finsupp

def leftRegularToInd₁' : (G →₀ R) →ₗ[R] G →₀ R := lmapDomain R R (fun x ↦ x⁻¹)

@[simp]
lemma leftReugularToInd₁'_single (g : G) :
    leftRegularToInd₁' R G (single g 1) = single g⁻¹ 1 := by
  ext; simp [leftRegularToInd₁']

lemma leftRegularToInd₁'_comp_lsingle (x : G) :
    leftRegularToInd₁' R G ∘ₗ lsingle x = lsingle x⁻¹ := by ext; simp

lemma leftRegularToInd₁'_comm (g : G) : leftRegularToInd₁' R G ∘ₗ (leftRegular R G).ρ g
    = (Representation.trivial R G R).ind₁' g ∘ₗ leftRegularToInd₁' R G := by
  ext; simp

lemma leftRegularToInd₁'_comm' (g : G) :
    leftRegularToInd₁' R G ∘ₗ (Representation.trivial R G R).ind₁' g =
    (leftRegular R G).ρ g ∘ₗ leftRegularToInd₁' R G := by
  ext; simp

lemma leftRegularToInd₁'_comp_leftRegularToInd₁' :
    leftRegularToInd₁' R G ∘ₗ leftRegularToInd₁' R G = 1 := by
  ext : 1
  rw [LinearMap.comp_assoc, leftRegularToInd₁'_comp_lsingle, leftRegularToInd₁'_comp_lsingle,
    inv_inv]
  rfl

/--
The left regular representation is isomorphic to `ind₁'.obj (trivial R G R)`
-/
def _root_.Rep.leftRegular.iso_ind₁' : leftRegular R G ≅ ind₁'.obj (trivial R G R) where
  hom := ofHom ⟨leftRegularToInd₁' R G, fun g ↦ leftRegularToInd₁'_comm R G g⟩
  inv := ofHom ⟨leftRegularToInd₁' R G, fun g ↦ leftRegularToInd₁'_comm' R G g⟩
  hom_inv_id := by
    ext : 2
    apply leftRegularToInd₁'_comp_leftRegularToInd₁'
  inv_hom_id := by
    ext : 2
    apply leftRegularToInd₁'_comp_leftRegularToInd₁'

/--
For a finite group, the left regular representation is acyclic for cohomology.
-/
instance _root_.Rep.leftRegular.trivialCohomology [Finite G] :
    (leftRegular R G).TrivialCohomology := .of_iso (iso_ind₁' R G)

/--
The left regular representation is acyclic for homology.
-/
instance _root_.Rep.leftRegular.trivialHomology :
    (leftRegular R G).TrivialHomology := .of_iso (iso_ind₁' R G)

set_option linter.unusedFintypeInType false in
/--
For a finite group, the left regular representation is acyclic for Tate cohomology.
-/
instance _root_.Rep.leftRegular.trivialTateCohomology [Fintype G] :
    (leftRegular R G).TrivialTateCohomology := .of_iso (iso_ind₁' R G)

/--
The connecting homomorphism from `Hⁿ⁺¹(G,R)` to `Hⁿ⁺²(G,aug R G)` is an isomorphism.
-/
lemma cohomology_aug_succ_iso [Finite G] (n : ℕ) :
    IsIso (δ (aug_isShortExact R G) (n + 1) (n + 2) rfl) :=
  /-
  This connecting homomorphism is sandwiched between two modules `H^{n + 1}(G, R[G])` and
  `H^{n + 2}(G, R[G])`, where `P` is the left regular representation.
  Then use `Rep.leftRegular.trivialCohomology` to show that both of these are zero.
  -/
  groupCohomology.isIso_δ_of_isZero _ _ Rep.isZero_of_trivialCohomology
    Rep.isZero_of_trivialCohomology

lemma tateCohomology_auc_succ_iso [Fintype G] (n : ℤ) :
    IsIso (TateCohomology.δ (aug_isShortExact R G) n) := by
  have : TrivialTateCohomology (leftRegular R G) := inferInstance
  exact TateCohomology.isIso_δ _ this _

lemma H2_aug_isZero [Finite G] [IsAddTorsionFree R] : IsZero (H2 (aug R G)) :=
  /-
  This follows from `cohomology_aug_succ_iso` and `groupCohomology.H1_isZero_of_trivial`.
  -/
  .of_iso (H1_isZero_of_trivial _) <| (@asIso _ _ _ _ (δ (aug_isShortExact R G) 1 2 rfl)
    (cohomology_aug_succ_iso R G 0)).symm

/--
If `H` is a subgroup of a finite group `G` then the connecting homomorphism
from `Hⁿ⁺¹(H,R)` to `Hⁿ⁺²(H,aug R G)` is an isomorphism.
-/
lemma cohomology_aug_succ_iso' [Finite G] {H : Type u} [Group H] {φ : H →* G}
    (inj : Function.Injective φ) (n : ℕ) :
    IsIso (δ (aug_isShortExact' R G φ) (n + 1) (n + 2) rfl) :=
  /-
  The proof is similar to that of `cohomology_aug_succ_iso` but uses
  `Rep.leftRegular.isZero_groupCohomology'` in place of `Rep.leftRegular.isZero_groupCohomology`.
  -/
  groupCohomology.isIso_δ_of_isZero _ _ (isZero_of_injective _ _ _ (by omega) inj) <|
    isZero_of_injective _ _ _ (by omega) inj

  /-
  If Tate cohomology is defined, then this is proved in the same way as a previous
  lemma. If not, then using usual cohomology we have a long exact sequence containing the
  following section:

    `H⁰(G,R[G]) ⟶ H⁰(G,R) ⟶ H¹(aug R G) ⟶ 0`.

  We clearly have `H⁰(G,R) ≅ R`.
  The group `H⁰(G,R[G])` is also cyclic over `R`, and is generated by the norm element,
  i.e. the sum of all elements of `G`. The image of the norm element in `H⁰(G,R)` is `|G|`,
  since every element of the group is mapped by `ε` to `1`.
  -/
set_option backward.isDefEq.respectTransparency false in
def H1_iso [Fintype G] :
    H1 (aug R G) ≅ ModuleCat.of R (R ⧸ Ideal.span {(Nat.card G : R)}) :=
  LinearEquiv.toModuleIso <| LinearEquiv.symm <| by
  refine ?_ ≪≫ₗ LinearMap.quotKerEquivOfSurjective (δ (aug_isShortExact R G) 0 1 rfl).hom
    (ModuleCat.epi_iff_surjective _|>.1 <| epi_δ_of_isZero _ 0 <| by
    simpa using by exact isZero_of_trivialCohomology)
  refine Submodule.Quotient.equiv _ _ (H0trivial R G).symm.toLinearEquiv ?_
  have : LinearMap.range _ = LinearMap.ker (δ (aug_isShortExact R G) 0 1 rfl).hom :=
    (groupCohomology.mapShortComplex₃_exact (aug_isShortExact R G) rfl).moduleCat_range_eq_ker
  rw [← this]
  apply le_antisymm
  · simp only [Nat.card_eq_fintype_card, Nat.reduceAdd]
    intro (x : H0 _)
    simp only [Submodule.mem_map, Ideal.mem_span_singleton', exists_exists_eq_and,
      LinearMap.mem_range, forall_exists_index]
    rintro a rfl
    refine ⟨a • leftRegular.norm R G, ?_⟩
    apply (H0trivial R G).toLinearEquiv.injective
    rw [← Iso.toLinearEquiv_symm, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
    change (H0trivial R G).hom.hom _ = _
    rw [show (mapShortComplex₃ ..).f = map (.id G) (ε R G) 0 by simp, ← LinearMap.comp_apply,
      ← ModuleCat.hom_comp, map_comp_H0trivial]
    simp only [ShortComplex.SnakeInput.L₁'_X₁, HomologicalComplex.HomologySequence.snakeInput_L₀,
      Functor.mapShortComplex_obj, ShortComplex.map_X₂, cochainsFunctor_obj,
      HomologicalComplex.homologyFunctor_obj, ModuleCat.hom_comp, map_smul, LinearMap.coe_comp,
      Function.comp_apply, smul_eq_mul]
    conv_lhs => enter [2, 2]; tactic => convert leftRegular.zeroι_norm R G
    rw [map_sum]
    simp
  · change _ ≤ Submodule.map (H0trivial R G).symm.toLinearEquiv.toLinearMap _
    rw [Submodule.map_equiv_eq_comap_symm]
    rw [LinearMap.range_eq_map, ← leftRegular.span_norm, Submodule.map_le_iff_le_comap,
      Submodule.span_le, Set.singleton_subset_iff]
    simp only [Nat.reduceAdd, ShortComplex.SnakeInput.L₁'_X₁,
      HomologicalComplex.HomologySequence.snakeInput_L₀, Functor.mapShortComplex_obj,
      ShortComplex.map_X₂, cochainsFunctor_obj, HomologicalComplex.homologyFunctor_obj,
      ShortComplex.SnakeInput.L₁'_X₂, ShortComplex.map_X₃, ShortComplex.SnakeInput.L₁'_f,
      ShortComplex.map_g, cochainsFunctor_map, HomologicalComplex.homologyFunctor_map,
      Nat.card_eq_fintype_card, Submodule.comap_coe, LinearEquiv.coe_coe, Set.mem_preimage,
      SetLike.mem_coe]
    rw [Iso.toLinearEquiv_symm, Iso.symm_symm_eq, Iso.toLinearEquiv_apply, map_comp_H0trivial_apply,
      leftRegular.zeroι_norm, map_sum]
    simpa [Ideal.mem_span_singleton'] using ⟨1, one_mul _⟩

  /-
  If Tate cohomology is defined, then this is proved in the same way as a previous
  lemma. If not, then using usual cohomology we have a long exact sequence containing the
  following section:

    `H⁰(H,R[G]) ⟶ H⁰(H,R) ⟶ H¹(aug R G) ⟶ 0`.

  We clearly have `H⁰(H,R) = R`.
  The group `H⁰(H,R[G])` is generated by the indicator functions of cosets of `H`,
  The image of such a function in `H⁰(H,R)` is `|H|`, since every element of the
  group is mapped by `ε` to `1`.
  -/
set_option backward.isDefEq.respectTransparency false in
def H1_iso' [Finite G] {H : Type u} [Group H] [Fintype H] {φ : H →* G}
    (inj : Function.Injective φ) :
    H1 (aug R G ↓ φ) ≅ ModuleCat.of R (R ⧸ Ideal.span {(Nat.card H : R)}) := by
  have := Rep.trivialCohomology_iff_res.1 (trivialCohomology R G) φ inj
  refine LinearEquiv.toModuleIso <|.symm ?_
  refine ?_ ≪≫ₗ LinearMap.quotKerEquivOfSurjective (δ (aug_isShortExact' R G φ) 0 1 rfl).hom
    (ModuleCat.epi_iff_surjective _|>.1 <| epi_δ_of_isZero _ 0 <|
      isZero_of_trivialCohomology (M := leftRegular R G ↓ φ))
  refine Submodule.Quotient.equiv _ _ (H0trivial R H).symm.toLinearEquiv ?_
  rw [show LinearMap.ker (δ (aug_isShortExact' R G φ) 0 1 rfl).hom = _ from
    (mapShortComplex₃_exact (aug_isShortExact' R G φ) rfl).moduleCat_range_eq_ker.symm]
  simp only [ShortComplex.map_X₃]
  rw [LinearMap.range_eq_map, ← leftRegular.res_span_norm R G φ inj, Submodule.map_span,
    ← Set.range_comp, Ideal.span, Submodule.map_span]
  congr 1
  ext x
  simp only [Iso.toLinearMap_toLinearEquiv, Iso.symm_hom, Set.image_singleton,
    Nat.card_eq_fintype_card, Set.mem_singleton_iff, Nat.reduceAdd, ShortComplex.SnakeInput.L₁'_X₂,
    HomologicalComplex.HomologySequence.snakeInput_L₀, Functor.mapShortComplex_obj,
    ShortComplex.map_X₃, cochainsFunctor_obj, HomologicalComplex.homologyFunctor_obj,
    ShortComplex.SnakeInput.L₁'_X₁, ShortComplex.map_X₂, ShortComplex.SnakeInput.L₁'_f,
    ShortComplex.map_g, hom_ofHom, Representation.isTrivial_def, LinearMap.id_coe, id_eq,
    Representation.IntertwiningMap.coe_eq_toLinearMap, cochainsFunctor_map,
    HomologicalComplex.homologyFunctor_map, Set.mem_range, Function.comp_apply]
  have : (resFunctor φ).map (ε R G) = ofHom ⟨lift R R G (fun _ ↦ 1), fun _ ↦ by ext; simp⟩ := rfl
  change _  ↔ ∃ g, groupCohomology.map (MonoidHom.id H) (ofHom _) 0 _ = _
  rw [← this]
  simp only [leftRegular.groupCoh_map_res_norm R G φ, eq_comm, exists_const]
  rfl

end Rep.aug

namespace Rep.leftRegular

variable (R G : Type u) [CommRing R] [Group G] [Fintype G]

/-- `Rep.norm` applied to `1 : R[G]` is indeed `∑ g, g`. -/
lemma norm_of_one : (Rep.norm (Rep.leftRegular R G)).hom (.single 1 1) =
    ∑ g, .single g 1 := by
  ext g'
  simp [Rep.norm, Representation.norm]

/-- the map from `R ⟶ R[G]` that sends `r : R` to `r • N` where `N` is the "norm" element. -/
def μ : trivial R G R ⟶ leftRegular R G := ofHom {
  __ := (LinearMap.lsmul R (leftRegular R G)).flip (∑ g, .single g 1)
  isIntertwining' g := by
    ext g'
    classical simp only [map_sum, LinearMap.lsmul_flip_apply, Representation.isTrivial_def,
      LinearMap.comp_id, LinearMap.coe_sum, Finset.sum_apply, LinearMap.toSpanSingleton_apply,
      one_smul, Finsupp.coe_finset_sum, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, LinearMap.coe_comp, Function.comp_apply, Representation.ofMulAction_single,
      smul_eq_mul, Finset.sum_boole, @eq_comm _ (1 : R)]
    rw [← Nat.cast_one]
    refine _root_.congr_arg _ (Finset.card_eq_one.2 ⟨g⁻¹ * g', ?_⟩)
    ext
    simp [eq_comm, ← inv_mul_eq_iff_eq_mul (a := g)]}

@[simp]
lemma μ_one : (μ R G).hom (1 : R) = ∑ g, .single g 1 := by
  simp [μ]

@[simp]
lemma μ_zero : (μ R G).hom (0 : R) = 0 := by simp [μ]

@[simp]
lemma μ_apply (r : R) : (μ R G).hom r = r • ∑ g, .single g 1 := by rfl

abbrev coaug : Rep R G := CategoryTheory.Limits.cokernel (μ R G)

@[simp]
lemma ModuleCat.ofHom_zero {R : Type u} {M N : Type v} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
  ModuleCat.ofHom (0 : M →ₗ[R] N) = 0 := rfl

/-- The forgetful functor from `Rep R G` to `ModuleCat R` preserves cokernels,
giving an isomorphism between the underlying module of the cokernel and
the cokernel of the underlying module map. -/
noncomputable def _root_.Rep.forgetCokernelIso {R G : Type u} [CommRing R] [Group G]
    {A B : Rep.{u} R G} (f : A ⟶ B) :
    ModuleCat.of R (Limits.cokernel f).V ≅ Limits.cokernel f.toModuleCatHom :=
  (preservesColimitIso (forget₂ (Rep R G) (ModuleCat R)) (Limits.parallelPair f 0)).trans
    (Limits.HasColimit.isoOfNatIso (Limits.parallelPair.ext (Iso.refl _) (Iso.refl _)
      (by simp) (by simp)))

lemma range_μ : (μ R G).hom.range.1 = Submodule.span R {∑ g, .single g 1} := by
  ext x
  simp +contextual only [Representation.IntertwiningMap.range_toSubmodule, LinearMap.mem_range,
    Representation.IntertwiningMap.coe_toLinearMap, Submodule.mem_span_singleton]
  constructor
  all_goals exact fun ⟨y, hy⟩ ↦ ⟨y, by rwa [μ_apply] at *⟩

private abbrev foo1 [Finite G] : (G →₀ R) →ₗ[R] (Set.univ.diff {(1 : G)}) →₀ R :=
    haveI : DecidablePred fun x ↦ x ∈ Set.univ.diff {(1 : G)} := Classical.decPred _
    -- (Finsupp.supportedEquivFinsupp _).toLinearMap ∘ₗ
    -- Finsupp.restrictDom R R (Set.univ.diff {(1 : G)})
    (Finsupp.linearEquivFunOnFinite R R (Set.univ.diff {(1 : G)})).symm.toLinearMap
    ∘ₗ {
      toFun f x := f x.1 - f 1
      map_add' f1 f2 := by ext; simp; abel
      map_smul' f r := by ext; simp [mul_sub]
    } ∘ₗ (Finsupp.linearEquivFunOnFinite R R G).toLinearMap

private def foo : @HasQuotient.Quotient (G →₀ R) (Submodule R (G →₀ R)) Submodule.hasQuotient
    (R ∙ ∑ g, Finsupp.single g 1) ≃ₗ[R] (Set.univ.diff {(1 : G)}) →₀ R :=
  Submodule.quotEquivOfEq _ _ (by
    simp only [LinearEquiv.ker_comp, SetLike.ext_iff, Submodule.mem_span_singleton,
      LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_coe,
      Function.comp_apply, Finsupp.linearEquivFunOnFinite_apply]
    refine fun x ↦ ⟨fun ⟨r, hr⟩ ↦ by simp [← hr, Pi.zero_def], fun h ↦ ⟨x 1, ?_⟩⟩
    ext g
    simp only [Finsupp.coe_smul, Finsupp.coe_finset_sum, Pi.smul_apply, Finset.sum_apply,
      Finsupp.univ_sum_single_apply', smul_eq_mul, mul_one, eq_comm]
    if hg : g = 1 then simp [hg] else
    replace h := funext_iff.1 h ⟨g, by simp [Set.diff, hg]⟩
    simpa [sub_eq_zero] using h) ≪≫ₗ LinearMap.quotKerEquivOfSurjective (foo1 R G) (by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_mk, AddHom.coe_mk,
      EquivLike.comp_surjective, EquivLike.surjective_comp]
    intro f
    classical
    use (fun g ↦ if hg : g = 1 then 0 else f ⟨g, Set.mem_diff_singleton.2 ⟨⟨⟩, hg⟩⟩)
    ext ⟨g, hg⟩
    simp [Set.mem_diff_singleton.1 hg])

instance : Module.Free R (coaug R G) := .of_basis (ι := Set.diff (⊤ : Set G) {1})
  { repr := (Rep.forgetCokernelIso (μ R G) ≪≫ ModuleCat.cokernelIsoRangeQuotient
      (μ R G).toModuleCatHom).toLinearEquiv ≪≫ₗ Submodule.quotEquivOfEq _ _ (range_μ R G) ≪≫ₗ
    foo R G}

-- for any Cat that has a forgetful functor to ModuleCat R, there is an iso
-- between (forget₂ _ _).obj (Limits.kernel f) and Limits.kernel ((forget₂ _ _).map f)
noncomputable def _root_.Rep.forgetKernelIso {R G : Type u} [CommRing R] [Group G]
    {A B : Rep.{u} R G}
    (f : A ⟶ B) : ModuleCat.of R (Limits.kernel f).V ≅ Limits.kernel f.toModuleCatHom :=
  (preservesLimitIso (forget₂ (Rep R G) (ModuleCat R)) (Limits.parallelPair f 0)).trans
    (Limits.HasLimit.isoOfNatIso (Limits.parallelPair.ext (Iso.refl _) (Iso.refl _)
      (by simp) (by simp)))

set_option backward.isDefEq.respectTransparency false in
lemma kernel_ι_comp_forgetKernelIso {R G : Type u} [CommRing R] [Group G]
    {A B : Rep R G} (f : A ⟶ B) : (forgetKernelIso f).hom ≫ Limits.kernel.ι f.toModuleCatHom =
    (Limits.kernel.ι f).toModuleCatHom := by
  simp [forgetKernelIso]

@[reassoc]
lemma forgetKernelIso_inv_comp_kernel_ι {R G : Type u} [CommRing R] [Group G] {A B : Rep R G}
    (f : A ⟶ B) : (forgetKernelIso f).inv ≫ (Limits.kernel.ι f).toModuleCatHom =
      Limits.kernel.ι f.toModuleCatHom := by
  rw [← kernel_ι_comp_forgetKernelIso, Iso.inv_hom_id_assoc]

noncomputable instance (ι R : Type*) [Ring R] [Fintype ι] : Ring (ι →₀ R) where
  __ := Finsupp.instNonUnitalRing
  one := Finsupp.equivFunOnFinite.symm 1
  one_mul f := show Finsupp.equivFunOnFinite.symm 1 * f = f by ext; simp
  mul_one f := show f * Finsupp.equivFunOnFinite.symm 1 = f by ext; simp

omit [Fintype G] in
variable {G} in
lemma singleBasis_mem_ker (g : G) : Finsupp.single g (1 : R) - Finsupp.single (1 : G) (1 : R) ∈
      (ε R G).hom.toLinearMap.ker := by
  rw [LinearMap.mem_ker, (ε R G).hom.toLinearMap_apply, map_sub, ε_of, ε_of, sub_self]

omit [Fintype G] in
abbrev kerε.v : (Set.univ.diff {(1 : G)}) → (ε R G).hom.toLinearMap.ker := fun g ↦
    ⟨Finsupp.single g.1 1 - Finsupp.single 1 1, singleBasis_mem_ker R g.1⟩

omit [Fintype G] in
variable {R G} in
lemma linearIndep_kerε_basis : LinearIndependent R (kerε.v R G) := fun _ _ h ↦ by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Subtype.ext_iff,
    Finsupp.sum, Submodule.coe_sum, Finsupp.sum, Submodule.coe_sum] at h
  simp_rw [Submodule.coe_smul, smul_sub, Finset.sum_sub_distrib] at h
  classical simp only [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.ext_iff,
    Finsupp.coe_sub, Finsupp.coe_finset_sum, Pi.sub_apply, Finset.sum_apply,
    Finsupp.single_apply, Finset.sum_ite_irrel, Finset.sum_const_zero] at h
  if hG : Subsingleton G then
  ext x
  simp only [Set.diff, Subsingleton.elim _ (1 : G), Set.mem_univ, Set.mem_singleton_iff,
    not_true_eq_false, and_false, Set.setOf_false] at x
  exact False.elim (Set.mem_empty_iff_false x.1|>.1 x.2)
  else
  ext ⟨g, hg⟩
  have hg' := by simpa [Set.diff] using hg
  specialize h g
  simp only [eq_comm (a := (1 : G)), hg', ↓reduceIte, sub_zero] at h
  rw [Finset.sum_eq_single ⟨g, hg⟩ (by simp +contextual) (by simp),
    Finset.sum_eq_single ⟨g, hg⟩ (by simp +contextual) (by simp)] at h
  simpa using h

omit [Fintype G] in
variable {R G} in
lemma kerε_basis_span : ⊤ ≤ Submodule.span R (Set.range <| kerε.v R G) := fun ⟨x, hx⟩ _ ↦ by
  have hGG := Classical.decEq G
  have hxx : x = ∑ i ∈ x.support, x i • Finsupp.single i 1 := by
      conv_lhs => rw [← x.sum_single, Finsupp.sum]
      simp
  have hx' : ∑ x_1 ∈ x.support, x x_1 = 0 := by
    rw [LinearMap.mem_ker, hxx, (ε R G).hom.toLinearMap_apply, map_sum] at hx
    simp_rw [map_smul, ε_of _, smul_eq_mul, mul_one] at hx
    exact hx
  have hx'' : x = ∑ i ∈ x.support, x i • (Finsupp.single i 1 - Finsupp.single 1 1) := by
    nth_rw 1 [← sub_zero x, ← zero_smul R (Finsupp.single 1 1), ← hx', hxx,
      Finset.sum_smul, ← Finset.sum_sub_distrib]
    simp [smul_sub]
  have hx''' : (⟨x, hx⟩ : (ε R G).hom.toLinearMap.ker) =
      ∑ i ∈ x.support, (x i) • ⟨Finsupp.single i 1 - Finsupp.single 1 1,
      singleBasis_mem_ker R i⟩ := by
    ext1
    simp_rw [Submodule.coe_sum, Submodule.coe_smul]
    exact hx''
  rw [hx''']
  refine Submodule.sum_mem _ (fun i _ ↦ if hi : i = 1 then ?_ else
    Submodule.smul_mem _ _ <| Submodule.mem_span_of_mem ?_)
  · refine Submodule.smul_mem _ _ ?_
    simp_rw [hi, sub_self]
    rw [show ⟨(0 : G →₀ R), _⟩ = (0 : (ε R G).hom.toLinearMap.ker) by rfl]
    exact zero_mem _
  · exact Set.mem_range.2 ⟨⟨i, by simp [Set.diff, hi]⟩, by simp [kerε.v]⟩

instance freekerV : Module.Free R (ε R G).hom.toLinearMap.ker :=
  .of_basis <| Module.Basis.mk (v := kerε.v R G) linearIndep_kerε_basis <|
     kerε_basis_span

instance [Finite G] : Module.Free R (aug R G).V :=
  @Module.Free.of_equiv _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((Rep.forgetKernelIso (ε R G) ≪≫ (ModuleCat.kernelIsoKer _)).toLinearEquiv :
    _ ≃ₗ[R] (ε R G).hom.toLinearMap.ker).symm (freekerV R G)

end Rep.leftRegular

end AugmentationModule
