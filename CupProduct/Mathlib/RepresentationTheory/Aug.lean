import CupProduct.Mathlib.RepresentationTheory.Rep
-- import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib

universe u

variable (R G : Type u) [CommRing R] [Group G]

open CategoryTheory
noncomputable section

def Rep.aug : Rep R G := Limits.kernel (Rep.leftRegular.ε R G)

namespace Rep.leftRegular

variable [Fintype G]

/-- `Rep.norm` applied to `1 : R[G]` is indeed `∑ g, g`. -/
lemma norm_of_one : (Rep.norm (Rep.leftRegular R G)).hom.hom (Rep.leftRegular.of 1) =
    ∑ g, Rep.leftRegular.of g := by
  ext g'
  simp [Representation.norm, Rep.leftRegular.of]

/-- the map from `R ⟶ R[G]` that sends `r : R` to `r • N` where `N` is the "norm" element. -/
def μ : trivial R G R ⟶ leftRegular R G where
  hom := ModuleCat.ofHom <| (LinearMap.lsmul R (leftRegular R G)).flip (∑ g, Rep.leftRegular.of g)
  comm g := by
    ext g'
    simp only [ModuleCat.endRingEquiv, RingEquiv.symm_mk, RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe,
      RingEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply, Representation.isTrivial_def,
      ModuleCat.ofHom_id, map_sum, LinearMap.lsmul_flip_apply, CategoryTheory.Category.id_comp,
      ModuleCat.hom_ofHom, LinearMap.coe_sum, Finset.sum_apply, LinearMap.toSpanSingleton_apply,
      one_smul, Finsupp.coe_finset_sum, ModuleCat.hom_comp, LinearMap.coe_comp,
      Representation.ofMulAction_apply, smul_eq_mul]
    refine Finset.sum_equiv (Equiv.mulLeft g⁻¹) (by simp) (fun i ↦ ?_)
    classical
    simp only [Finset.mem_univ, Equiv.coe_mulLeft, forall_const]
    rw [of_apply, of_apply]
    split_ifs with h1 h2 h3
    all_goals try grind [mul_right_inj]

@[simp]
lemma μ_one : (μ R G).hom (1 : R) = ∑ g, Rep.leftRegular.of g := by
  simp [μ]

@[simp]
lemma μ_zero : (μ R G).hom (0 : R) = 0 := by simp [μ]

@[simp]
lemma μ_apply (r : R) : (μ R G).hom r = r • ∑ g, Rep.leftRegular.of g := by rfl

def coaug : Rep R G := CategoryTheory.Limits.cokernel (μ R G)

@[simp]
lemma _root_.Rep.quotient_V {G} [Monoid G] (A : Rep R G) (W : Submodule R A) (h : ∀ (g : G), W ≤
    Submodule.comap (A.ρ g) W) : (Rep.quotient A W h).V = (A.V ⧸ W) := by
  simp

/-- The forgetful functor from `Rep R G` to `ModuleCat R` preserves cokernels,
giving an isomorphism between the underlying module of the cokernel and
the cokernel of the underlying module map. -/
noncomputable def _root_.Rep.forgetCokernelIso {R G : Type u} [CommRing R] [Group G] {A B : Rep R G}
    (f : A ⟶ B) : (Limits.cokernel f).V ≅ Limits.cokernel f.hom :=
  (preservesColimitIso (forget₂ (Rep R G) (ModuleCat R)) (Limits.parallelPair f 0)).trans
    (Limits.HasColimit.isoOfNatIso (Limits.parallelPair.ext (Iso.refl _) (Iso.refl _)
      (by simp [forget₂_map]) (by simp)))

lemma range_μ : (μ R G).hom.hom.range = Submodule.span R {∑ g, Rep.leftRegular.of g} := by
  ext x
  simp +contextual only [LinearMap.mem_range, Submodule.mem_span_singleton]
  constructor
  all_goals exact fun ⟨y, hy⟩ ↦ ⟨y, by rwa [μ_apply] at *⟩

lemma le_comap (g : G) : R ∙ ∑ g, of g ≤ Submodule.comap ((leftRegular R G).ρ g)
    (R ∙ ∑ g, of g) := by
  simp only [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap, map_sum]
  conv => enter [2, 2, x]; rw [ρ_apply_of]
  nth_rw 2 [Finset.sum_equiv (t := Finset.univ) (g := fun i ↦ of i)
    (Equiv.mulLeft g) (by simp) (by simp)]
  exact Submodule.mem_span_singleton_self _

-- is this correct?
-- def coaugIsoQuot : coaug R G ≅ Rep.quotient (Rep.leftRegular R G)
--     (Submodule.span R {∑ g, Rep.leftRegular.of g}) (le_comap R G) where
--   hom := {
--     hom := ((Rep.forgetCokernelIso (μ R G)) ≪≫ ModuleCat.cokernelIsoRangeQuotient (μ R G).hom ≪≫
--       (Submodule.quotEquivOfEq _ _ (range_μ R G)).toModuleIso).hom
--     comm g := by
--       ext1
--       simp only [Iso.trans_hom, LinearEquiv.toModuleIso_hom, ModuleCat.hom_comp,
--         ModuleCat.hom_ofHom, ρ_hom, RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, of_ρ,
--         MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe, Function.comp_apply,
--         Representation.quotient_apply, Category.assoc]
--       ext x
--       simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
--         ModuleCat.endRingEquiv, RingEquiv.symm_mk, RingEquiv.coe_mk, Equiv.coe_fn_mk,
--         ModuleCat.hom_ofHom]
--       -- have := (coaug R G).hom_comm_apply _ _ x
--       -- rw [show (R ∙ ∑ g, of g).mapQ (R ∙ ∑ g, of g) ((Representation.ofMulAction R G G) g)
--       --   (le_comap R G g) = LinearMap.id by
--       --   ext g' : 3
--       --   simp
--       --   sorry]
--       -- simp
--       sorry
--   }
--   inv := sorry
--   hom_inv_id := sorry
--   inv_hom_id := sorry

end Rep.leftRegular
