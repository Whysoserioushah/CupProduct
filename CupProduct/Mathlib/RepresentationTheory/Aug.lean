import CupProduct.Mathlib.RepresentationTheory.Rep
import Mathlib

universe u

variable (R G : Type u) [CommRing R] [Group G]

noncomputable section

def Rep.aug : Rep R G := CategoryTheory.Limits.kernel (Rep.leftRegular.ε R G)

namespace Rep.leftRegular

variable [Fintype G]

/-- `Rep.norm` applied to `1 : R[G]` is indeed `∑ g, g`. -/
lemma norm_of_one : (Rep.norm (Rep.leftRegular R G)).hom.hom (Rep.leftRegular.of 1) =
    ∑ g, Rep.leftRegular.of g := by
  ext g'
  simp [Representation.norm, Rep.leftRegular.of]

/-- the map from `R ⟶ R[G]` that sends `r : R` to `r • N` where `N` is the "norm" element. -/
abbrev μ : trivial R G R ⟶ leftRegular R G where
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

end Rep.leftRegular
