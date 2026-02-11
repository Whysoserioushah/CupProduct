import Mathlib
import CupProduct.Cohomology.AugmentationModule

open CategoryTheory Rep.leftRegular MonoidalCategory

universe u

variable (R G : Type u) [CommRing R] [Group G]

noncomputable section

def upSES₀ [Fintype G] : ShortComplex (Rep R G) where
  X₁ := Rep.trivial R G R
  X₂ := Rep.leftRegular R G
  X₃ := coaug R G
  f := μ R G
  g := Limits.cokernel.π _
  zero := by ext1; simp

lemma shortExact_upSES₀ [Fintype G] : (upSES₀ R G).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := Rep.mono_iff_injective (μ R G) |>.2 fun x y h ↦ by
    dsimp [μ] at x y h
    simpa [of] using Finsupp.ext_iff.1 h 1
  epi_g := Limits.coequalizer.π_epi

instance : HasForget₂ (Rep R G) Ab := .trans (Rep R G) (ModuleCat R) Ab

instance : (forget₂ (Rep R G) Ab).Additive :=
  inferInstanceAs (_ ⋙ _).Additive

instance : (forget₂ (Rep R G) Ab).PreservesHomology :=
  { preservesKernels _ _ _ := Limits.comp_preservesLimit _ _
    preservesCokernels _ _ _:= Limits.comp_preservesColimit _ _ }

open ShortComplex
lemma shortExact_upSES' [Fintype G] : ((upSES₀ R G).map (tensorRight A)).Exact :=
  exact_iff_exact_map_forget₂ _|>.2 <| by
  change (((upSES₀ R G).map _).map (_ ⋙ _)).Exact
  rw [map_comp, ← exact_iff_exact_map_forget₂, moduleCat_exact_iff_ker_sub_range]
  simp only [upSES₀, map_X₂, Functor.flip_obj_obj, curriedTensor_obj_obj,
    RepresentationTheory.Rep.forget₂_obj, Action.tensorObj_V, map_X₃, map_g, Functor.flip_obj_map,
    curriedTensor_map_app, Rep.forget₂_map, Action.whiskerRight_hom, map_X₁, map_f]
  intro fx h
  induction fx using TensorProduct.induction_on with
  | zero => simp
  | tmul f x =>
    change G →₀ R at f
    rw [LinearMap.mem_ker] at h
    change (TensorProduct.map _ _) _ = 0 at h
    simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq] at h
    simp only [ModuleCat.hom_whiskerRight, LinearMap.mem_range]
    have : Exact ((upSES₀ R G).map (_ ⋙ _)) :=
      exact_iff_exact_map_forget₂ _|>.1 <| (shortExact_upSES₀ R G).1
    rw [map_comp, ← exact_iff_exact_map_forget₂, moduleCat_exact_iff_range_eq_ker] at this
    replace this := by simpa [upSES₀] using SetLike.ext_iff.1 this f

    sorry
  | add x y _ _ => sorry
