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

instance : Functor.LaxMonoidal (functor R G 0) where
  ε := ModuleCat.ofHom <| by sorry
  μ := sorry
  μ_natural_left := sorry
  μ_natural_right := sorry
  associativity := sorry
  left_unitality := sorry
  right_unitality := sorry
