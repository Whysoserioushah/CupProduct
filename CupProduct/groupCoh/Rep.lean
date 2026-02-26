import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.RepresentationTheory.Rep

universe u

variable (R G : Type u) [CommRing R] [Group G]

open CategoryTheory

instance : HasForget₂ (Rep R G) Ab := .trans (Rep R G) (ModuleCat R) Ab

instance : (forget₂ (Rep R G) Ab).Additive :=
  inferInstanceAs (_ ⋙ _).Additive

instance : (forget₂ (Rep R G) Ab).PreservesHomology :=
  { preservesKernels _ _ _ := Limits.comp_preservesLimit _ _
    preservesCokernels _ _ _:= Limits.comp_preservesColimit _ _ }
