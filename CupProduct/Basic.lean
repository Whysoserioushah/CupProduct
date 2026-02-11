import Mathlib
import CupProduct.UpIso

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

@[simp]
lemma cup0_apply (a : H0 A) (b : H0 B) : cup0 A B a b = (H0Iso (A ⊗ B)).inv
  ⟨((H0Iso A).hom a).1 ⊗ₜ ((H0Iso B).hom b).1, mem_tensorInvariants A B
    (H0Iso A|>.hom.hom a) (H0Iso B|>.hom.hom b)⟩ := rfl

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
    (-1 : R) ^ p • (𝟙 _ ⊗ₘ δ h1 q (q + 1) rfl) ≫ map p (q + 1) (p + q + 1) (by omega) A S2.X₁

noncomputable section

def cup1aux [Fintype G] (σ : H0 B) : H1 A ⟶ H1 (A ⊗ B) := by
  -- haveI := δ_up_zero_epi A
  haveI : Epi (mapShortComplex₃ (shortExact_upSES A) (Nat.zero_add 1)).g :=
    δ_up_zero_epi A
  refine (mapShortComplex₃_exact (shortExact_upSES A) (Nat.zero_add 1)).desc
    ((ModuleCat.ofHom ((cup0 (up.obj A) B).flip σ)) ≫
    (CategoryTheory.Functor.mapIso (groupCohomology.functor R G _) (upTensor A B)).hom ≫
    (δ (shortExact_upSES (A ⊗ B)) 0 1 rfl : _ ⟶ H1 (A ⊗ B))) ?_
  dsimp
  change groupCohomology.map _ _ _ ≫ _ = 0
  sorry

noncomputable def CupProduct [Fintype G] (p q r : ℕ) (h : r = p + q) (A B : Rep R G) :
    -- do I want the aditional r = p + q condition?
    groupCohomology A p ⊗ groupCohomology B q ⟶ groupCohomology (A ⊗ B) r :=
  match p, q with
  | 0, 0 => cup0' A B ≫ eqToHom (by rw [h])
  | _, 1 => sorry--(sorry : _ ⟶ groupCohomology (A ⊗ B) 1) ≫ eqToHom _
  | 1, _ => sorry
  | (n + 2), q => (δUpIso A n).inv ▷ (groupCohomology B q) ≫
    CupProduct (n + 1) q (n + q + 1) (by omega) (up.obj A) B ≫
    ((functor R G (n + q + 1)).mapIso (upTensor A B)).hom ≫
    (δUpIso (A ⊗ B) (n + q)).hom ≫ eqToHom (by rw [h, add_assoc, add_comm q, ← add_assoc])
  | p, (n + 2) => sorry
