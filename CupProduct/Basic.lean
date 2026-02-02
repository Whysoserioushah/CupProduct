import Mathlib
import CupProduct.Mathlib.RepresentationTheory.Aug

open CategoryTheory groupCohomology

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

-- noncomputable def cup0' : (ModuleCat.of R (H0 A × H0 B)) ⟶ H0 (A ⊗ B) := ModuleCat.ofHom {
--   toFun ab := cup0 A B ab.1 ab.2
--   map_add' := by simp
--   map_smul' := sorry
-- }
  -- (AddMonoidHom.uncurry (cup0 A B))

-- how to do the product thing???

@[simp]
lemma cup0_apply (a : H0 A) (b : H0 B) : cup0 A B a b = (H0Iso (A ⊗ B)).inv
  ⟨((H0Iso A).hom a).1 ⊗ₜ ((H0Iso B).hom b).1, mem_tensorInvariants A B
    (H0Iso A|>.hom.hom a) (H0Iso B|>.hom.hom b)⟩ := rfl

noncomputable def groupCohomology.cast {n m} (h : n = m) :
    groupCohomology A n ≅ groupCohomology A m := h ▸ Iso.refl _

structure CupProductData where
  map (p q r : ℕ) (h : r = p + q) (A B : Rep R G) :
    groupCohomology A p →ₗ[R] groupCohomology B q →ₗ[R] groupCohomology (A ⊗ B) r
  zero : map 0 0 0 rfl = cup0
  commSq1 (p q : ℕ) (S1 : ShortComplex (Rep R G)) (h1 : S1.ShortExact)
    (h2 : (S1.map (tensorRight B)).ShortExact) :
    ∀ (a : groupCohomology S1.X₃ p) (b : groupCohomology B q),
    (δ h2 (p + q) (p + q + 1) rfl).hom (map p q (p + q) rfl S1.X₃ B a b) =
    (map (p + 1) q (p + q + 1) (by omega) S1.X₁ B ((δ h1 p (p + 1) rfl).hom a) b)
  commSq2 (p q : ℕ) (S2 : ShortComplex (Rep R G)) (h1 : S2.ShortExact)
    (h2 : (S2.map (tensorLeft A)).ShortExact) :
    ∀ (a : groupCohomology A p) (b : groupCohomology S2.X₃ q),
    (δ h2 (p + q) (p + q + 1) rfl).hom (map p q (p + q) rfl A S2.X₃ a b) =
    (-1) ^ p • map p (q + 1) (p + q + 1) (add_assoc p q 1)
    A S2.X₁ a ((δ h1 q (q + 1) rfl).hom b)

def Rep.zpow (A : Rep R G) (m : ℤ) : Rep R G := match m with
  | 0 => A
  | (n : ℕ) + 1 => sorry
  | - (n + 1: ℕ)  => sorry
