import CupProduct.Cohomology.TateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G] (A B : Rep.{u} R G)

noncomputable section

namespace TateCohomology

abbrev cocycles (n : ℤ) := (groupCohomology.tateComplex A).cycles n

abbrev iCocycles (n : ℤ) := (groupCohomology.tateComplex A).iCycles n

-- lemma iCocyclesOfNat_eq {n : ℕ} : iCocycles A n = groupCohomology.iCocycles A n := by
--   -- simp only [iCocycles, cocycles, groupCohomology.tateComplex_iCyclesOfNat]
--   sorry

abbrev cocyclesMkOfNat {n : ℕ} (f : (Fin n → G) → A)
    (hf : (groupCohomology.tateComplex A).d n (n + 1) f = 0) : cocycles A n :=
  (groupCohomology.tateComplex A).cyclesMk f (n + 1) (by simp) hf

abbrev cocyclesMkOfNeg {n : ℕ} (f : (Fin n → G) →₀ A)
    (hf : (groupCohomology.tateComplex A).d (-(n + 1)) (-n) f = 0) :
    cocycles A (-(n + 1)) :=
  (groupCohomology.tateComplex A).cyclesMk f (-n) (by simp) hf

abbrev π (n : ℤ) : cocycles A n ⟶ (groupCohomology.tateCohomology n).obj A :=
  (groupCohomology.tateComplex A).homologyπ n

open CategoryTheory MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
-- this is very wrong and need more api on `ConnectData` to fix
private abbrev blah :
    ((groupCohomology.tateComplex A).d 0 ((ComplexShape.up ℤ).next 0)).hom.ker ≃ₗ[R]
    ((groupCohomology.inhomogeneousCochains A).d 0 ((ComplexShape.up ℕ).next 0)).hom.ker where
  toFun := fun ⟨(x : (Fin 0 → G) → A), hx⟩ ↦ ⟨x, by
    simp only [groupCohomology.tateComplex_X, CochainComplex.ConnectData.X_zero,
      CochainComplex.of_x, LinearMap.mem_ker] at hx ⊢
    rw [show ((ComplexShape.up ℤ).next 0) = (0 : ℕ) + 1 by simp] at hx
    change ((groupCohomology.tateComplex A).d (0 : ℕ) ((0 : ℕ) + 1)).hom x = 0 at hx
    rw [groupCohomology.tateComplex_d_ofNat] at hx
    rw [show (ComplexShape.up ℕ).next 0 = 1 by simp]
    simpa using hx⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by ext; simp
  invFun := fun ⟨(x : (Fin 0 → G) → A), hx⟩ ↦ ⟨x, by
    simp only [CochainComplex.of_x, LinearMap.mem_ker, groupCohomology.tateComplex_X,
      CochainComplex.ConnectData.X_zero] at hx ⊢
    rw [show ((ComplexShape.up ℤ).next 0) = (0 : ℕ) + 1 by simp]
    change ((groupCohomology.tateComplex A).d (0 : ℕ) ((0 : ℕ) + 1)).hom x = 0
    rw [groupCohomology.tateComplex_d_ofNat]
    rw [show (ComplexShape.up ℕ).next 0 = 1 by simp] at hx
    simpa using hx⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev cocyclesIso₀ : cocycles A 0 ≅ ModuleCat.of R A.ρ.invariants :=
  ((groupCohomology.tateComplex A).sc 0).moduleCatCyclesIso ≪≫
  (blah A).toModuleIso
  ≪≫ ((groupCohomology.inhomogeneousCochains A).sc 0).moduleCatCyclesIso.symm
  ≪≫ groupCohomology.cocyclesIso₀ A

abbrev cochainsIso₀ : (groupCohomology.tateComplex A).X 0 ≅ ModuleCat.of R A :=
    groupCohomology.cochainsIso₀ A

set_option backward.isDefEq.respectTransparency false in
lemma cocyclesIso₀_hom_comp_f :
    (cocyclesIso₀ A).hom ≫ (groupCohomology.shortComplexH0 A).f =
    iCocycles A 0 ≫ (cochainsIso₀ A).hom := by
  unfold cochainsIso₀ cocyclesIso₀
  simp only [Iso.trans_hom, Category.assoc, groupCohomology.cocyclesIso₀_hom_comp_f A]
  simp only [← Category.assoc]
  congr 1
  unfold iCocycles HomologicalComplex.iCycles

  -- ext ⟨(x : (Fin 0 → G) → A), hx⟩
  -- erw [← Category]
  -- rw [← groupCohomology.cocyclesIso₀_hom_comp_f A]

  sorry

abbrev zeroTensor (n : ℤ) (σ : cocycles A 0) (τ : cocycles B n) :
    cocycles (A ⊗ B) n := match n with
  | .ofNat n => cocyclesMkOfNat (A ⊗ B)
      (fun f ↦ TensorProduct.mk R A B (cocyclesIso₀ A|>.hom.hom σ)
      sorry) sorry
  | .negSucc _ => sorry

end TateCohomology
