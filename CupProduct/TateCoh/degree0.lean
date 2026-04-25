import CupProduct.Cohomology.TateCohomology
import CupProduct.Cohomology.Functors.UpDown
import CupProduct.groupCoh.UpIso
import CupProduct.groupCoh.DownIso
import CupProduct.groupCoh.degree0

open CategoryTheory groupCohomology MonoidalCategory Rep.dimensionShift

universe u

variable (R G : Type u) [CommRing R] [Group G] [Fintype G]

noncomputable section

namespace TateCohomology

variable {R G}

abbrev cup0Aux' (A B : Rep R G) (a : A.ρ.invariants) :
    B.ρ.invariants ⧸ (LinearMap.range B.ρ.norm).submoduleOf B.ρ.invariants →ₗ[R]
    (A ⊗ B).ρ.invariants ⧸ (LinearMap.range (A ⊗ B).ρ.norm).submoduleOf (A ⊗ B).ρ.invariants :=
  Submodule.mapQ (R₂ := R) (τ₁₂ := .id R) _ _ (_root_.cup0Aux' A B a) <| fun x hx ↦ by
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.mem_range, Rep.tensor_V, Rep.tensor_ρ, _root_.cup0Aux', LinearMap.coe_mk,
      AddHom.coe_mk] at hx ⊢
    obtain ⟨b, hb⟩ := hx
    use a ⊗ₜ b
    simp only [Representation.norm, Representation.tprod_apply, LinearMap.coe_sum, Finset.sum_apply,
      TensorProduct.map_tmul, ← hb, TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun g _ ↦ by rw [a.2 g]

@[simps]
def cup0AuxAux (A B : Rep R G) : A.ρ.invariants →ₗ[R] B.ρ.invariants ⧸
    (LinearMap.range B.ρ.norm).submoduleOf B.ρ.invariants →ₗ[R]
    (A ⊗ B).ρ.invariants ⧸ (LinearMap.range (A ⊗ B).ρ.norm).submoduleOf (A ⊗ B).ρ.invariants where
  toFun a := cup0Aux' A B a
  map_add' a1 a2 := by
    ext b
    simp only [Rep.tensor_ρ, cup0Aux', LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.add_apply]
    change Submodule.Quotient.mk (cup0Aux A B (a1 + a2) b) = _
    rw [map_add, LinearMap.add_apply, Submodule.Quotient.mk_add]
    simp [cup0Aux]
  map_smul' r a := by
    ext b
    simp only [Rep.tensor_ρ, cup0Aux', LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.mapQ_apply, RingHom.id_apply, LinearMap.smul_apply]
    change Submodule.Quotient.mk (cup0Aux _ _ _ _) = _
    rw [map_smul, LinearMap.smul_apply, Submodule.Quotient.mk_smul]
    simp [cup0Aux]

set_option backward.isDefEq.respectTransparency false in
abbrev cup0Aux (A B : Rep R G) : A.ρ.invariants ⧸
    (LinearMap.range A.ρ.norm).submoduleOf A.ρ.invariants →ₗ[R] B.ρ.invariants ⧸
    (LinearMap.range B.ρ.norm).submoduleOf B.ρ.invariants →ₗ[R]
    (A ⊗ B).ρ.invariants ⧸ (LinearMap.range (A ⊗ B).ρ.norm).submoduleOf (A ⊗ B).ρ.invariants :=
  Submodule.liftQ _ (cup0AuxAux A B) <| fun a ha ↦ by
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.mem_range, Rep.tensor_V, Rep.tensor_ρ, cup0AuxAux, cup0Aux', LinearMap.mem_ker,
      LinearMap.coe_mk, AddHom.coe_mk] at ha ⊢
    ext b
    simp only [Rep.tensor_V, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, LinearMap.zero_comp, LinearMap.zero_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, LinearMap.mem_range]
    obtain ⟨a', ha'⟩ := ha
    use a' ⊗ₜ b.1
    simp only [Representation.norm, Representation.tprod_apply, LinearMap.coe_sum, Finset.sum_apply,
      TensorProduct.map_tmul, _root_.cup0Aux', Rep.tensor_V, Rep.tensor_ρ, ← ha',
      TensorProduct.sum_tmul, LinearMap.coe_mk, AddHom.coe_mk]
    exact Finset.sum_congr rfl fun g _ ↦ by rw [b.2 g]

def cup0 (A B : Rep.{u} R G) : (tateCohomology 0).obj A →ₗ[R] (tateCohomology 0).obj B →ₗ[R]
    (tateCohomology 0).obj (A ⊗ B) where
  toFun a := (TateCohomology.zeroIso (A ⊗ B)).inv.hom ∘ₗ
    cup0Aux A B (TateCohomology.zeroIso A|>.hom.hom a) ∘ₗ (TateCohomology.zeroIso B).hom.hom
  map_add' a1 a2 := by simp [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' r a := by simp [LinearMap.smul_comp, LinearMap.comp_smul]

abbrev cup0' (A B : Rep R G) : (tateCohomology 0).obj A ⊗ (tateCohomology 0).obj B ⟶
    (tateCohomology 0).obj (A ⊗ B) :=
  ModuleCat.ofHom <| TensorProduct.lift <| cup0 A B

variable (R G) in
@[simps]
def Rep.invariantsQuotFunctor : Rep.{u} R G ⥤ ModuleCat R where
  obj A := ModuleCat.of R <| A.ρ.invariants ⧸ (LinearMap.range A.ρ.norm).submoduleOf A.ρ.invariants
  map {A B} f := ModuleCat.ofHom <| Submodule.mapQ _ _
      ((Rep.invariantsFunctor R G).map f).hom <| fun x hx ↦ by
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.mem_range] at hx ⊢
    obtain ⟨a, ha⟩ := hx
    use f.hom a
    simp [Rep.invariantsFunctor, Rep.norm_comm_apply, ha]

abbrev case0 (A B : Rep.{u} R G) (r : ℤ) (h : r = 0 + 0) :
  (tateCohomology 0).obj A ⊗ (tateCohomology 0).obj B ⟶ (tateCohomology r).obj (A ⊗ B) :=
  cup0' A B ≫ eqToHom (by rw [h, zero_add])

abbrev case1 (A B : Rep.{u} R G) (n : ℕ) (q r : ℤ) (h : r = n.succ + q)
    (CupProduct : (tateCohomology ↑n).obj (up.{u}.obj A) ⊗
      (tateCohomology q).obj B ⟶ (tateCohomology (↑n + q)).obj (up.obj A ⊗ B)) :
  (tateCohomology n.succ).obj A ⊗ (tateCohomology q).obj B ⟶ (tateCohomology r).obj (A ⊗ B) :=
  ((δUpIsoTate A n).inv ▷ (tateCohomology q).obj B) ≫ CupProduct ≫
      (tateCohomology (n + q)).map (upTensor A B).hom ≫ (δUpIsoTate (A ⊗ B) (n + q)).hom ≫
      eqToHom.{u} (by rw [h, add_assoc, add_comm q 1, ← add_assoc, Nat.cast_succ])

abbrev case2 (A B : Rep.{u} R G) (p : ℤ) (n : ℕ) (r : ℤ) (h : r = p + n.succ)
    (CupProduct : (tateCohomology p).obj A ⊗
      (tateCohomology ↑n).obj (up.{u}.obj B) ⟶ (tateCohomology (p + ↑n)).obj (A ⊗ up.obj B)) :
  (tateCohomology p).obj A ⊗ (tateCohomology n.succ).obj B ⟶ (tateCohomology r).obj (A ⊗ B) :=
  (_ ◁ (δUpIsoTate B n).inv) ≫ CupProduct ≫
      ((-1) ^ p.natAbs • (tateCohomology (p + n)).map (upTensor' A B).hom) ≫
      (δUpIsoTate (A ⊗ B) (p + n)).hom ≫ eqToHom.{u} (by rw [h, Nat.cast_succ, add_assoc])

abbrev case3 (A B : Rep R G) (n : ℕ) (q r : ℤ) (h : r = Int.negSucc n + q)
    (CupProduct : (tateCohomology (Int.negSucc n + 1)).obj (down.{u}.obj A) ⊗
      (tateCohomology q).obj B ⟶ (tateCohomology (-n + q)).obj (down.obj A ⊗ B)) :
    (tateCohomology (Int.negSucc n)).obj A ⊗ (tateCohomology q).obj B ⟶
      (tateCohomology r).obj (A ⊗ B) :=
  (δDownIsoTate A (Int.negSucc n)).hom ▷ _ ≫ CupProduct ≫ (tateCohomology (-n + q)).map
      (downTensorIso A B).hom ≫ eqToHom (by rw [sub_add, sub_self, sub_zero]) ≫
      (δDownIsoTate (A ⊗ B) (-n + q - 1)).inv ≫ eqToHom.{u} (by
      rw [h, Int.negSucc_eq, neg_add, add_assoc, add_comm (-1), ← add_assoc, ← sub_eq_add_neg])

set_option backward.isDefEq.respectTransparency false in
abbrev case4 (A B : Rep R G) (p : ℤ) (n : ℕ) (r : ℤ) (h : r = p + Int.negSucc n)
    (CupProduct : (tateCohomology p).obj A ⊗
      (tateCohomology (Int.negSucc n + 1)).obj (down.{u}.obj B) ⟶
      (tateCohomology (p - n)).obj (A ⊗ down.obj B)) :
    (tateCohomology p).obj A ⊗ (tateCohomology (Int.negSucc n)).obj B ⟶
      (tateCohomology r).obj (A ⊗ B) :=
  _ ◁ (δDownIsoTate B (Int.negSucc n)).hom ≫ CupProduct ≫
      ((-1) ^ p.natAbs • ((tateCohomology (p - n)).map (downTensorIso' A B).hom)) ≫
      eqToHom (by rw [Int.sub_add_cancel]) ≫ (δDownIsoTate (A ⊗ B) (p - n - 1)).inv ≫
      eqToHom.{u} (by rw [h, Int.negSucc_eq, sub_sub, ← sub_eq_add_neg])

-- why is this so slow even after I split off the cases?

-- 117847570
-- 12946876
def CupProduct (A B : Rep.{u} R G) (p q r : ℤ) (h : r = p + q) :
    (tateCohomology p).obj A ⊗ (tateCohomology q).obj B ⟶ (tateCohomology r).obj (A ⊗ B) :=
  match p, q with
  | 0, 0 => case0 A B r h
  | Nat.succ n, q => case1 A B n q r h (CupProduct (up.{u, u}.obj A) B n q (n + q) rfl)
  | p, Nat.succ n => case2 A B p n r h (CupProduct A (up.{u, u}.obj B) p n (p + n) rfl)
  | Int.negSucc n, q =>
    case3 A B n q r h (CupProduct (down.{u, u}.obj A) B (Int.negSucc n + 1) q (-n + q) (by omega))
  | p, Int.negSucc n =>
    case4 A B p n r h (CupProduct A (down.{u, u}.obj B) p (Int.negSucc n + 1) (p - n) (by omega))
  termination_by (p.natAbs, q.natAbs)

structure IsCupProduct (map : (A B : Rep R G) → (p q r : ℤ) → (h : r = p + q) →
    (tateCohomology p).obj A ⊗ (tateCohomology q).obj B ⟶
    (tateCohomology r).obj (A ⊗ B)) : Prop where
  zero : map A B 0 0 0 rfl = cup0' A B
  commSq1 (p q : ℤ) (S1 : ShortComplex (Rep R G)) (h1 : S1.ShortExact)
    (h2 : (S1.map (tensorRight B)).ShortExact) :
    map S1.X₃ B p q (p + q) rfl  ≫ TateCohomology.δ h2 (p + q) =
    (TateCohomology.δ h1 p ⊗ₘ 𝟙 _) ≫ map S1.X₁ B (p + 1) q (p + q + 1) (by omega)
  commSq2 (p q : ℤ) (S2 : ShortComplex (Rep R G)) (h1 : S2.ShortExact)
    (h2 : (S2.map (tensorLeft A)).ShortExact) :
    map A S2.X₃ p q (p + q) rfl ≫ TateCohomology.δ h2 (p + q) =
    ((-1) ^ p.natAbs • (_ ◁ TateCohomology.δ h1 q)) ≫
    map A S2.X₁ p (q + 1) (p + q + 1) (by omega)

#check Int.negInduction
-- TODO: use `upSES` and `downSES` as the first SES to prove if two maps
-- are `IsCupProduct`, then they are equal.
lemma IsCupProduct.unique (map1 map2 : (A B : Rep R G) → (p q r : ℤ) → (h : r = p + q) →
    (tateCohomology p).obj A ⊗ (tateCohomology q).obj B ⟶
    (tateCohomology r).obj (A ⊗ B)) (h1 : IsCupProduct map1) (h2 : IsCupProduct map2) :
    map1 = map2 := by
  funext A B p
  induction p with
  | zero =>
    funext q r h
    induction q generalizing A B r with
    | zero => subst h; simp [h1.zero, h2.zero]
    | succ m hm =>
      have h1' := h1.commSq2 0 m (A := A) (upSES B) (shortExact_upSES B)
        (shortExact_upSESTensorLeft _ _)
      have h2' := h2.commSq2 0 m (A := A) (upSES B) (shortExact_upSES B)
        (shortExact_upSESTensorLeft _ _)
      dsimp [-up_obj, zero_add, one_smul] at h1' h2'
      rw [one_smul] at h1' h2'
      change _ = (((tateCohomology 0).obj A ◁ᵢ δUpIsoTate B m).hom) ≫ _ at h1' h2'
      rw [← Iso.inv_comp_eq] at h1' h2'
      rw [← add_assoc] at h
      subst h
      rw [← h1', ← h2', hm]
    | pred m hm =>
      have h1' := h1.commSq2 0 (-m-1) (A := A) (downSES B) (shortExact_downSES B)
        (shortExact_downSESTensorLeft _ _)
      have h2' := h2.commSq2 0 (-m-1) (A := A) (downSES B) (shortExact_downSES B)
        (shortExact_downSESTensorLeft _ _)
      dsimp [-down_obj] at h1' h2'
      rw [one_smul] at h1' h2'
      subst h

      -- change _ = (((tateCohomology 0).obj A ◁ᵢ δDownIsoTate B (-m)).hom) ≫ _ at h1' h2'



      sorry
  | succ i _ =>
    funext q r h
    induction q generalizing A B r with
    | zero => sorry
    | succ i _ => sorry
    | pred i _ => sorry
  | pred i _ => sorry

-- TODO : change `TateCohomology.map` to use `(i j : ℤ) (h : i + 1 = j)` instead of `i` and `i + 1`
open groupCohomology.TateCohomology in
lemma δ_naturality {X1 X2 : ShortComplex (Rep.{u, u, u} R G)}
    (hX1 : X1.ShortExact) (hX2 : X2.ShortExact) (F : X1 ⟶ X2) (i : ℤ) :
    TateCohomology.δ hX1 i ≫ (tateCohomology (i + 1)).map F.τ₁ =
    (tateCohomology i).map F.τ₃ ≫ TateCohomology.δ hX2 i :=
  HomologicalComplex.HomologySequence.δ_naturality
    (tateComplexFunctor.mapShortComplex.map F)
    (map_tateComplexFunctor_shortExact hX1) (map_tateComplexFunctor_shortExact hX2) i (i + 1) rfl

lemma case00 {B : Rep R G} {S : ShortComplex (Rep R G)} (hS1 : S.ShortExact)
    (hS2 : (S.map (tensorRight B)).ShortExact) :
    CupProduct S.X₃ B 0 0 0 rfl ≫ TateCohomology.δ hS2 0 =
    (TateCohomology.δ hS1 0 ⊗ₘ 𝟙 ((tateCohomology 0).obj B)) ≫
    CupProduct S.X₁ B 1 0 1 rfl := by

  sorry

theorem IsCup_CupProduct :
    IsCupProduct (R := R) (G := G) CupProduct := by
  constructor
  · intro A B; simp [CupProduct]
  · intro B p q S hS1 hS2
    induction p with
    | zero =>
      induction q with
      | zero => exact case00 hS1 hS2
      | succ i hi => sorry
      | pred i hi => sorry
    | succ i _ => sorry
    | pred i _ => sorry
    -- match p, q with
    -- | 0, 0 =>
    --   unfold CupProduct
    --   simp [case1]
    --   sorry
    -- | Nat.succ n, q =>
    --   sorry
    -- | p, Nat.succ n => sorry
    -- | .ofNat _, .negSucc _ => sorry
    -- | .negSucc _, .ofNat _ => sorry
    -- | .negSucc _, .negSucc _ => sorry
  · sorry

-- abbrev TateCohomology.π (A : Rep R G) (n : ℕ) :
--   (tateComplex A).cycles n ⟶ (tateCohomology n).obj A := (tateComplex A).homologyπ n

-- -- abbrev lift_subtype (A : Rep R G) : ModuleCat.of R (A.ρ.invariants ⧸
-- --     (LinearMap.range A.ρ.norm).submoduleOf A.ρ.invariants) ⟶ A.V :=
-- --   ModuleCat.ofHom <| Submodule.liftQ _ A.ρ.invariants.subtype <| fun x hx ↦ by
-- --   simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
-- --     LinearMap.mem_range, Submodule.ker_subtype, Submodule.mem_bot] at hx ⊢
-- --   obtain ⟨a, ha⟩ := hx

-- --   sorry

-- -- lemma map_id_comp_zeroIso_f {A B : Rep R G} (f : A ⟶ B) : (tateCohomology 0).map f ≫
-- --     (TateCohomology.zeroIso B).hom ≫
-- --     (ModuleCat.ofHom (Submodule.liftQ _ B.ρ.invariants.subtype _) : _ ⟶ B.V) = _ := by

-- --   sorry

-- #check map_id_comp_H0Iso_hom
-- lemma map_id_comp_zeroIso {A B : Rep R G} (f : A ⟶ B) : (tateCohomology 0).map f ≫
--     (TateCohomology.zeroIso B).hom = (TateCohomology.zeroIso A).hom ≫
--     (Rep.invariantsQuotFunctor R G).map f := by
--   ext a
--   sorry

-- open TensorProduct

-- def cup0NatTrans : .prod (tateCohomology 0) (tateCohomology 0) ⋙ tensor (ModuleCat R) ⟶
--     tensor (Rep R G) ⋙ tateCohomology 0 where
--   app MN := cup0' MN.1 MN.2
--   naturality := sorry

-- end TateCohomology

-- instance : (@tateCohomology R G _ _ _ 0).LaxBraided where
--   ε := sorry
--   μ := sorry
--   μ_natural_left := sorry
--   μ_natural_right := sorry
--   associativity := sorry
--   left_unitality := sorry
--   right_unitality := sorry
--   braided := sorry
end TateCohomology
