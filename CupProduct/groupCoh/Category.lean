import Mathlib

open CategoryTheory MonoidalCategory Limits Functor

variable (C D E : Type*) [Category C] [Category D] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [BraidedCategory C] [EnoughInjectives C] [Abelian D] [MonoidalCategory D] [BraidedCategory D]
  [Category E] [Abelian E] [MonoidalCategory E] [MonoidalPreadditive E] [BraidedCategory E]
  -- F is the forgetful functor
  (F : C ⥤ E) [F.Faithful] [PreservesLimits F] [PreservesColimits F] [hF : F.Monoidal]
  (Hzero : C ⥤ D) [Hzero.Additive] [Hzero.LaxBraided] [PreservesLimits Hzero]
  [PreservesZeroMorphisms Hzero]
  (RGSES : ShortComplex C) (h1 : (RGSES.map F).Splitting) (h2 : RGSES.X₁ = 𝟙_ C)

abbrev coindCat : C ⥤ C := tensorLeft RGSES.X₂

abbrev upCat : C ⥤ C := tensorLeft RGSES.X₃

def μNatIso (M : C) : tensorRight M ⋙ F ≅ F ⋙ tensorRight (F.obj M) :=
  NatIso.ofComponents (fun X ↦ hF.μIso _ X _|>.symm)

def Isoμ_shortComplex (M : C) : (RGSES.map (tensorRight M) |>.map F) ≅
    (RGSES.map F).map (tensorRight <|F.obj M) := by
  rw [← ShortComplex.map_comp, ← ShortComplex.map_comp]
  exact ShortComplex.mapNatIso _ <| μNatIso _ _ _ _

def splitAux (M : C) : ((RGSES.map F).map (tensorRight (F.obj M))).Splitting where
  r := h1.r ▷ F.obj M
  s := h1.s ▷ F.obj M
  f_r := by
    simp only [ShortComplex.map_X₁, flip_obj_obj, curriedTensor_obj_obj, ShortComplex.map_X₂,
      ShortComplex.map_f, flip_obj_map, curriedTensor_map_app, ← comp_whiskerRight]
    change ((RGSES.map F).f ≫ h1.r) ▷ _ = _
    rw [h1.3, id_whiskerRight]
    rfl
  s_g := by
    simp only [ShortComplex.map_X₃, flip_obj_obj, curriedTensor_obj_obj, ShortComplex.map_X₂,
      ShortComplex.map_g, flip_obj_map, curriedTensor_map_app, ← comp_whiskerRight]
    change (h1.s ≫ (RGSES.map F).g) ▷ _ = _
    rw [h1.4, id_whiskerRight]
    rfl
  id := by
    simp only [ShortComplex.map_X₂, flip_obj_obj, curriedTensor_obj_obj, ShortComplex.map_X₁,
      ShortComplex.map_f, flip_obj_map, curriedTensor_map_app, ← comp_whiskerRight,
      ShortComplex.map_X₃, ShortComplex.map_g, ← MonoidalPreadditive.add_whiskerRight]
    change (h1.r ≫ (RGSES.map F).f + (RGSES.map F).g ≫ h1.s) ▷ _ = _
    rw [h1.5, id_whiskerRight]
    rfl

def split_upSESCat_forget (M : C) : (RGSES.map (tensorRight M) |>.map F).Splitting :=
  .ofIso (splitAux C E F RGSES h1 M) (Isoμ_shortComplex C E F RGSES M).symm

include h1 in
omit [BraidedCategory C] [EnoughInjectives C] [BraidedCategory E] [PreservesColimits F] in
lemma shortExact_upCat (M : C) : (RGSES.map (tensorRight M)).ShortExact where
  exact := reflects_exact_of_faithful F _ (split_upSESCat_forget C E F RGSES h1 M).exact
  mono_f := Functor.ReflectsMonomorphisms.reflects (F := F) _
    (split_upSESCat_forget C E F RGSES h1 M).shortExact.mono_f
  epi_g := Functor.ReflectsEpimorphisms.reflects (F := F) _
    (split_upSESCat_forget C E F RGSES h1 M).shortExact.epi_g

-- homework for richard : prove if enough injectives, then the derived
-- functors of H0 is isomorphic to Hn
variable (h3 : ∀ n : ℕ, IsZero <| tensorLeft RGSES.X₂ ⋙ Hzero.rightDerived (n + 1))

-- three resolution by enought injective => three cochain complex => short exact sequence
-- of cochain complexes => long exact sequence of cohomology (by horseshoe lemma?)
-- => Hⁿ iso to Hⁿ⁺¹ for 0 < n


-- has value because Functor.mapShortComplex needs PreservesZeroMorphisms and
-- `injectiveResolution` only preserves zero up to homotopy
noncomputable def ShortComplex.toHomotopyCatSc : ShortComplex C ⥤
    ShortComplex (HomotopyCategory D (ComplexShape.up ℕ)) where
  obj S := {
    X₁ := (HomotopyCategory.quotient D (ComplexShape.up ℕ)).obj <|
      Hzero.mapHomologicalComplex _|>.obj (InjectiveResolution.of S.X₁).cocomplex
    X₂ := (HomotopyCategory.quotient D (ComplexShape.up ℕ)).obj <|
      Hzero.mapHomologicalComplex _|>.obj (InjectiveResolution.of S.X₂).cocomplex
    X₃ := (HomotopyCategory.quotient D (ComplexShape.up ℕ)).obj <|
      Hzero.mapHomologicalComplex _|>.obj (InjectiveResolution.of S.X₃).cocomplex
    f := (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map <|
      Hzero.mapHomologicalComplex _|>.map <| InjectiveResolution.desc S.f _ _
    g := (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map <|
      Hzero.mapHomologicalComplex _|>.map <| InjectiveResolution.desc S.g _ _
    zero := by
      rw [← map_comp, ← map_comp, HomotopyCategory.quotient_map_eq_zero_iff]
      refine ⟨?_⟩
      rw [← (Hzero.mapHomologicalComplex (ComplexShape.up ℕ)).map_zero]
      refine Hzero.mapHomotopy ?_
      refine Homotopy.trans (InjectiveResolution.descCompHomotopy S.f S.g _ _ _).symm ?_
      rw [S.zero]
      exact InjectiveResolution.descHomotopy 0 _ 0 (by simp) (by simp)}
  map {S1 S2} fS := {
    τ₁ := (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map <|
      Hzero.mapHomologicalComplex _|>.map <| InjectiveResolution.desc fS.1 _ _
    τ₂ := (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map <|
      Hzero.mapHomologicalComplex _|>.map <| InjectiveResolution.desc fS.2 _ _
    τ₃ := (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map <|
      Hzero.mapHomologicalComplex _|>.map <| InjectiveResolution.desc fS.3 _ _
    comm₁₂ := by
      simp only [← map_comp]
      refine HomotopyCategory.eq_of_homotopy _ _ <| Hzero.mapHomotopy <|
        Homotopy.trans (InjectiveResolution.descCompHomotopy _ _ _ _ _).symm <|
        Homotopy.trans (.ofEq ?_) (InjectiveResolution.descCompHomotopy _ _ _ _ _)
      rw [fS.comm₁₂]
    comm₂₃ := by
      simp only [← map_comp]
      refine HomotopyCategory.eq_of_homotopy _ _ <| Hzero.mapHomotopy <|
        Homotopy.trans (InjectiveResolution.descCompHomotopy _ _ _ _ _).symm <|
        Homotopy.trans (.ofEq ?_) (InjectiveResolution.descCompHomotopy _ _ _ _ _)
      rw [fS.comm₂₃]}
  map_id S := by
    ext <;> simp only [ShortComplex.id_τ₁, ShortComplex.id_τ₂, ShortComplex.id_τ₃] <;> {
      rw [← map_id (HomotopyCategory.quotient D _),
        ← map_id (Hzero.mapHomologicalComplex _)]
      exact HomotopyCategory.eq_of_homotopy _ _
        (Hzero.mapHomotopy (InjectiveResolution.descIdHomotopy _ _)) }
  map_comp {S1 S2 S3} fS gS := by
    ext <;>
      simp only [ShortComplex.comp_τ₁, ShortComplex.comp_τ₂,
        ShortComplex.comp_τ₃] <;>
      simp only [← map_comp] <;>
      exact HomotopyCategory.eq_of_homotopy _ _ <|
        Hzero.mapHomotopy <|
          InjectiveResolution.descCompHomotopy _ _ _ _ _

variable {C}
def myX2 {S : ShortComplex C} (hS : S.ShortExact) (I1 : InjectiveResolution S.X₁)
  (I3 : InjectiveResolution S.X₃) : InjectiveResolution S.X₂ := sorry

noncomputable def ShortExact.mapInjectiveResol {S : ShortComplex C} (hS : S.ShortExact) :
    ShortComplex (CochainComplex C ℕ) where
  X₁ := (InjectiveResolution.of S.X₁).cocomplex
  X₂ := (myX2 hS (InjectiveResolution.of S.X₁) (InjectiveResolution.of S.X₃)).cocomplex
  X₃ := (InjectiveResolution.of S.X₃).cocomplex
  f := sorry
  g := sorry
  zero := sorry

lemma ShortExact.mapInjectiveResol_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    ((ShortExact.mapInjectiveResol hS).map
    (Hzero.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact := sorry

#check DerivedCategory.triangleOfSES
#check homologySequenceComposableArrows₅
-- def
#check CategoryTheory.ShortComplex.ShortExact.δ

#check rightDerived

#check groupCohomology.δ
#check CategoryTheory.ShortComplex.SnakeInput.naturality_δ
#check HomologicalComplex.HomologySequence.δ_naturality
-- there is groupCohomology.δ_naturality in CFT need to be imported here
noncomputable def Category.upIso (i j : ℕ) (h : j = i + 1) :
    ((ShortExact.mapInjectiveResol (shortExact_upCat C E F RGSES h1 M)).map
    (Hzero.mapHomologicalComplex (ComplexShape.up ℕ))).X₃.homology (i + 1) ≅
    ((ShortExact.mapInjectiveResol (shortExact_upCat C E F RGSES h1 M)).map
    (Hzero.mapHomologicalComplex (ComplexShape.up ℕ))).X₁.homology (j + 1) := by
  have h0 := ShortComplex.ShortExact.homology_exact₁ (ShortExact.mapInjectiveResol_shortExact
    D Hzero (shortExact_upCat C E F RGSES h1 M)) j (j + 1) rfl
  have h0' := ShortComplex.ShortExact.homology_exact₃ (ShortExact.mapInjectiveResol_shortExact
    D Hzero (shortExact_upCat C E F RGSES h1 M))
  have zero' := by simpa using (h3 j).obj M
  simp only [ShortComplex.map_X₃, ShortComplex.map_X₁, ShortComplex.map_X₂,
    ShortComplex.map_f] at h0
  unfold ShortExact.mapInjectiveResol at h0 h0' ⊢
  simp only [ShortComplex.map_X₁, flip_obj_obj, curriedTensor_obj_obj, ShortComplex.map_X₂,
    ShortComplex.map_X₃] at h0
  have := by simpa using InjectiveResolution.isoRightDerivedObj (myX2 (shortExact_upCat C E F
    RGSES h1 M) (InjectiveResolution.of _) (InjectiveResolution.of _)) Hzero (j + 1)

  have hEpi := by simpa using ShortComplex.Exact.epi_f h0 (IsZero.eq_zero_of_tgt
    (IsZero.of_iso zero' this.symm) _)
  simp only [ComplexShape.up_Rel, ShortComplex.map_X₁, flip_obj_obj, curriedTensor_obj_obj,
    ShortComplex.map_X₂, ShortComplex.map_X₃, ShortComplex.map_g] at h0'
  specialize h0' j (j + 1) rfl
  have zero'' := by simpa [← h] using (h3 i).obj M
  have e := by simpa using InjectiveResolution.isoRightDerivedObj (myX2 (shortExact_upCat C E F
    RGSES h1 M) (InjectiveResolution.of _) (InjectiveResolution.of _)) Hzero j
  have := by simpa using ShortComplex.Exact.mono_g h0' (IsZero.eq_zero_of_src
    (IsZero.of_iso zero'' e.symm) _)
  have := @CategoryTheory.isIso_of_mono_of_epi _ _ _ _ _ _ this hEpi
  simp only [ShortComplex.map_X₁, flip_obj_obj, curriedTensor_obj_obj, ShortComplex.map_X₂,
    ShortComplex.map_X₃, ← h]
  exact @asIso _ _ _ _ _ this


-- write one instance for enough injectives for Rep passing equivalence to R[G]-Mod


-- variable (R G : Type u) [CommRing R] [Group G] in
-- #synth CategoryTheory.EnoughInjectives (ModuleCat R)
