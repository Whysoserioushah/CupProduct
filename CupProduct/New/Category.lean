import Mathlib

open CategoryTheory MonoidalCategory Limits Functor

variable (C D E : Type*) [Category C] [Category D] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [BraidedCategory C] [EnoughInjectives C] [Abelian D] [MonoidalCategory D] [BraidedCategory D]
  [Category E] [Abelian E] [MonoidalCategory E] [MonoidalPreadditive E] [BraidedCategory E]
  -- F is the forgetful functor
  (F : C ⥤ E) [F.Faithful] [PreservesLimits F] [PreservesColimits F] [hF : F.Monoidal]
  (Hzero : C ⥤ D) [Hzero.Additive] [Hzero.LaxBraided] [PreservesLimits Hzero]
  (RGSES : ShortComplex C) (h1 : (RGSES.map F).Splitting) (h2 : RGSES.X₁ = 𝟙_ C)

abbrev coindCat : C ⥤ C := tensorLeft RGSES.X₂

abbrev upCat : C ⥤ C := tensorLeft RGSES.X₃

def μNatIso (M : C) : tensorRight M ⋙ F ≅ F ⋙ tensorRight (F.obj M) :=
  NatIso.ofComponents (fun X ↦ hF.μIso _ X _|>.symm)

#check ShortComplex.map_comp
def Isoμ_shortComplex (M : C) : (RGSES.map (tensorRight M) |>.map F) ≅
    (RGSES.map F).map (tensorRight <|F.obj M) := by
  rw [← ShortComplex.map_comp, ← ShortComplex.map_comp]
  exact ShortComplex.mapNatIso _ <| μNatIso _ _ _ _
  -- eqToIso _ ≪≫ ShortComplex.mapNatIso (RGSES.map (tensorRight M ⋙ F)) _ ≪≫
  --   eqToIso (ShortComplex.map_comp RGSES (tensorRight M) F)

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


-- write one instance for enough injectives for Rep passing equivalence to R[G]-Mod


-- variable (R G : Type u) [CommRing R] [Group G] in
-- #synth CategoryTheory.EnoughInjectives (ModuleCat R)
