import CupProduct.TateCoh.degree0
open CategoryTheory groupCohomology.TateCohomology Limits
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [Fintype G]


variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasFiniteLimits C] [HasFiniteColimits C]
  [HasImages C] [HasKernels C]

abbrev CategoryTheory.ShortComplex.transpose (S : ShortComplex <| ShortComplex C) :
    ShortComplex (ShortComplex C) where
      X₁ := {
        X₁ := S.X₁.X₁
        X₂ := S.X₂.X₁
        X₃ := S.X₃.X₁
        f := S.f.τ₁
        g := S.g.τ₁
        zero := congr(ShortComplex.Hom.τ₁ $S.zero)
      }
      X₂ := {
        X₁ := S.X₁.X₂
        X₂ := S.X₂.X₂
        X₃ := S.X₃.X₂
        f := S.f.τ₂
        g := S.g.τ₂
        zero := congr(ShortComplex.Hom.τ₂ $S.zero)
      }
      X₃ := {
        X₁ := S.X₁.X₃
        X₂ := S.X₂.X₃
        X₃ := S.X₃.X₃
        f := S.f.τ₃
        g := S.g.τ₃
        zero := congr(ShortComplex.Hom.τ₃ $S.zero)
      }
      f := {
        τ₁ := S.X₁.f
        τ₂ := S.X₂.f
        τ₃ := S.X₃.f
        comm₁₂ := S.f.comm₁₂.symm
        comm₂₃ := S.g.comm₁₂.symm
      }
      g := {
        τ₁ := S.X₁.g
        τ₂ := S.X₂.g
        τ₃ := S.X₃.g
        comm₁₂ := S.f.comm₂₃.symm
        comm₂₃ := S.g.comm₂₃.symm
      }
      zero := by ext1 <;> simp



lemma ses₁ {S : ShortComplex <| ShortComplex C} (hS : S.transpose.ShortExact) :
    S.X₁.ShortExact :=
  have := hS.2
  have := hS.3
  hS.map ShortComplex.π₁

lemma ses₂ {S : ShortComplex <| ShortComplex C} (hS : S.transpose.ShortExact) :
    S.X₂.ShortExact :=
  have := hS.2
  have := hS.3
  hS.map ShortComplex.π₂

lemma ses₃ {S : ShortComplex <| ShortComplex C} (hS : S.transpose.ShortExact) :
    S.X₃.ShortExact :=
  have := hS.2
  have := hS.3
  hS.map ShortComplex.π₃

abbrev transposeTranspose (S : ShortComplex (ShortComplex C)) : S ≅ S.transpose.transpose := Iso.refl _

lemma ttses {S : ShortComplex (ShortComplex C)} (hS : S.ShortExact) : S.transpose.transpose.ShortExact := by
  simpa

lemma anticommutativity (S : ShortComplex <| ShortComplex (Rep R G)) (hS : S.ShortExact)
    (hS' : S.transpose.ShortExact) (n : ℤ) :
    δ (ses₃ hS') n ≫ δ (ses₁ (ttses hS)) (n + 1) = - δ (ses₃ (ttses hS)) n ≫ δ (ses₁ hS') (n + 1)
    := by
  have _ := hS.2
  have _ := hS.3
  have _ := hS'.2
  have _ := hS'.3
  let φ : S.X₂.X₂ ⟶ S.X₃.X₃ := S.X₂.g ≫ S.g.τ₃
  let D := kernel φ
  let SD : ShortComplex (Rep.{u} R G) := {
    X₁ := D
    X₂ := S.X₂.X₂
    X₃ := S.X₃.X₃
    f := kernel.ι φ
    g := φ
    zero := kernel.condition φ
  }
  have hSD : SD.ShortExact := {
    exact := by exact ShortComplex.exact_kernel φ
    mono_f := by exact equalizer.ι_mono
    epi_g := @epi_comp _ _ _ _ _ _ (ses₂ hS').3 _ (ses₃ (ttses hS)).3
  }
  let i : S.X₁.X₁ ⟶ S.X₁.X₂ ⨿ S.X₂.X₁ := S.X₁.f ≫ coprod.inl + S.f.τ₁ ≫ coprod.inr
  let j : S.X₁.X₂ ⨿ S.X₂.X₁ ⟶ D := coprod.desc (kernel.lift _ S.f.τ₂ (by
      change S.f.τ₂ ≫ S.X₂.g ≫ S.g.τ₃ = 0
      rw [← Category.assoc, S.f.comm₂₃, Category.assoc]
      rw [show S.f.τ₃ ≫ S.g.τ₃ = (S.f ≫ S.g).τ₃ from rfl, S.zero]
      simp))
    (kernel.lift _ (- S.X₂.f) (by
      change (-S.X₂.f) ≫ S.X₂.g ≫ S.g.τ₃ = 0
      rw [Preadditive.neg_comp, ← Category.assoc, S.X₂.zero, Limits.zero_comp, neg_zero]))
  have hj₁ : coprod.inl ≫ j ≫ kernel.ι φ = S.f.τ₂ := by
    rw [← Category.assoc, coprod.inl_desc, kernel.lift_ι]
  have hj₂ : coprod.inr ≫ j ≫ kernel.ι φ = -S.X₂.f := by
    rw [← Category.assoc, coprod.inr_desc, kernel.lift_ι]
  have hij : i ≫ j = 0 := by
    apply (cancel_mono (kernel.ι φ)).1
    change ((S.X₁.f ≫ coprod.inl + S.f.τ₁ ≫ coprod.inr) ≫ j) ≫ kernel.ι φ = 0 ≫ kernel.ι φ
    simp only [Preadditive.add_comp, Limits.zero_comp, Category.assoc, hj₁, hj₂]
    rw [Preadditive.comp_neg, ← S.f.comm₁₂]
    abel
  let SA' : ShortComplex (Rep.{u} R G) := {
    X₁ := S.X₁.X₁
    X₂ := S.X₁.X₂ ⨿ S.X₂.X₁
    X₃ := D
    f := i
    g := j
    zero := hij
  }
  have mono_X₁f : Mono S.X₁.f := (ses₁ hS').mono_f
  have mono_i : Mono i := by
    have hfac : i ≫ coprod.desc (𝟙 _) 0 = S.X₁.f := by
      change (S.X₁.f ≫ coprod.inl + S.f.τ₁ ≫ coprod.inr) ≫ coprod.desc (𝟙 _) 0 = _
      rw [Preadditive.add_comp, Category.assoc, Category.assoc, coprod.inl_desc,
        coprod.inr_desc, Category.comp_id, Limits.comp_zero, add_zero]
    exact mono_of_mono_fac hfac
  -- Outline of the remainder of the proof.
  --
  -- Two further hard pieces remain.  We isolate them as anonymous `have` blocks
  -- with `sorry` so that the structural skeleton typechecks.
  --
  -- (1)  `hSA' : SA'.ShortExact`.  This is the "3 × 3" lemma:
  --      given the 3 × 3 commutative diagram with exact rows and columns,
  --      the auxiliary sequence
  --         `0 ⟶ A' ⟶ A ⊕ B' ⟶ D ⟶ 0`
  --      is short exact.  Mono of `i` was proved above (`mono_i`).  The
  --      remaining pieces are `Epi j` and `SA'.Exact`; both are standard
  --      diagram chases using the exact rows (`ses_i hS'`) and columns
  --      (`ses_j (ttses hS)`).
  --
  -- (2)  Build two morphisms of short exact sequences
  --        F₁ : SA' ⟶ S.transpose.X₁  -- the first column   `A' → B' → C'`
  --        F₃ : SA' ⟶ S.X₁            -- the first row      `A' → A  → A''`
  --      together with a morphism `G : SD ⟶ S.X₃` of `S.X₃` (third row).
  --      Using `δ_naturality` (proved in
  --      `CupProduct/TateCoh/degree0.lean`) for each of these and the
  --      construction of `SD` and `SA'` we factor
  --        `δ (ses₃ hS') n ≫ δ (ses₁ (ttses hS)) (n+1)`
  --      and
  --        `δ (ses₃ (ttses hS)) n ≫ δ (ses₁ hS') (n+1)`
  --      both through `δ hSD n ≫ δ hSA' (n+1)`, with a difference of sign
  --      coming from the `-S.X₂.f` choice in the second summand of `j`.
  --
  -- We isolate each remaining piece as a `have` with its own `sorry`,
  -- so the overall scaffold becomes easier to attack incrementally.
  -- (1a) Epi j: surjectivity onto D.
  have epi_X₂g : Epi S.X₂.g := (ses₂ hS').epi_g
  have epi_X₁g : Epi S.X₁.g := (ses₁ hS').epi_g
  have epi_gτ₃ : Epi S.g.τ₃ := (ses₃ (ttses hS)).epi_g
  have mono_fτ₃ : Mono S.f.τ₃ := (ses₃ (ttses hS)).mono_f
  have mono_X₂f : Mono S.X₂.f := (ses₂ hS').mono_f
  have exact_col2 : (ShortComplex.mk S.X₂.f S.X₂.g S.X₂.zero).Exact := (ses₂ hS').exact
  have exact_col3 : (ShortComplex.mk S.f.τ₃ S.g.τ₃
      (show S.f.τ₃ ≫ S.g.τ₃ = 0 from congr(ShortComplex.Hom.τ₃ $S.zero))).Exact :=
    (ses₃ (ttses hS)).exact
  have exact_row1 : (ShortComplex.mk S.X₁.f S.X₁.g S.X₁.zero).Exact := (ses₁ hS').exact
  have epi_j : Epi j := by
    rw [epi_iff_surjective_up_to_refinements]
    intro A d
    -- Step 1: b := d ≫ kernel.ι φ : A ⟶ S.X₂.X₂.
    -- We don't materialize b; instead carry d through.
    have hd_gτ₃ : (d ≫ kernel.ι φ) ≫ S.X₂.g ≫ S.g.τ₃ = 0 := by
      rw [show S.X₂.g ≫ S.g.τ₃ = φ from rfl, ← Category.assoc, ← Category.assoc,
        kernel.condition, Limits.zero_comp]
    have hd_gτ₃' : (d ≫ kernel.ι φ ≫ S.X₂.g) ≫ S.g.τ₃ = 0 := by
      simpa [Category.assoc] using hd_gτ₃
    -- Step 2: b ≫ S.X₂.g goes through ker S.g.τ₃ = im S.f.τ₃.
    obtain ⟨A₁, π₁, hπ₁, a'', ha''⟩ :=
      exact_col3.exact_up_to_refinements (d ≫ kernel.ι φ ≫ S.X₂.g) hd_gτ₃'
    -- ha'' : π₁ ≫ (d ≫ kernel.ι φ ≫ S.X₂.g) = a'' ≫ S.f.τ₃
    -- Step 3: lift a'' via epi S.X₁.g.
    obtain ⟨A₂, π₂, hπ₂, a, ha⟩ :=
      surjective_up_to_refinements_of_epi S.X₁.g a''
    -- ha : π₂ ≫ a'' = a ≫ S.X₁.g
    -- Step 4: b' := π₂ ≫ π₁ ≫ d ≫ kernel.ι φ - a ≫ S.f.τ₂ has b' ≫ S.X₂.g = 0.
    have hf₂₃ : S.f.τ₂ ≫ S.X₂.g = S.X₁.g ≫ S.f.τ₃ := S.f.comm₂₃
    have hb'_g :
        (π₂ ≫ π₁ ≫ d ≫ kernel.ι φ - a ≫ S.f.τ₂) ≫ S.X₂.g = 0 := by
      rw [Preadditive.sub_comp]
      have e1 : (π₂ ≫ π₁ ≫ d ≫ kernel.ι φ) ≫ S.X₂.g
          = π₂ ≫ a'' ≫ S.f.τ₃ := by
        calc (π₂ ≫ π₁ ≫ d ≫ kernel.ι φ) ≫ S.X₂.g
            = π₂ ≫ π₁ ≫ d ≫ kernel.ι φ ≫ S.X₂.g := by simp [Category.assoc]
          _ = π₂ ≫ a'' ≫ S.f.τ₃ := by rw [ha'']
      have e2 : (a ≫ S.f.τ₂) ≫ S.X₂.g = π₂ ≫ a'' ≫ S.f.τ₃ := by
        rw [Category.assoc, hf₂₃, ← Category.assoc a, ← ha, Category.assoc]
      rw [e1, e2, sub_self]
    -- Step 5: factor (π₂ ≫ π₁ ≫ d ≫ kernel.ι φ - a ≫ S.f.τ₂) through im S.X₂.f.
    obtain ⟨A₃, π₃, hπ₃, b'', hb''⟩ :=
      exact_col2.exact_up_to_refinements
        (π₂ ≫ π₁ ≫ d ≫ kernel.ι φ - a ≫ S.f.τ₂) hb'_g
    -- hb'' : π₃ ≫ (π₂ ≫ π₁ ≫ d ≫ kernel.ι φ - a ≫ S.f.τ₂) = b'' ≫ S.X₂.f
    -- Step 6: preimage = j of (π₃ ≫ a, -b'').
    refine ⟨A₃, π₃ ≫ π₂ ≫ π₁, epi_comp _ _,
        (π₃ ≫ a) ≫ (coprod.inl : S.X₁.X₂ ⟶ S.X₁.X₂ ⨿ S.X₂.X₁) -
          b'' ≫ (coprod.inr : S.X₂.X₁ ⟶ S.X₁.X₂ ⨿ S.X₂.X₁), ?_⟩
    apply (cancel_mono (kernel.ι φ)).1
    -- Goal: (π₃ ≫ π₂ ≫ π₁) ≫ d ≫ kernel.ι φ
    --     = ((π₃ ≫ a) ≫ coprod.inl - b'' ≫ coprod.inr) ≫ j ≫ kernel.ι φ
    have rhs_eq :
        ((π₃ ≫ a) ≫ (coprod.inl : S.X₁.X₂ ⟶ S.X₁.X₂ ⨿ S.X₂.X₁) -
          b'' ≫ (coprod.inr : S.X₂.X₁ ⟶ S.X₁.X₂ ⨿ S.X₂.X₁)) ≫ j ≫ kernel.ι φ
          = (π₃ ≫ a) ≫ S.f.τ₂ + b'' ≫ S.X₂.f := by
      have e1 : ((π₃ ≫ a) ≫ (coprod.inl : S.X₁.X₂ ⟶ S.X₁.X₂ ⨿ S.X₂.X₁))
                ≫ j ≫ kernel.ι φ = (π₃ ≫ a) ≫ S.f.τ₂ := by
        rw [Category.assoc, hj₁]
      have e2 : (b'' ≫ (coprod.inr : S.X₂.X₁ ⟶ S.X₁.X₂ ⨿ S.X₂.X₁))
                ≫ j ≫ kernel.ι φ = -(b'' ≫ S.X₂.f) := by
        rw [Category.assoc, hj₂, Preadditive.comp_neg]
      rw [Preadditive.sub_comp, e1, e2, sub_neg_eq_add]
    -- hb''_eq : π₃ ≫ π₂ ≫ π₁ ≫ d ≫ kernel.ι φ = (π₃ ≫ a) ≫ S.f.τ₂ + b'' ≫ S.X₂.f
    have hb''_eq : π₃ ≫ π₂ ≫ π₁ ≫ d ≫ kernel.ι φ
        = (π₃ ≫ a) ≫ S.f.τ₂ + b'' ≫ S.X₂.f := by
      have h1 : π₃ ≫ (π₂ ≫ π₁ ≫ d ≫ kernel.ι φ - a ≫ S.f.τ₂) = b'' ≫ S.X₂.f := hb''
      rw [Preadditive.comp_sub] at h1
      -- h1 : π₃ ≫ π₂ ≫ π₁ ≫ d ≫ kernel.ι φ - π₃ ≫ a ≫ S.f.τ₂ = b'' ≫ S.X₂.f
      have h2 : π₃ ≫ π₂ ≫ π₁ ≫ d ≫ kernel.ι φ
          = π₃ ≫ a ≫ S.f.τ₂ + b'' ≫ S.X₂.f := by
        linear_combination (norm := abel) h1
      rw [h2, Category.assoc]
    have lhs_eq : ((π₃ ≫ π₂ ≫ π₁) ≫ d) ≫ kernel.ι φ
        = π₃ ≫ π₂ ≫ π₁ ≫ d ≫ kernel.ι φ := by simp [Category.assoc]
    rw [lhs_eq, hb''_eq, ← rhs_eq, Category.assoc]
  -- (1b) SA'.Exact: exactness at the middle term.
  have exact_SA' : SA'.Exact := by sorry
  -- (1c) Assemble the short exact sequence.
  have hSA' : SA'.ShortExact :=
    { exact := exact_SA', mono_f := mono_i, epi_g := epi_j }
  -- Step (2) and the final assembly remain as one bundled `sorry`.
  sorry
