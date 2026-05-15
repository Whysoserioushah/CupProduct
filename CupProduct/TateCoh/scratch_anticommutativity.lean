import CupProduct.TateCoh.degree0
open CategoryTheory groupCohomology groupCohomology.TateCohomology Limits
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
    have hd_gτ₃' : (d ≫ kernel.ι φ ≫ S.X₂.g) ≫ S.g.τ₃ = 0 := by
      have : kernel.ι φ ≫ S.X₂.g ≫ S.g.τ₃ = 0 := kernel.condition φ
      rw [show (d ≫ kernel.ι φ ≫ S.X₂.g) ≫ S.g.τ₃ = d ≫ kernel.ι φ ≫ S.X₂.g ≫ S.g.τ₃ by
        simp [Category.assoc], this, Limits.comp_zero]
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
    rw [lhs_eq, hb''_eq, ← rhs_eq]
    simp [Category.assoc]
  -- (1b) SA'.Exact: exactness at the middle term.
  have exact_SA' : SA'.Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A x hx
    -- x : A ⟶ S.X₁.X₂ ⨿ S.X₂.X₁ with x ≫ j = 0.
    -- Split via biproduct: a := x ≫ coprod.desc (𝟙 _) 0 : A ⟶ S.X₁.X₂
    --                      b' := x ≫ coprod.desc 0 (𝟙 _) : A ⟶ S.X₂.X₁
    let a : A ⟶ S.X₁.X₂ := x ≫ coprod.desc (𝟙 _) 0
    let b' : A ⟶ S.X₂.X₁ := x ≫ coprod.desc 0 (𝟙 _)
    -- We have x = a ≫ coprod.inl + b' ≫ coprod.inr (preadditive coprod = biprod).
    -- Decomposition: any morphism into a coproduct (= biproduct in additive)
    -- decomposes via projections.
    have hx_decomp : x = a ≫ coprod.inl + b' ≫ coprod.inr := by
      have hid :
          coprod.desc (𝟙 _) 0 ≫ (coprod.inl : S.X₁.X₂ ⟶ S.X₁.X₂ ⨿ S.X₂.X₁) +
          coprod.desc 0 (𝟙 _) ≫ (coprod.inr : S.X₂.X₁ ⟶ S.X₁.X₂ ⨿ S.X₂.X₁)
            = 𝟙 (S.X₁.X₂ ⨿ S.X₂.X₁) := by
        apply coprod.hom_ext
        · rw [Preadditive.comp_add, Category.comp_id]
          rw [← Category.assoc, coprod.inl_desc, ← Category.assoc, coprod.inl_desc]
          rw [Category.id_comp, Limits.zero_comp, add_zero]
        · rw [Preadditive.comp_add, Category.comp_id]
          rw [← Category.assoc, coprod.inr_desc, ← Category.assoc, coprod.inr_desc]
          rw [Limits.zero_comp, Category.id_comp, zero_add]
      have hxid : x = x ≫ 𝟙 _ := by rw [Category.comp_id]
      rw [hxid, ← hid, Preadditive.comp_add]
      simp [a, b', Category.assoc]
    -- From hx : x ≫ j = 0, computing x ≫ j ≫ kernel.ι φ via hj₁/hj₂:
    have hjx : a ≫ S.f.τ₂ - b' ≫ S.X₂.f = 0 := by
      have : x ≫ j ≫ kernel.ι φ = 0 := by rw [← Category.assoc, hx, Limits.zero_comp]
      rw [hx_decomp] at this
      simp only [Preadditive.add_comp, Category.assoc] at this
      rw [hj₁, hj₂, Preadditive.comp_neg, ← sub_eq_add_neg] at this
      exact this
    -- Then S.f.τ₂ ≫ S.X₂.g = S.X₁.g ≫ S.f.τ₃, so a ≫ S.X₁.g ≫ S.f.τ₃ = b' ≫ S.X₂.f ≫ S.X₂.g = 0.
    have ha_g_τ₃ : (a ≫ S.X₁.g) ≫ S.f.τ₃ = 0 := by
      have e1 : a ≫ S.X₁.g ≫ S.f.τ₃ = a ≫ S.f.τ₂ ≫ S.X₂.g := by
        rw [← S.f.comm₂₃]
      have hX₂zero : S.X₂.f ≫ S.X₂.g = 0 := S.X₂.zero
      have e2 : b' ≫ S.X₂.f ≫ S.X₂.g = 0 := by
        rw [hX₂zero, Limits.comp_zero]
      have h1 : a ≫ S.f.τ₂ = b' ≫ S.X₂.f := by linear_combination (norm := abel) hjx
      rw [Category.assoc, e1, ← Category.assoc, h1, Category.assoc, e2]
    have ha_g : a ≫ S.X₁.g = 0 := by
      rw [← cancel_mono S.f.τ₃, Limits.zero_comp]
      exact ha_g_τ₃
    -- Use exactness of row 1 (S.X₁): a factors through S.X₁.f.
    obtain ⟨A', π, hπ, a', ha'⟩ := exact_row1.exact_up_to_refinements a ha_g
    -- ha' : π ≫ a = a' ≫ S.X₁.f
    -- We want: π ≫ x = a' ≫ i.
    -- i = S.X₁.f ≫ coprod.inl + S.f.τ₁ ≫ coprod.inr
    -- So a' ≫ i = a' ≫ S.X₁.f ≫ coprod.inl + a' ≫ S.f.τ₁ ≫ coprod.inr
    --           = π ≫ a ≫ coprod.inl + a' ≫ S.f.τ₁ ≫ coprod.inr
    -- We need: π ≫ a ≫ coprod.inl + a' ≫ S.f.τ₁ ≫ coprod.inr
    --        = π ≫ (a ≫ coprod.inl + b' ≫ coprod.inr)
    --        = π ≫ a ≫ coprod.inl + π ≫ b' ≫ coprod.inr
    -- So we need: a' ≫ S.f.τ₁ = π ≫ b'. To prove this, use S.X₂.f mono and
    --   (a' ≫ S.f.τ₁) ≫ S.X₂.f = a' ≫ S.X₁.f ≫ S.f.τ₂ = π ≫ a ≫ S.f.τ₂ = π ≫ b' ≫ S.X₂.f
    have h_f_τ₁_X₂f : S.f.τ₁ ≫ S.X₂.f = S.X₁.f ≫ S.f.τ₂ := S.f.comm₁₂
    have ha'_f_τ₁ : a' ≫ S.f.τ₁ = π ≫ b' := by
      rw [← cancel_mono S.X₂.f]
      have e1 : (a' ≫ S.f.τ₁) ≫ S.X₂.f = π ≫ a ≫ S.f.τ₂ := by
        rw [Category.assoc, h_f_τ₁_X₂f, ← Category.assoc, ← ha', Category.assoc]
      have h1 : a ≫ S.f.τ₂ = b' ≫ S.X₂.f := by linear_combination (norm := abel) hjx
      rw [e1, h1, ← Category.assoc]
    refine ⟨A', π, hπ, a', ?_⟩
    -- π ≫ x = a' ≫ i
    show π ≫ x = a' ≫ i
    have h_i : a' ≫ i = a' ≫ S.X₁.f ≫ coprod.inl + a' ≫ S.f.τ₁ ≫ coprod.inr := by
      show a' ≫ (S.X₁.f ≫ coprod.inl + S.f.τ₁ ≫ coprod.inr) =
        a' ≫ S.X₁.f ≫ coprod.inl + a' ≫ S.f.τ₁ ≫ coprod.inr
      rw [Preadditive.comp_add]
    rw [h_i, hx_decomp, Preadditive.comp_add]
    congr 1
    · rw [show a' ≫ S.X₁.f ≫ coprod.inl = (a' ≫ S.X₁.f) ≫ coprod.inl by
            rw [Category.assoc]]
      rw [← ha']
      simp [Category.assoc]
    · rw [show a' ≫ S.f.τ₁ ≫ coprod.inr = (a' ≫ S.f.τ₁) ≫ coprod.inr by
            rw [Category.assoc]]
      rw [ha'_f_τ₁]
      simp [Category.assoc]
  -- (1c) Assemble the short exact sequence.
  have hSA' : SA'.ShortExact :=
    { exact := exact_SA', mono_f := mono_i, epi_g := epi_j }
  -- (2)  Build the four short complex morphisms.
  -- `ses₃ hS'`  is the third column of S  (with  f = S.X₃.f, g = S.X₃.g).
  -- `ses₁ (ttses hS)` is the first row of S (with f = S.f.τ₁, g = S.g.τ₁) — wait it's
  -- the row.  Note `ses₁` and `ses₃` are applied to `S.transpose.ShortExact`.
  -- So `ses₃ hS'` uses `hS' : S.transpose.ShortExact` to give SE of `S.X₃`,
  --     `ses₃ (ttses hS)` uses `S.transpose.transpose.ShortExact` to give SE
  --       of `S.transpose.X₃`.
  -- F_col3 : SD ⟶ S.X₃ with τ₂ = S.g.τ₂, τ₃ = 𝟙, τ₁ lifts kernel.ι φ ≫ S.g.τ₂ via S.X₃.f.
  have exact_S_X₃ : S.X₃.Exact := (ses₃ hS').exact
  have mono_S_X₃f : Mono S.X₃.f := (ses₃ hS').mono_f
  have hFcol_lift_zero : (kernel.ι φ ≫ S.g.τ₂) ≫ S.X₃.g = 0 := by
    have hcom : S.g.τ₂ ≫ S.X₃.g = S.X₂.g ≫ S.g.τ₃ := S.g.comm₂₃
    rw [Category.assoc, hcom]
    show kernel.ι φ ≫ φ = 0
    exact kernel.condition φ
  let Fcol_τ₁ : D ⟶ S.X₃.X₁ := exact_S_X₃.lift (kernel.ι φ ≫ S.g.τ₂) hFcol_lift_zero
  have hFcol_τ₁ : Fcol_τ₁ ≫ S.X₃.f = kernel.ι φ ≫ S.g.τ₂ := exact_S_X₃.lift_f _ _
  let Fcol : SD ⟶ S.X₃ := {
    τ₁ := Fcol_τ₁
    τ₂ := S.g.τ₂
    τ₃ := 𝟙 _
    comm₁₂ := by
      show Fcol_τ₁ ≫ S.X₃.f = kernel.ι φ ≫ S.g.τ₂
      exact hFcol_τ₁
    comm₂₃ := by
      show S.g.τ₂ ≫ S.X₃.g = φ ≫ 𝟙 _
      rw [Category.comp_id]
      exact S.g.comm₂₃
  }
  -- F_row3 : SD ⟶ S.transpose.X₃ with τ₂ = S.X₂.g, τ₃ = 𝟙, τ₁ lifts
  -- kernel.ι φ ≫ S.X₂.g via S.f.τ₃.
  have exact_S_t_X₃ : S.transpose.X₃.Exact := (ses₃ (ttses hS)).exact
  have mono_S_t_X₃f : Mono S.transpose.X₃.f := (ses₃ (ttses hS)).mono_f
  have hFrow_lift_zero : (kernel.ι φ ≫ S.X₂.g) ≫ S.g.τ₃ = 0 := by
    rw [Category.assoc]
    show kernel.ι φ ≫ φ = 0
    exact kernel.condition φ
  let Frow_τ₁ : D ⟶ S.X₁.X₃ :=
    exact_S_t_X₃.lift (kernel.ι φ ≫ S.X₂.g) hFrow_lift_zero
  have hFrow_τ₁ : Frow_τ₁ ≫ S.f.τ₃ = kernel.ι φ ≫ S.X₂.g :=
    exact_S_t_X₃.lift_f _ _
  let Frow : SD ⟶ S.transpose.X₃ := {
    τ₁ := Frow_τ₁
    τ₂ := S.X₂.g
    τ₃ := 𝟙 _
    comm₁₂ := by
      show Frow_τ₁ ≫ S.f.τ₃ = kernel.ι φ ≫ S.X₂.g
      exact hFrow_τ₁
    comm₂₃ := by
      show S.X₂.g ≫ S.g.τ₃ = φ ≫ 𝟙 _
      rw [Category.comp_id]
  }
  -- G_col1 : SA' ⟶ S.X₁  (first column of S).
  -- τ₁ = 𝟙, τ₂ = coprod.desc 𝟙 0, τ₃ = Frow_τ₁.
  let Gcol : SA' ⟶ S.X₁ := {
    τ₁ := 𝟙 _
    τ₂ := coprod.desc (𝟙 _) 0
    τ₃ := Frow_τ₁
    comm₁₂ := by
      show 𝟙 _ ≫ S.X₁.f = i ≫ coprod.desc (𝟙 _) 0
      rw [Category.id_comp]
      show S.X₁.f = (S.X₁.f ≫ coprod.inl + S.f.τ₁ ≫ coprod.inr) ≫ coprod.desc (𝟙 _) 0
      rw [Preadditive.add_comp, Category.assoc, Category.assoc, coprod.inl_desc,
        coprod.inr_desc, Category.comp_id, Limits.comp_zero, add_zero]
    comm₂₃ := by
      show coprod.desc (𝟙 _) (0 : S.X₂.X₁ ⟶ S.X₁.X₂) ≫ S.X₁.g = j ≫ Frow_τ₁
      apply (cancel_mono S.f.τ₃).1
      rw [Category.assoc, Category.assoc, hFrow_τ₁]
      apply coprod.hom_ext
      · -- coprod.inl side
        have e1 : coprod.inl ≫ coprod.desc (𝟙 _) (0 : S.X₂.X₁ ⟶ S.X₁.X₂)
              ≫ S.X₁.g ≫ S.f.τ₃ = S.X₁.g ≫ S.f.τ₃ := by
          rw [← Category.assoc, coprod.inl_desc, Category.id_comp]
        have e2 : coprod.inl ≫ j ≫ kernel.ι φ ≫ S.X₂.g
            = S.f.τ₂ ≫ S.X₂.g := by
          rw [show coprod.inl ≫ j ≫ kernel.ι φ ≫ S.X₂.g =
            (coprod.inl ≫ j ≫ kernel.ι φ) ≫ S.X₂.g from by simp [Category.assoc]]
          rw [hj₁]
        rw [e1, e2]
        exact S.f.comm₂₃.symm
      · -- coprod.inr side
        have e1 : coprod.inr ≫ coprod.desc (𝟙 _) (0 : S.X₂.X₁ ⟶ S.X₁.X₂)
              ≫ S.X₁.g ≫ S.f.τ₃ = 0 := by
          rw [← Category.assoc, coprod.inr_desc, Limits.zero_comp]
        have e2 : coprod.inr ≫ j ≫ kernel.ι φ ≫ S.X₂.g = 0 := by
          rw [show coprod.inr ≫ j ≫ kernel.ι φ ≫ S.X₂.g =
            (coprod.inr ≫ j ≫ kernel.ι φ) ≫ S.X₂.g from by simp [Category.assoc]]
          rw [hj₂, Preadditive.neg_comp]
          have hX₂zero : S.X₂.f ≫ S.X₂.g = 0 := S.X₂.zero
          rw [hX₂zero, neg_zero]
        rw [e1, e2]
  }
  -- G_row1 : SA' ⟶ S.transpose.X₁  (first row of S).
  -- τ₁ = 𝟙, τ₂ = coprod.desc 0 𝟙, τ₃ = -Fcol_τ₁  (sign from -S.X₂.f in j).
  let Grow : SA' ⟶ S.transpose.X₁ := {
    τ₁ := 𝟙 _
    τ₂ := coprod.desc 0 (𝟙 _)
    τ₃ := -Fcol_τ₁
    comm₁₂ := by
      show (𝟙 _ : S.X₁.X₁ ⟶ _) ≫ S.f.τ₁ = i ≫ coprod.desc 0 (𝟙 _)
      rw [Category.id_comp]
      show S.f.τ₁ = (S.X₁.f ≫ coprod.inl + S.f.τ₁ ≫ coprod.inr) ≫ coprod.desc 0 (𝟙 _)
      rw [Preadditive.add_comp, Category.assoc, Category.assoc, coprod.inl_desc,
        coprod.inr_desc, Category.comp_id, Limits.comp_zero, zero_add]
    comm₂₃ := by
      show coprod.desc (0 : S.X₁.X₂ ⟶ S.X₂.X₁) (𝟙 _) ≫ S.g.τ₁ = j ≫ (-Fcol_τ₁)
      apply coprod.hom_ext
      · -- coprod.inl side: LHS = 0, want to show RHS = 0 (via mono S.X₃.f).
        have hfg : S.f.τ₂ ≫ S.g.τ₂ = 0 :=
          show (S.f ≫ S.g).τ₂ = 0 by rw [S.zero]; rfl
        have hjFcol_inl : (coprod.inl ≫ j ≫ (-Fcol_τ₁)) ≫ S.X₃.f = 0 := by
          have step1 : (coprod.inl ≫ j ≫ (-Fcol_τ₁)) ≫ S.X₃.f
              = -((coprod.inl ≫ j ≫ kernel.ι φ) ≫ S.g.τ₂) := by
            have h_neg : (-Fcol_τ₁) ≫ S.X₃.f = -(kernel.ι φ ≫ S.g.τ₂) := by
              rw [Preadditive.neg_comp, hFcol_τ₁]
            calc (coprod.inl ≫ j ≫ (-Fcol_τ₁)) ≫ S.X₃.f
                = coprod.inl ≫ j ≫ ((-Fcol_τ₁) ≫ S.X₃.f) := by simp [Category.assoc]
              _ = coprod.inl ≫ j ≫ (-(kernel.ι φ ≫ S.g.τ₂)) := by rw [h_neg]
              _ = -((coprod.inl ≫ j ≫ kernel.ι φ) ≫ S.g.τ₂) := by
                  simp [Preadditive.comp_neg, Category.assoc]
          rw [step1, hj₁, hfg, neg_zero]
        have key : coprod.inl ≫ j ≫ (-Fcol_τ₁) = 0 := by
          apply (cancel_mono S.X₃.f).1
          rw [Limits.zero_comp]; exact hjFcol_inl
        rw [← Category.assoc, coprod.inl_desc, Limits.zero_comp, key]
      · -- coprod.inr side: LHS = S.g.τ₁; want this = -(coprod.inr ≫ j ≫ Fcol_τ₁) via mono.
        rw [← Category.assoc, coprod.inr_desc, Category.id_comp]
        have hjFcol_inr : (coprod.inr ≫ j ≫ (-Fcol_τ₁)) ≫ S.X₃.f = S.g.τ₁ ≫ S.X₃.f := by
          have step1 : (coprod.inr ≫ j ≫ (-Fcol_τ₁)) ≫ S.X₃.f
              = -((coprod.inr ≫ j ≫ kernel.ι φ) ≫ S.g.τ₂) := by
            have h_neg : (-Fcol_τ₁) ≫ S.X₃.f = -(kernel.ι φ ≫ S.g.τ₂) := by
              rw [Preadditive.neg_comp, hFcol_τ₁]
            calc (coprod.inr ≫ j ≫ (-Fcol_τ₁)) ≫ S.X₃.f
                = coprod.inr ≫ j ≫ ((-Fcol_τ₁) ≫ S.X₃.f) := by simp [Category.assoc]
              _ = coprod.inr ≫ j ≫ (-(kernel.ι φ ≫ S.g.τ₂)) := by rw [h_neg]
              _ = -((coprod.inr ≫ j ≫ kernel.ι φ) ≫ S.g.τ₂) := by
                  simp [Preadditive.comp_neg, Category.assoc]
          rw [step1, hj₂, Preadditive.neg_comp, neg_neg]
          exact S.g.comm₁₂.symm
        have key : coprod.inr ≫ j ≫ (-Fcol_τ₁) = S.g.τ₁ := by
          apply (cancel_mono S.X₃.f).1
          exact hjFcol_inr
        exact key.symm
  }
  -- Step 8: assemble via δ_naturality.
  -- δ_naturality Fcol : δ hSD n ≫ map Fcol.τ₁ = map Fcol.τ₃ ≫ δ (ses₃ hS') n
  -- δ_naturality Frow : δ hSD n ≫ map Frow.τ₁ = map Frow.τ₃ ≫ δ (ses₃ (ttses hS)) n
  -- δ_naturality Gcol : δ hSA' (n+1) ≫ map Gcol.τ₁ = map Gcol.τ₃ ≫ δ (ses₁ hS') (n+1)
  -- δ_naturality Grow : δ hSA' (n+1) ≫ map Grow.τ₁ = map Grow.τ₃ ≫ δ (ses₁ (ttses hS)) (n+1)
  have hδFcol : δ hSD n ≫ (tateCohomology (n + 1)).map Fcol.τ₁
      = (tateCohomology n).map Fcol.τ₃ ≫ δ (ses₃ hS') n :=
    δ_naturality hSD (ses₃ hS') Fcol n
  have hδFrow : δ hSD n ≫ (tateCohomology (n + 1)).map Frow.τ₁
      = (tateCohomology n).map Frow.τ₃ ≫ δ (ses₃ (ttses hS)) n :=
    δ_naturality hSD (ses₃ (ttses hS)) Frow n
  have hδGcol : δ hSA' (n + 1) ≫ (tateCohomology (n + 1 + 1)).map Gcol.τ₁
      = (tateCohomology (n + 1)).map Gcol.τ₃ ≫ δ (ses₁ hS') (n + 1) :=
    δ_naturality hSA' (ses₁ hS') Gcol (n + 1)
  have hδGrow : δ hSA' (n + 1) ≫ (tateCohomology (n + 1 + 1)).map Grow.τ₁
      = (tateCohomology (n + 1)).map Grow.τ₃ ≫ δ (ses₁ (ttses hS)) (n + 1) :=
    δ_naturality hSA' (ses₁ (ttses hS)) Grow (n + 1)
  -- All of Gcol.τ₁, Frow.τ₃, Grow.τ₁, Fcol.τ₃ are 𝟙. Grow.τ₃ = -Fcol_τ₁.
  have hFcol_τ₃_id : (tateCohomology n).map Fcol.τ₃ = 𝟙 _ := Functor.map_id _ _
  have hFrow_τ₃_id : (tateCohomology n).map Frow.τ₃ = 𝟙 _ := Functor.map_id _ _
  have hGcol_τ₁_id : (tateCohomology (n + 1 + 1)).map Gcol.τ₁ = 𝟙 _ :=
    Functor.map_id _ _
  have hGrow_τ₁_id : (tateCohomology (n + 1 + 1)).map Grow.τ₁ = 𝟙 _ :=
    Functor.map_id _ _
  -- Grow.τ₃ = -Fcol_τ₁ = -Frow_τ₁? No, Grow.τ₃ = -Fcol_τ₁ (different from Frow_τ₁).
  -- Wait, Grow goes to row1 with row1.X₃ = S.X₃.X₁, and Fcol goes to col3 with col3.X₁ = S.X₃.X₁.
  -- So Grow.τ₃ : D → S.X₃.X₁ and Fcol.τ₁ : D → S.X₃.X₁, types match.
  have hGrow_τ₃_eq : (tateCohomology (n + 1)).map Grow.τ₃
      = -(tateCohomology (n + 1)).map Fcol.τ₁ := by
    show (tateCohomology (n + 1)).map (-Fcol_τ₁) = -(tateCohomology (n + 1)).map Fcol_τ₁
    exact Functor.map_neg _
  -- Plug hGcol_τ₁_id into hδGcol.
  have hδGcol' : δ hSA' (n + 1)
      = (tateCohomology (n + 1)).map Gcol.τ₃ ≫ δ (ses₁ hS') (n + 1) := by
    have := hδGcol
    rw [hGcol_τ₁_id, Category.comp_id] at this
    exact this
  -- Plug hGrow_τ₁_id into hδGrow.
  have hδGrow' : δ hSA' (n + 1)
      = (tateCohomology (n + 1)).map Grow.τ₃ ≫ δ (ses₁ (ttses hS)) (n + 1) := by
    have := hδGrow
    rw [hGrow_τ₁_id, Category.comp_id] at this
    exact this
  -- Plug hFcol_τ₃_id into hδFcol.
  have hδFcol' : δ hSD n ≫ (tateCohomology (n + 1)).map Fcol.τ₁ = δ (ses₃ hS') n := by
    rw [hδFcol, hFcol_τ₃_id, Category.id_comp]
  have hδFrow' : δ hSD n ≫ (tateCohomology (n + 1)).map Frow.τ₁
      = δ (ses₃ (ttses hS)) n := by
    rw [hδFrow, hFrow_τ₃_id, Category.id_comp]
  -- Note Gcol.τ₃ = Frow.τ₁, so map Gcol.τ₃ = map Frow.τ₁.
  -- So δ hSA' (n+1) = map Frow.τ₁ ≫ δ (ses₁ hS') (n+1)
  have hδGcol'' : δ hSA' (n + 1)
      = (tateCohomology (n + 1)).map Frow.τ₁ ≫ δ (ses₁ hS') (n + 1) := hδGcol'
  -- Note Grow.τ₃ = -Fcol_τ₁, so map Grow.τ₃ = -map Fcol.τ₁.
  -- So δ hSA' (n+1) = -map Fcol.τ₁ ≫ δ (ses₁ (ttses hS)) (n+1).
  have hδGrow'' : δ hSA' (n + 1)
      = -((tateCohomology (n + 1)).map Fcol.τ₁ ≫ δ (ses₁ (ttses hS)) (n + 1)) := by
    rw [hδGrow', hGrow_τ₃_eq, Preadditive.neg_comp]
  -- Now combine.  LHS = δ (ses₃ hS') n ≫ δ (ses₁ (ttses hS)) (n+1)
  --              = (δ hSD n ≫ map Fcol.τ₁) ≫ δ (ses₁ (ttses hS)) (n+1)
  --              = δ hSD n ≫ (map Fcol.τ₁ ≫ δ (ses₁ (ttses hS)) (n+1))
  --              = δ hSD n ≫ (-δ hSA' (n+1))      [from hδGrow'']
  --              = -(δ hSD n ≫ δ hSA' (n+1)).
  --       RHS = -δ (ses₃ (ttses hS)) n ≫ δ (ses₁ hS') (n+1)
  --           = -((δ hSD n ≫ map Frow.τ₁) ≫ δ (ses₁ hS') (n+1))
  --           = -(δ hSD n ≫ (map Frow.τ₁ ≫ δ (ses₁ hS') (n+1)))
  --           = -(δ hSD n ≫ δ hSA' (n+1))         [from hδGcol''].
  rw [← hδFcol', ← hδFrow', Category.assoc, Category.assoc]
  rw [show (tateCohomology (n + 1)).map Fcol.τ₁ ≫ δ (ses₁ (ttses hS)) (n + 1) =
    -δ hSA' (n + 1) by rw [hδGrow'']; rw [neg_neg]]
  rw [show (tateCohomology (n + 1)).map Frow.τ₁ ≫ δ (ses₁ hS') (n + 1) =
    δ hSA' (n + 1) from hδGcol''.symm]
  rw [Preadditive.comp_neg, Preadditive.neg_comp]
