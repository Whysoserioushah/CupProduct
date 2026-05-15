import CupProduct.TateCoh.degree0
open CategoryTheory groupCohomology groupCohomology.TateCohomology Limits
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [Fintype G]


variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasFiniteLimits C] [HasFiniteColimits C]
  [HasImages C] [HasKernels C]

/-- Transpose a short complex of short complexes by swapping rows and columns. -/
abbrev CategoryTheory.ShortComplex.transpose (S : ShortComplex <| ShortComplex C) :
    ShortComplex (ShortComplex C) where
  X₁ :=
    { X₁ := S.X₁.X₁, X₂ := S.X₂.X₁, X₃ := S.X₃.X₁, f := S.f.τ₁, g := S.g.τ₁
      zero := congr(ShortComplex.Hom.τ₁ $S.zero) }
  X₂ :=
    { X₁ := S.X₁.X₂, X₂ := S.X₂.X₂, X₃ := S.X₃.X₂, f := S.f.τ₂, g := S.g.τ₂
      zero := congr(ShortComplex.Hom.τ₂ $S.zero) }
  X₃ :=
    { X₁ := S.X₁.X₃, X₂ := S.X₂.X₃, X₃ := S.X₃.X₃, f := S.f.τ₃, g := S.g.τ₃
      zero := congr(ShortComplex.Hom.τ₃ $S.zero) }
  f := { τ₁ := S.X₁.f, τ₂ := S.X₂.f, τ₃ := S.X₃.f
         comm₁₂ := S.f.comm₁₂.symm, comm₂₃ := S.g.comm₁₂.symm }
  g := { τ₁ := S.X₁.g, τ₂ := S.X₂.g, τ₃ := S.X₃.g
         comm₁₂ := S.f.comm₂₃.symm, comm₂₃ := S.g.comm₂₃.symm }
  zero := by ext1 <;> simp

omit [HasImages C] [HasKernels C] in
/-- Row 1 of a bicomplex with short-exact transpose is short-exact. -/
lemma ses₁ {S : ShortComplex <| ShortComplex C} (hS : S.transpose.ShortExact) :
    S.X₁.ShortExact :=
  have := hS.2; have := hS.3; hS.map ShortComplex.π₁

omit [HasImages C] [HasKernels C] in
/-- Row 2 of a bicomplex with short-exact transpose is short-exact. -/
lemma ses₂ {S : ShortComplex <| ShortComplex C} (hS : S.transpose.ShortExact) :
    S.X₂.ShortExact :=
  have := hS.2; have := hS.3; hS.map ShortComplex.π₂

omit [HasImages C] [HasKernels C] in
/-- Row 3 of a bicomplex with short-exact transpose is short-exact. -/
lemma ses₃ {S : ShortComplex <| ShortComplex C} (hS : S.transpose.ShortExact) :
    S.X₃.ShortExact :=
  have := hS.2; have := hS.3; hS.map ShortComplex.π₃

/-- The double transpose of a short complex is isomorphic to itself. -/
abbrev transposeTranspose (S : ShortComplex (ShortComplex C)) :
    S ≅ S.transpose.transpose := Iso.refl _

omit [HasFiniteLimits C] [HasFiniteColimits C] [HasImages C] [HasKernels C] in
/-- A short-exact `S` gives a short-exact double transpose. -/
lemma ttses {S : ShortComplex (ShortComplex C)} (hS : S.ShortExact) :
    S.transpose.transpose.ShortExact := by simpa

/-- The two composite connecting homomorphisms through the bicomplex differ by a sign. -/
lemma anticommutativity (S : ShortComplex <| ShortComplex (Rep R G)) (hS : S.ShortExact)
    (hS' : S.transpose.ShortExact) (n : ℤ) :
    δ (ses₃ hS') n ≫ δ (ses₁ (ttses hS)) (n + 1) = - δ (ses₃ (ttses hS)) n ≫ δ (ses₁ hS') (n + 1)
    := by
  have _ := hS.2; have _ := hS.3; have _ := hS'.2; have _ := hS'.3
  let φ : S.X₂.X₂ ⟶ S.X₃.X₃ := S.X₂.g ≫ S.g.τ₃
  let D := kernel φ
  let SD : ShortComplex (Rep.{u} R G) :=
    { X₁ := D, X₂ := S.X₂.X₂, X₃ := S.X₃.X₃
      f := kernel.ι φ, g := φ, zero := kernel.condition φ }
  have hSD : SD.ShortExact :=
    { exact := ShortComplex.exact_kernel φ
      mono_f := equalizer.ι_mono
      epi_g := @epi_comp _ _ _ _ _ _ (ses₂ hS').3 _ (ses₃ (ttses hS)).3 }
  let i : S.X₁.X₁ ⟶ S.X₁.X₂ ⨿ S.X₂.X₁ := S.X₁.f ≫ coprod.inl + S.f.τ₁ ≫ coprod.inr
  let j : S.X₁.X₂ ⨿ S.X₂.X₁ ⟶ D := coprod.desc (kernel.lift _ S.f.τ₂ (by
      change S.f.τ₂ ≫ S.X₂.g ≫ S.g.τ₃ = 0
      rw [← Category.assoc, S.f.comm₂₃, Category.assoc,
        show S.f.τ₃ ≫ S.g.τ₃ = (S.f ≫ S.g).τ₃ from rfl, S.zero]; simp))
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
    rw [Preadditive.comp_neg, ← S.f.comm₁₂]; abel
  let SA' : ShortComplex (Rep.{u} R G) :=
    { X₁ := S.X₁.X₁, X₂ := S.X₁.X₂ ⨿ S.X₂.X₁, X₃ := D, f := i, g := j, zero := hij }
  have mono_X₁f : Mono S.X₁.f := (ses₁ hS').mono_f
  have mono_i : Mono i :=
    mono_of_mono_fac (f := coprod.desc (𝟙 _) 0) (show
      (S.X₁.f ≫ coprod.inl + S.f.τ₁ ≫ coprod.inr) ≫ coprod.desc (𝟙 _) 0 = S.X₁.f by
      rw [Preadditive.add_comp, Category.assoc, Category.assoc, coprod.inl_desc,
        coprod.inr_desc, Category.comp_id, Limits.comp_zero, add_zero])
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
    have hd_gτ₃' : (d ≫ kernel.ι φ ≫ S.X₂.g) ≫ S.g.τ₃ = 0 := by
      rw [show (d ≫ kernel.ι φ ≫ S.X₂.g) ≫ S.g.τ₃ = d ≫ kernel.ι φ ≫ S.X₂.g ≫ S.g.τ₃ by
        simp [Category.assoc], kernel.condition φ, Limits.comp_zero]
    obtain ⟨A₁, π₁, hπ₁, a'', ha''⟩ :=
      exact_col3.exact_up_to_refinements (d ≫ kernel.ι φ ≫ S.X₂.g) hd_gτ₃'
    obtain ⟨A₂, π₂, hπ₂, a, ha⟩ := surjective_up_to_refinements_of_epi S.X₁.g a''
    have hb'_g : (π₂ ≫ π₁ ≫ d ≫ kernel.ι φ - a ≫ S.f.τ₂) ≫ S.X₂.g = 0 := by
      have e1 : (π₂ ≫ π₁ ≫ d ≫ kernel.ι φ) ≫ S.X₂.g = π₂ ≫ a'' ≫ S.f.τ₃ := by
        rw [show (π₂ ≫ π₁ ≫ d ≫ kernel.ι φ) ≫ S.X₂.g = π₂ ≫ π₁ ≫ d ≫ kernel.ι φ ≫ S.X₂.g
          by simp [Category.assoc], ha'']
      have e2 : (a ≫ S.f.τ₂) ≫ S.X₂.g = π₂ ≫ a'' ≫ S.f.τ₃ := by
        rw [Category.assoc, S.f.comm₂₃, ← Category.assoc a, ← ha, Category.assoc]
      rw [Preadditive.sub_comp, e1, e2, sub_self]
    obtain ⟨A₃, π₃, hπ₃, b'', hb''⟩ :=
      exact_col2.exact_up_to_refinements _ hb'_g
    refine ⟨A₃, π₃ ≫ π₂ ≫ π₁, epi_comp _ _,
        (π₃ ≫ a) ≫ (coprod.inl : S.X₁.X₂ ⟶ S.X₁.X₂ ⨿ S.X₂.X₁) -
          b'' ≫ (coprod.inr : S.X₂.X₁ ⟶ S.X₁.X₂ ⨿ S.X₂.X₁), ?_⟩
    apply (cancel_mono (kernel.ι φ)).1
    rw [Preadditive.comp_sub] at hb''
    simp only [Preadditive.sub_comp, Category.assoc, hj₁, hj₂, Preadditive.comp_neg, sub_neg_eq_add]
    linear_combination (norm := (simp; abel)) hb''
  -- (1b) SA'.Exact: exactness at the middle term.
  have exact_SA' : SA'.Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A x hx
    let a : A ⟶ S.X₁.X₂ := x ≫ coprod.desc (𝟙 _) 0
    let b' : A ⟶ S.X₂.X₁ := x ≫ coprod.desc 0 (𝟙 _)
    have hx_decomp : x = a ≫ coprod.inl + b' ≫ coprod.inr := by
      have hid : coprod.desc (𝟙 _) 0 ≫ (coprod.inl : S.X₁.X₂ ⟶ S.X₁.X₂ ⨿ S.X₂.X₁) +
          coprod.desc 0 (𝟙 _) ≫ (coprod.inr : S.X₂.X₁ ⟶ S.X₁.X₂ ⨿ S.X₂.X₁) =
            𝟙 (S.X₁.X₂ ⨿ S.X₂.X₁) := by
        apply coprod.hom_ext <;>
        · simp only [Preadditive.comp_add, ← Category.assoc, coprod.inl_desc,
            coprod.inr_desc, Category.id_comp, Limits.zero_comp, add_zero, zero_add,
            Category.comp_id]
      rw [show x = x ≫ 𝟙 _ by simp, ← hid, Preadditive.comp_add]
      simp [a, b']
    have hjx : a ≫ S.f.τ₂ - b' ≫ S.X₂.f = 0 := by
      have h0 : x ≫ j ≫ kernel.ι φ = 0 := by rw [← Category.assoc, hx, Limits.zero_comp]
      rw [hx_decomp] at h0
      simp only [Preadditive.add_comp, Category.assoc, hj₁, hj₂, Preadditive.comp_neg,
        ← sub_eq_add_neg] at h0
      exact h0
    have ha_g : a ≫ S.X₁.g = 0 := by
      rw [← cancel_mono S.f.τ₃, Limits.zero_comp, Category.assoc, ← S.f.comm₂₃,
        ← Category.assoc, show a ≫ S.f.τ₂ = b' ≫ S.X₂.f by linear_combination (norm := abel) hjx,
        Category.assoc, S.X₂.zero, Limits.comp_zero]
    obtain ⟨A', π, hπ, a', ha'⟩ := exact_row1.exact_up_to_refinements a ha_g
    have ha'_f_τ₁ : a' ≫ S.f.τ₁ = π ≫ b' := by
      rw [← cancel_mono S.X₂.f, Category.assoc, S.f.comm₁₂, ← Category.assoc, ← ha',
        Category.assoc,
        show a ≫ S.f.τ₂ = b' ≫ S.X₂.f by linear_combination (norm := abel) hjx,
        ← Category.assoc]
    refine ⟨A', π, hπ, a', ?_⟩
    change π ≫ x = a' ≫ i
    rw [show a' ≫ i = a' ≫ S.X₁.f ≫ coprod.inl + a' ≫ S.f.τ₁ ≫ coprod.inr by
      change a' ≫ (S.X₁.f ≫ coprod.inl + S.f.τ₁ ≫ coprod.inr) = _; rw [Preadditive.comp_add],
      hx_decomp, Preadditive.comp_add]
    congr 1
    · rw [← Category.assoc, ha', Category.assoc]
    · rw [← Category.assoc, ← ha'_f_τ₁, Category.assoc]
  have hSA' : SA'.ShortExact := { exact := exact_SA', mono_f := mono_i, epi_g := epi_j }
  have exact_S_X₃ : S.X₃.Exact := (ses₃ hS').exact
  have mono_S_X₃f : Mono S.X₃.f := (ses₃ hS').mono_f
  have hFcol_lift_zero : (kernel.ι φ ≫ S.g.τ₂) ≫ S.X₃.g = 0 := by
    rw [Category.assoc, S.g.comm₂₃]; exact kernel.condition φ
  let Fcol_τ₁ : D ⟶ S.X₃.X₁ := exact_S_X₃.lift (kernel.ι φ ≫ S.g.τ₂) hFcol_lift_zero
  have hFcol_τ₁ : Fcol_τ₁ ≫ S.X₃.f = kernel.ι φ ≫ S.g.τ₂ := exact_S_X₃.lift_f _ _
  let Fcol : SD ⟶ S.X₃ :=
    { τ₁ := Fcol_τ₁, τ₂ := S.g.τ₂, τ₃ := 𝟙 _
      comm₁₂ := hFcol_τ₁
      comm₂₃ := by change S.g.τ₂ ≫ S.X₃.g = φ ≫ 𝟙 _; rw [Category.comp_id]; exact S.g.comm₂₃ }
  have exact_S_t_X₃ : S.transpose.X₃.Exact := (ses₃ (ttses hS)).exact
  have mono_S_t_X₃f : Mono S.transpose.X₃.f := (ses₃ (ttses hS)).mono_f
  have hFrow_lift_zero : (kernel.ι φ ≫ S.X₂.g) ≫ S.g.τ₃ = 0 := by
    rw [Category.assoc]; exact kernel.condition φ
  let Frow_τ₁ : D ⟶ S.X₁.X₃ := exact_S_t_X₃.lift (kernel.ι φ ≫ S.X₂.g) hFrow_lift_zero
  have hFrow_τ₁ : Frow_τ₁ ≫ S.f.τ₃ = kernel.ι φ ≫ S.X₂.g := exact_S_t_X₃.lift_f _ _
  let Frow : SD ⟶ S.transpose.X₃ :=
    { τ₁ := Frow_τ₁, τ₂ := S.X₂.g, τ₃ := 𝟙 _
      comm₁₂ := hFrow_τ₁
      comm₂₃ := by change S.X₂.g ≫ S.g.τ₃ = φ ≫ 𝟙 _; rw [Category.comp_id] }
  let Gcol : SA' ⟶ S.X₁ :=
    { τ₁ := 𝟙 _, τ₂ := coprod.desc (𝟙 _) 0, τ₃ := Frow_τ₁
      comm₁₂ := by
        change 𝟙 _ ≫ S.X₁.f = i ≫ coprod.desc (𝟙 _) 0
        rw [Category.id_comp]
        change S.X₁.f = (S.X₁.f ≫ coprod.inl + S.f.τ₁ ≫ coprod.inr) ≫ coprod.desc (𝟙 _) 0
        rw [Preadditive.add_comp, Category.assoc, Category.assoc, coprod.inl_desc,
          coprod.inr_desc, Category.comp_id, Limits.comp_zero, add_zero]
      comm₂₃ := by
        change coprod.desc (𝟙 _) (0 : S.X₂.X₁ ⟶ S.X₁.X₂) ≫ S.X₁.g = j ≫ Frow_τ₁
        apply (cancel_mono S.f.τ₃).1
        rw [Category.assoc, Category.assoc, hFrow_τ₁]
        apply coprod.hom_ext
        · rw [← Category.assoc, ← Category.assoc, coprod.inl_desc, Category.id_comp,
            show coprod.inl ≫ j ≫ kernel.ι φ ≫ S.X₂.g =
              (coprod.inl ≫ j ≫ kernel.ι φ) ≫ S.X₂.g by simp [Category.assoc], hj₁]
          exact S.f.comm₂₃.symm
        · rw [← Category.assoc, ← Category.assoc, coprod.inr_desc, Limits.zero_comp,
            show coprod.inr ≫ j ≫ kernel.ι φ ≫ S.X₂.g =
              (coprod.inr ≫ j ≫ kernel.ι φ) ≫ S.X₂.g by simp [Category.assoc],
            hj₂, Preadditive.neg_comp, S.X₂.zero, neg_zero] }
  have hfg_τ₂ : S.f.τ₂ ≫ S.g.τ₂ = 0 := show (S.f ≫ S.g).τ₂ = 0 by rw [S.zero]; rfl
  let Grow : SA' ⟶ S.transpose.X₁ :=
    { τ₁ := 𝟙 _, τ₂ := coprod.desc 0 (𝟙 _), τ₃ := -Fcol_τ₁
      comm₁₂ := by
        change (𝟙 _ : S.X₁.X₁ ⟶ _) ≫ S.f.τ₁ = i ≫ coprod.desc 0 (𝟙 _)
        rw [Category.id_comp]
        change S.f.τ₁ = (S.X₁.f ≫ coprod.inl + S.f.τ₁ ≫ coprod.inr) ≫ coprod.desc 0 (𝟙 _)
        rw [Preadditive.add_comp, Category.assoc, Category.assoc, coprod.inl_desc,
          coprod.inr_desc, Category.comp_id, Limits.comp_zero, zero_add]
      comm₂₃ := by
        change coprod.desc (0 : S.X₁.X₂ ⟶ S.X₂.X₁) (𝟙 _) ≫ S.g.τ₁ = j ≫ (-Fcol_τ₁)
        apply coprod.hom_ext
        · apply (cancel_mono S.X₃.f).1
          rw [← Category.assoc, coprod.inl_desc, Limits.zero_comp, Limits.zero_comp,
            Category.assoc, Category.assoc, Preadditive.neg_comp, hFcol_τ₁,
            show coprod.inl ≫ j ≫ -(kernel.ι φ ≫ S.g.τ₂) =
              -((coprod.inl ≫ j ≫ kernel.ι φ) ≫ S.g.τ₂) by
              simp [Preadditive.comp_neg, Category.assoc],
            hj₁, hfg_τ₂, neg_zero]
        · apply (cancel_mono S.X₃.f).1
          rw [← Category.assoc, coprod.inr_desc, Category.id_comp,
            Category.assoc, Category.assoc, Preadditive.neg_comp, hFcol_τ₁,
            show coprod.inr ≫ j ≫ -(kernel.ι φ ≫ S.g.τ₂) =
              -((coprod.inr ≫ j ≫ kernel.ι φ) ≫ S.g.τ₂) by
              simp [Preadditive.comp_neg, Category.assoc],
            hj₂, Preadditive.neg_comp, neg_neg]
          exact S.g.comm₁₂.symm }
  -- Step 8: assemble via δ_naturality.
  -- δ_naturality Fcol : δ hSD n ≫ map Fcol.τ₁ = map Fcol.τ₃ ≫ δ (ses₃ hS') n
  -- δ_naturality Frow : δ hSD n ≫ map Frow.τ₁ = map Frow.τ₃ ≫ δ (ses₃ (ttses hS)) n
  -- δ_naturality Gcol : δ hSA' (n+1) ≫ map Gcol.τ₁ = map Gcol.τ₃ ≫ δ (ses₁ hS') (n+1)
  -- δ_naturality Grow : δ hSA' (n+1) ≫ map Grow.τ₁ = map Grow.τ₃ ≫ δ (ses₁ (ttses hS)) (n+1)
  have hδFcol : δ hSD n ≫ (tateCohomology (n + 1)).map Fcol.τ₁
      = (tateCohomology n).map Fcol.τ₃ ≫ δ (ses₃ hS') n :=
    TateCohomology.δ_naturality hSD (ses₃ hS') Fcol n
  have hδFrow : δ hSD n ≫ (tateCohomology (n + 1)).map Frow.τ₁
      = (tateCohomology n).map Frow.τ₃ ≫ δ (ses₃ (ttses hS)) n :=
    TateCohomology.δ_naturality hSD (ses₃ (ttses hS)) Frow n
  have hδGcol : δ hSA' (n + 1) ≫ (tateCohomology (n + 1 + 1)).map Gcol.τ₁
      = (tateCohomology (n + 1)).map Gcol.τ₃ ≫ δ (ses₁ hS') (n + 1) :=
    TateCohomology.δ_naturality hSA' (ses₁ hS') Gcol (n + 1)
  have hδGrow : δ hSA' (n + 1) ≫ (tateCohomology (n + 1 + 1)).map Grow.τ₁
      = (tateCohomology (n + 1)).map Grow.τ₃ ≫ δ (ses₁ (ttses hS)) (n + 1) :=
    TateCohomology.δ_naturality hSA' (ses₁ (ttses hS)) Grow (n + 1)
  -- All of Gcol.τ₁, Frow.τ₃, Grow.τ₁, Fcol.τ₃ are 𝟙. Grow.τ₃ = -Fcol_τ₁.
  have hFcol_τ₃_id : (tateCohomology n).map Fcol.τ₃ = 𝟙 _ := CategoryTheory.Functor.map_id _ _
  have hFrow_τ₃_id : (tateCohomology n).map Frow.τ₃ = 𝟙 _ := CategoryTheory.Functor.map_id _ _
  have hGcol_τ₁_id : (tateCohomology (n + 1 + 1)).map Gcol.τ₁ = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  have hGrow_τ₁_id : (tateCohomology (n + 1 + 1)).map Grow.τ₁ = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  -- Grow.τ₃ = -Fcol_τ₁ = -Frow_τ₁? No, Grow.τ₃ = -Fcol_τ₁ (different from Frow_τ₁).
  -- Wait, Grow goes to row1 with row1.X₃ = S.X₃.X₁, and Fcol goes to col3 with col3.X₁ = S.X₃.X₁.
  -- So Grow.τ₃ : D → S.X₃.X₁ and Fcol.τ₁ : D → S.X₃.X₁, types match.
  have inst_add : (tateCohomology (R := R) (G := G) (n + 1)).Additive := by
    change (tateComplexFunctor ⋙ HomologicalComplex.homologyFunctor _ _ (n + 1)).Additive
    infer_instance
  have hGrow_τ₃_eq : (tateCohomology (n + 1)).map Grow.τ₃
      = -(tateCohomology (n + 1)).map Fcol.τ₁ := by
    change (tateCohomology (n + 1)).map (-Fcol_τ₁) = -(tateCohomology (n + 1)).map Fcol_τ₁
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
  rw [Preadditive.comp_neg]
