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
  -- The remaining substance of the proof:
  --   * `Epi j`        -- standard 3x3 lemma diagram chase using rows and columns exact
  --   * `SA'.Exact`    -- standard 3x3 lemma diagram chase, identifying kernel(j) with image(i)
  --   * The main anticommutativity: build two morphisms of short exact sequences
  --     `SA' ⟶ S.X₃` (third row) and `SA' ⟶ S.X₁` (first row, with sign on the
  --     τ₁ component), then apply naturality of δ twice and combine.
  sorry
