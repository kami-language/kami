
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

--
-- Purpose: Function types don't have modalites,
-- mod introduces always single modalities
--

module KamiCore.Language.MinMTT.Translation where

open import Agora.Conventions hiding (m ; n ; k ; _∣_)
open import Agora.Data.Product.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.TypeTheory.STT.Definition
open import Agora.TypeTheory.ParamSTT.Definition
open import Agora.Category.Std.Category.Structured.Classified.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice


open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding (ModeHom)
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id') hiding (unit-r-◆)

open import KamiCore.Language.MTT.Definition
open import KamiCore.Language.MinMTT.Definition
open import KamiCore.Language.MinMTT.Properties


F₁ : Min𝔐TT 𝑖 -> 𝔐TT _
F₁ This = Min𝔐TT/Definition.[Min𝔐TT/Definition::Private].Super This

module _ {𝑖} where
  macro 𝔉₁ = #structureOn (F₁ {𝑖 = 𝑖})

module _ (This : Min𝔐TT 𝑖) where
  open Min𝔐TT/Definition This
  open [Min𝔐TT/Definition::Private]
  open [Min𝔐TT/Definition::Type]
  open [Min𝔐TT/Definition::Ctx]
  open [Min𝔐TT/Definition::Term]
  open Min𝔐TT/Properties This

  open 𝔐TT/Definition Super
  open [𝔐TT/Definition::Type] renaming (⊢Type to 𝔐TT⊢Type)
  open [𝔐TT/Definition::Ctx] renaming (⊢Ctx to 𝔐TT⊢Ctx)
  open [𝔐TT/Definition::Term] renaming (_⊢_ to _𝔐TT⊢_ ; _⊢Var⟮_∣_⇒_⟯ to _𝔐TT⊢Var⟮_∣_⇒_⟯ ; _⊢Var⟮_∣_⇒∼_⟯ to _𝔐TT⊢Var⟮_∣_⇒∼_⟯)
  open Variables/Mode
  open Variables/Hom

  par-𝔉₁ : Param Super -> Param This
  par-𝔉₁ x = x



  --------------------------------------------------------------------
  -- Types

  ⟪𝔉₁∣_Type⟫ : ∀{a} -> 𝔐TT⊢Type a -> ⊢Type a
  ⟪𝔉₁∣ ⟨ X ∣ μ ⟩ Type⟫ = Mod-Type (split This μ) ⟪𝔉₁∣ X Type⟫
  ⟪𝔉₁∣ Unit Type⟫ = Unit
  ⟪𝔉₁∣ Tr X Type⟫ = Tr ⟪𝔉₁∣ X Type⟫
  ⟪𝔉₁∣ Either X Y Type⟫ = Either ⟪𝔉₁∣ X Type⟫ ⟪𝔉₁∣ Y Type⟫
  ⟪𝔉₁∣ Lst X Type⟫ = Lst ⟪𝔉₁∣ X Type⟫
  ⟪𝔉₁∣ ⟮ X ∣ μ ⟯⇒ Y Type⟫ =  Mod-Type (split This μ) ⟪𝔉₁∣ X Type⟫ ⇒ ⟪𝔉₁∣ Y Type⟫

  -- End Types
  --------------------------------------------------------------------


  --------------------------------------------------------------------
  -- Contexts

  ⟪𝔉₁∣_Ctx⟫ : {a : Param Super} -> Ctx a of Super -> Ctx a of This
  ⟪𝔉₁∣ ε Ctx⟫ = ε
  ⟪𝔉₁∣ Γ ∙⟮ X ∣ μ ⟯ Ctx⟫ = ⟪𝔉₁∣ Γ Ctx⟫ ∙⟮ ⟪𝔉₁∣ X Type⟫ ∣ μ ⟯
  ⟪𝔉₁∣ Γ ∙! μ Ctx⟫ = ⟪𝔉₁∣ Γ Ctx⟫ ∙!* (split This μ)

  -- End Contexts
  --------------------------------------------------------------------

  --------------------------------------------------
  -- Variables


  mutual
    preserve-∙!* : {X : 𝔐TT⊢Type k} {Γ : 𝔐TT⊢Ctx {n} m}
                  -> ∀ (ωs : Path _⟶ₛ_ l  m) -> {μ : k ⟶ o}
                  -- -> ∀ ωs -> {μ : k ⟶ o}
                  -> Γ 𝔐TT⊢Var⟮ X ∣ μ ⇒ η ⟯
                  -> ⟪𝔉₁∣ Γ Ctx⟫ ∙!* ωs ⊢Var⟮ ⟪𝔉₁∣ X Type⟫  ∣ μ ⇒∼ (Comp-Path fst ωs) ◆ η ⟯
    preserve-∙!* id' v = transp-Var-∼ (sym unit-l-◆) (transl-Var v)
    preserve-∙!* (x ⨾ ωs) v =
      let (varOver η' x ωs◆η∼η') = preserve-∙!* ωs v
      in varOver _ (suc! x) (assoc-l-◆ ∙ refl-∼ ◈ ωs◆η∼η')


    transl-Var : {X : 𝔐TT⊢Type k} {Γ : 𝔐TT⊢Ctx {n} m} -> Γ 𝔐TT⊢Var⟮ X ∣ μ ⇒ η ⟯ -> ⟪𝔉₁∣ Γ Ctx⟫ ⊢Var⟮ ⟪𝔉₁∣ X Type⟫  ∣ μ ⇒∼ η ⟯
    transl-Var zero = varOver _ zero refl-∼ -- zero
    transl-Var (suc! {ω = ω} v) = transp-Var-∼ (preserve-comp-split This ◈ refl-∼) (preserve-∙!* (split This ω) v)
    transl-Var (suc v) =
      let (varOver η' v' p) = transl-Var v
      in varOver _ (suc v') p

    -- transl-Var' : {X : 𝔐TT⊢Type k} {Γ : 𝔐TT⊢Ctx {n} k} -> Γ 𝔐TT⊢Var⟮ X ∣ μ ⇒ η ⟯ -> ⟪𝔉₁∣ Γ Ctx⟫ ⊢ ⟪𝔉₁∣ X Type⟫
    -- transl-Var' = {!!}


  -- End Variables
  --------------------------------------------------


  --------------------------------------------------------------------
  -- Terms
  Mod-Term : (μs : Path _⟶ₛ_ m n) -> {X : ⊢Type m}
             -> (t : Γ ∙!* μs ⊢ X)
             -> Γ ⊢ Mod-Type μs X
  Mod-Term id' t = t
  Mod-Term (μ ⨾ μs) t = Mod-Term μs (mod μ t)

  Pure-letmod : (νs : Path _⟶ₛ_ n m)
        -> Γ ∙!* νs ⊢ A
        -> Γ ∙⟮ A ∣ Comp-Path fst νs ⟯ ⊢ B
        -> Γ ⊢ B
  Pure-letmod id' t s = app (lam s) t
  Pure-letmod (x ⨾ νs) t s = letmod (Comp-Path fst νs) (transp-Ctx-res2 {μ₀ = νs} (sym (preserve-comp-split This) ) (mod x t)) s

  Letmod-Term-impl : ∀{μs : Path _⟶ₛ_ o n} -> (ν : n ⟶ m)
        -> Γ ∙!* (split This ν) ⊢ Mod-Type μs A
        -> Γ ∙⟮ A ∣ Comp-Path fst μs ◆ ν ⟯ ⊢ B
        -> Γ ⊢ B
  Letmod-Term-impl {μs = id'} ν t s = (Pure-letmod (split This ν) t (transp-Ctx-∼ (unit-l-◆ ∙ sym (preserve-comp-split This)) s) )
  Letmod-Term-impl {Γ = Γ} {A = A} {μs = x ⨾ μs} ν t s =
    Letmod-Term-impl {μs = μs} ν t
    (letmod {A = A} {μ = x} (Comp-Path fst μs ◆ ν)
    (
    let s' : Γ ∙⟮ ⟨ A ∣ x ⟩ ∣ Comp-Path fst μs ◆ ν ⟯ ∙!* split This (Comp-Path fst μs ◆ ν) ⊢ ⟨ A ∣ x ⟩
        s' = var (suc!* (sym (preserve-comp-split This) ∙ sym unit-r-◆) zero) id (is⊥:id This ⟡-∼≤ initial-⊥)
    in s'
    )
    (wk-ind {Δ = ε ∙⟮ _ ∣ _ ⟯} (transp-Ctx-∼ assoc-l-◆ s)))


  Letmod-Term : ∀{μ : o ⟶ n} -> (ν : n ⟶ m)
        -> Γ ∙!* (split This ν) ⊢ Mod-Type (split This μ) A
        -> Γ ∙⟮ A ∣ μ ◆ ν ⟯ ⊢ B
        -> Γ ⊢ B
  Letmod-Term {μ = μ} ν t s = Letmod-Term-impl {μs = split This μ} ν t (transp-Ctx-∼ (sym (preserve-comp-split This) ◈ refl-∼) s)

  Letmod'-Term : ∀{μ : o ⟶ n}
        -> Γ ⊢ Mod-Type (split This μ) A
        -> Γ ∙⟮ A ∣ μ ⟯ ⊢ B
        -> Γ ⊢ B
  Letmod'-Term {μ = μ} t s = Letmod-Term id (transp-Ctx-res2 {μ₀ = idₛ ⨾ id'} (unit-l-◆ ∙ sym (preserve-comp-split This)) (lift-id-Term t)) (transp-Ctx-∼ (sym unit-r-◆) s)



  ⟪𝔉₁∣_Term⟫ : {a : Param Super} -> {Γ : Ctx a of Super} -> {X : Type a of Super}
               -> Γ ⊢ X at a of Super
               -> ⟪𝔉₁∣ Γ Ctx⟫ ⊢ ⟪𝔉₁∣ X Type⟫ at a of This
  ⟪𝔉₁∣ var x α x₁ Term⟫ =
    let (varOver η' x pp) = (transl-Var x)
    in var x (α ◆ ⟨ 2celliso pp ⟩) (preserve-◆ α ⟨ 2celliso pp ⟩ ⟡-∼≤ [ x₁ , is⊥:2celliso This pp ⟡-∼≤ initial-⊥ ]-∨)
  ⟪𝔉₁∣ mod μ t Term⟫ = Mod-Term (split This μ) ⟪𝔉₁∣ t Term⟫
  ⟪𝔉₁∣ letmod ν t s Term⟫ = Letmod-Term ν ⟪𝔉₁∣ t Term⟫ ⟪𝔉₁∣ s Term⟫
  ⟪𝔉₁∣ trans α x t Term⟫ = trans α x ⟪𝔉₁∣ t Term⟫
  ⟪𝔉₁∣ pure t Term⟫ = pure ⟪𝔉₁∣ t Term⟫
  ⟪𝔉₁∣ seq t t₁ Term⟫ = seq ⟪𝔉₁∣ t Term⟫ ⟪𝔉₁∣ t₁ Term⟫
  ⟪𝔉₁∣ lam t Term⟫ = lam (Letmod'-Term (var zero ⟨ 2celliso refl-∼ ⟩ (is⊥:2celliso This refl-∼ ⟡-∼≤ initial-⊥)) -- ⟪𝔉₁∣ var zero υ⁻¹-l-◆ {!!} Term⟫
    let t' = ⟪𝔉₁∣ t Term⟫
    in wk-ind {Δ = ε ∙⟮ _ ∣ _ ⟯} t')
  ⟪𝔉₁∣ app {μ = μ} t t₁ Term⟫ = app ⟪𝔉₁∣ t Term⟫ (Mod-Term (split This μ) ⟪𝔉₁∣ t₁ Term⟫)
  ⟪𝔉₁∣ tt Term⟫ = tt
  ⟪𝔉₁∣ left t Term⟫ = left ⟪𝔉₁∣ t Term⟫
  ⟪𝔉₁∣ right t Term⟫ = right ⟪𝔉₁∣ t Term⟫
  ⟪𝔉₁∣ either t t₁ t₂ Term⟫ = either ⟪𝔉₁∣ t Term⟫ ⟪𝔉₁∣ t₁ Term⟫ ⟪𝔉₁∣ t₂ Term⟫
  ⟪𝔉₁∣ [] Term⟫ = []
  ⟪𝔉₁∣ t ∷ t₁ Term⟫ = ⟪𝔉₁∣ t Term⟫ ∷ ⟪𝔉₁∣ t₁ Term⟫
  ⟪𝔉₁∣ rec-Lst t t₁ t₂ Term⟫ = rec-Lst ⟪𝔉₁∣ t Term⟫ ⟪𝔉₁∣ t₁ Term⟫ ⟪𝔉₁∣ t₂ Term⟫

  -- End Terms
  --------------------------------------------------------------------


  run-𝔉₁ : {a : Param Super}
           -> (pa : SubParam Super a)
           -> Hom-STT (Super at a) (This at a)
  run-𝔉₁ pa = record
    { ⟪_∣_Ctx⟫ = ⟪𝔉₁∣_Ctx⟫
    ; ⟪_∣_Type⟫ = ⟪𝔉₁∣_Type⟫
    ; ⟪_∣_Term⟫ = ⟪𝔉₁∣_Term⟫
    }



instance
  isReduction:F₁ : isParamSTTHom (Min𝔐TT 𝑖) (𝔐TT _) F₁
  isReduction:F₁ = record
    { param = par-𝔉₁
    ; runAt = run-𝔉₁
    }


