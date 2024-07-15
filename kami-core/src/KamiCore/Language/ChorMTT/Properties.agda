
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorMTT.Properties where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import KamiTheory.Basics
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.UniqueSortedList.Instance.Preorder
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import Data.List using (drop)

open import KamiCore.Language.ChorMTT.Definition
open import KamiCore.Language.MinMTT.Definition
open import KamiCore.Language.MinMTT.Properties


module Chor𝔐TT/Properties (This : Chor𝔐TT 𝑗) where
  -- open Chor𝔐TT/Definition This
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Private] This
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Param] This
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Ctx] This
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Term] This
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Type] This

  open Min𝔐TT/Properties Super
  open Min𝔐TT/Definition Super
  open [Min𝔐TT/Definition::Private] using (_⟶ₛ_)

  ----------------------------------------------------------
  -- Ctx₂ proofs
  ----------------------------------------------------------

  -- stepsVar : ∀{μ : } -> isCtx₂ Γ -> isCtx₂ (Γ ∙!* μ)
  stepsRes : {Γ : ⊢Ctx c} -> (μs : Path _⟶ₛ_ b c)
             -> isCtx₂ Γ -> isCtx₂ (Γ ∙!* μs)
  stepsRes id' Γp = Γp
  stepsRes ((.(x ⨾ id') , incl x) ⨾ μs) Γp = stepRes _ (stepsRes μs Γp)


  ----------------------------------------------------------
  -- Working with the context
  --
  -- Various proofs which let us transfer terms from
  -- some context to a similar one.
  ----------------------------------------------------------
  --
  {-
  com-restr-single : ∀{x : BaseModeHom-PolySR a b} -> ∀{xp} -> {A : ⊢Type c}
                    -> {B : ⊢Type a}
                    -> (Γ ∙! ((x ⨾ id') , xp)) ∙⟮ A ∣ μ ⟯ ⊢ B
                    -> Γ ∙⟮ A ∣ μ ◆ (x ⨾ id') ⟯ ∙! ((x ⨾ id') , xp) ⊢ B
  com-restr-single = {!!}

  com⁻¹-restr-single : ∀{x : BaseModeHom-PolySR a b} -> ∀{xp} -> {A : ⊢Type c}
                    -> {B : ⊢Type a}
                    -> Γ ∙⟮ A ∣ μ ◆ (x ⨾ id') ⟯ ∙! ((x ⨾ id') , xp) ⊢ B
                    -> (Γ ∙! ((x ⨾ id') , xp)) ∙⟮ A ∣ μ ⟯ ⊢ B
  com⁻¹-restr-single = {!!}

  id-annotate : {μ : a ⟶ b} -> Γ ∙⟮ A ∣ μ ⟯ ⊢ B -> Γ ∙⟮ Mod-Type (split Super μ) A ∣ id' ⟯ ⊢ B
  id-annotate = {!!}
  -}


  ----------------------------------------------------------
  -- Terms
  ----------------------------------------------------------

  cong-Type-ChorMTT : A ≡ B -> Γ ⊢ A -> Γ ⊢ B
  cong-Type-ChorMTT refl-≡ t = t

  cong-Mod-Type : {μ ν : Path _⟶ₛ_ a b}
                -> μ ≡ ν -> Mod-Type μ A ≡ Mod-Type ν A
  cong-Mod-Type refl-≡ = refl-≡



  ----------------------------------------------------------
  -- Dealing with transformations
  ----------------------------------------------------------

  invisible-id : ∀ {μ ν : a ⟶ b}
              -> (α : Linear2Cell invis μ ν)
              -> μ ≡ ν
  invisible-id [] = refl-≡


  transl-trans-Single : ∀ {μ ν : a ⟶ ◯}
              -> {A : ⊢Type a}
              -> (α : SingleFace' vis μ ν)
              -> (classify-Single α ≤ impureTrans Super)
              -> Γ ⊢ Mod-Type (split-Min𝔐TT μ) A
              -> Γ ⊢ Tr (Mod-Type (split-Min𝔐TT ν) A)
  transl-trans-Single (singleFace (idₗ₁ ⌟[ send U ]⌞ idᵣ₁) top₁ bot) αp t = ⊥-elim (≰-singleton (λ ()) αp)
  transl-trans-Single (singleFace (idₗ₁ ⌟[ recv U ]⌞ (_ ⨾ _)) top₁ bot) αp t = ⊥-elim (≰-singleton (λ ()) αp)
  transl-trans-Single {Γ = Γ} {A = A} (singleFace (ϕ ⌟[ recv U ]⌞ id') refl-≡ refl-≡) αp t =
    let p : Mod-Type (split-Min𝔐TT (ϕ ◆' `[]` ⨾ `＠` U ⨾ id')) A
            ≡ Mod-Type (split-Min𝔐TT ϕ ◆' split-Min𝔐TT (`[]` ⨾ `＠` U ⨾ id')) A
        p = cong-Mod-Type (preserve-◆-split-Min𝔐TT {μ = ϕ} {ν = (`[]` ⨾ `＠` U ⨾ id')})

        t' : Γ ⊢ Mod-Type (split-Min𝔐TT (`[]` ⨾ `＠` U ⨾ id')) (Mod-Type (split-Min𝔐TT ϕ) A)
        t' = cong-Type-ChorMTT ( p ∙-≡ preserve-◆-Mod-Type {μ = (split-Min𝔐TT ϕ)} {ν = (split-Min𝔐TT (`[]` ⨾ `＠` U ⨾ id'))}) t

    in broadcast t'



  transl-trans-Linear : ∀ {μ ν : a ⟶ ◯}
              -> {A : ⊢Type a}
              -> (α : Linear2Cell vis μ ν)
              -> (classify-Linear α ≤ impureTrans Super)
              -> Γ ⊢ Mod-Type (split-Min𝔐TT μ) A
              -> Γ ⊢ Tr (Mod-Type (split-Min𝔐TT ν) A)
  transl-trans-Linear [] αp t = pure t
  transl-trans-Linear (x ∷ α) αp t =
    let t' = transl-trans-Single x (ι₀-∨ ⟡ αp) t
        t'' = transl-trans-Linear α (ι₁-∨ {a = classify-Single x} ⟡ αp) (var zero [ incl [] ∣ incl [] ] initial-⊥)
    in seq t' t''


  transl-trans : ∀ {μ ν : a ⟶ ◯}
              -> {A : ⊢Type a}
              -> (α : μ ⟹ ν)
              -> (classify α ≤ impureTrans Super)
              -> Γ ⊢ Mod-Type (split-Min𝔐TT μ) A
              -> Γ ⊢ Tr (Mod-Type (split-Min𝔐TT ν) A)
  transl-trans [ incl α-invis ∣ incl α-vis ] αp t
    with invisible-id (linearize α-invis)
  ... | refl-≡
    = transl-trans-Linear (linearize α-vis) αp t



  impossible-trans-Single : ∀ {μ ν : a ⟶ ▲ U}
              -> (α : SingleFace' vis μ ν)
              -> (classify-Single α ≤ impureTrans Super)
              -> 𝟘-𝒰
  impossible-trans-Single (singleFace (idₗ₁ ⌟[ send U ]⌞ idᵣ₁) top₁ bot) αp = ⊥-elim (≰-singleton (λ ()) αp) -- {!!} --  with ⟨ αp ⟩ _ here
  -- ... | there ()
  impossible-trans-Single (singleFace (idₗ₁ ⌟[ recv U ]⌞ (_ ⨾ _)) refl-≡ bot) αp = ⊥-elim (≰-singleton (λ ()) αp) -- {!!}

  impossible-trans-Linear : {μ ν : a ⟶ ▲ U}
              -> (α : Linear2Cell vis μ ν)
              -> (classify-Linear α ≤ impureTrans Super) 
              -> μ ≡ ν
  impossible-trans-Linear [] αp = refl-≡
  impossible-trans-Linear (x ∷ α) αp = ⊥-elim (impossible-trans-Single x (ι₀-∨ ⟡ αp))

  impossible-trans : {μ ν : a ⟶ ▲ U}
              -> (α : μ ⟹ ν)
              -> (classify α ≤ impureTrans Super) 
              -> μ ≡ ν
  impossible-trans [ incl α-invis ∣ incl α ] αp
    with invisible-id (linearize α-invis)
  ... | refl-≡
    = impossible-trans-Linear (linearize α) αp

