
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

--
-- Purpose: Function types don't have modalites,
-- mod introduces always single modalities
--

module KamiCore.Language.MinMTT.Definition where

open import Agora.Conventions hiding (m ; n ; k ; _∣_)
open import Agora.Data.Product.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.TypeTheory.Notation

open import KamiCore.Language.MTT.Definition


record MinMTT (𝑖 : 𝔏 ^ 5) : 𝒰 (𝑖 ⁺) where
  field modeTheory : 2Category 𝑖

open MinMTT public

module _ 𝑖 where macro
  Min𝔐TT = #structureOn (MinMTT 𝑖)

module Min𝔐TT/Definition (This : Min𝔐TT 𝑖) where

  private
    Super : 𝔐TT 𝑖
    Super = record { 𝓂 = ⟨ modeTheory This ⟩ }

    open 𝔐TT/Definition {{Super}} hiding (_⊢_)

    variable
      m n o : Param {{hasParamSTT:MTT}} Super
      μ η : ModeHom m n
      Γ : CtxOf {{hasParamSTT:MTT}} Super m
      A B C : TypeOf {{hasParamSTT:MTT}} Super m


  data _⊢_ : ∀{a : Param Super} -> Ctx a of Super -> Type a of Super -> 𝒰 𝑖 where
    var : ∀{μ : _ ⟶ o} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> (α : μ ⟹ η) -> Γ ⊢ A

    tt : Γ ⊢ Unit

    -- modalities
    mod : ∀ μ -> Γ ∙! μ ⊢ A -> Γ ⊢ ⟨ A ∣ μ ⟩
    letmod : ∀{μ : o ⟶ n} -> (ν : n ⟶ m)
          -> Γ ∙! ν ⊢ ⟨ A ∣ μ ⟩
          -> Γ ∙⟮ A ∣ μ ◆ ν ⟯ ⊢ B
          -> Γ ⊢ B

    -- explicit transformations
    trans : ∀ {μ ν : n ⟶ m} -> μ ⟹ ν -> Γ ⊢ ⟨ A ∣ μ ⟩ -> Γ ⊢ Tr ⟨ A ∣ ν ⟩

    -- transformations monad
    pure : Γ ⊢ A -> Γ ⊢ Tr A
    seq : ∀{A : ⊢Type m} -> Γ ⊢ Tr A -> Γ ∙⟮ A ∣ id ⟯ ⊢ Tr B -> Γ ⊢ Tr B

    -- functions
    lam : Γ ∙⟮ A ∣ μ ⟯ ⊢ B -> Γ ⊢ ⟮ A ∣ μ ⟯⇒ B
    app : Γ ⊢ ⟮ A ∣ μ ⟯⇒ B -> Γ ∙! μ ⊢ B -> Γ ⊢ B

    -- sum types
    left : Γ ⊢ A -> Γ ⊢ Either A B
    right : Γ ⊢ B -> Γ ⊢ Either A B
    either : {Γ : Ctx m of Super} -> Γ ⊢ Either A B -> Γ ∙⟮ A ∣ id ⟯ ⊢ C -> Γ ∙⟮ B ∣ id ⟯ ⊢ C -> Γ ⊢ C

    -- list types
    [] : Γ ⊢ Lst A
    _∷_ : Γ ⊢ A -> Γ ⊢ Lst A -> Γ ⊢ Lst A
    rec-Lst : {Γ : Ctx m of Super} -> Γ ⊢ Lst A -> Γ ⊢ C -> Γ ∙⟮ A ∣ id ⟯ ∙⟮ C ∣ id ⟯ ⊢ C -> Γ ⊢ C




