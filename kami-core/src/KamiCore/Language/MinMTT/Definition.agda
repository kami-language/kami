
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

open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')


record MinMTT (𝑖 : 𝔏 ^ 5) : 𝒰 (𝑖 ⁺) where
  field ModeTheory : 2Category 𝑖
  field isSmall : ∀{a b : ⟨ ModeTheory ⟩} -> a ⟶ b -> 𝒰₀
  field split : ∀{a b : ⟨ ModeTheory ⟩} -> a ⟶ b -> Path (λ a b -> a ⟶ b) a b

  -- TODO: We need extra information here
  -- about how to split the arrows into singletons

open MinMTT public

module _ 𝑖 where macro
  Min𝔐TT = #structureOn (MinMTT 𝑖)

module Min𝔐TT/Definition (This : Min𝔐TT 𝑖) where

  private
    Super : 𝔐TT 𝑖
    Super = record { 𝓂 = ⟨ This .ModeTheory ⟩ }

    open 𝔐TT/Definition {{Super}} hiding (_⊢_)
    open Variables/Mode
    open Variables/Hom
    open Variables/Type
    open Variables/Ctx


  data _⊢_ : ∀{m : Param Super} -> Ctx m of Super -> Type m of Super -> 𝒰 𝑖 where
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

  module _ (m : Param Super) where
    λMinMTT : STT _
    λMinMTT = record
      { Ctx = Ctx m of Super
      ; Type = Type m of Super
      ; Term = λ Γ A -> Γ ⊢ A
      }

instance
  hasParamSTT:MinMTT : hasParamSTT (Min𝔐TT 𝑖)
  hasParamSTT:MinMTT = record
    { Param = λ This -> ⟨ This .ModeTheory ⟩
    ; _at_ = λ This m -> Min𝔐TT/Definition.λMinMTT This m
    }

