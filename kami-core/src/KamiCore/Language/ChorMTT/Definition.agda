
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorMTT.Definition where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category
open import Data.List using (drop)


open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')

open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Basics hiding (_⋆_)


open import Agora.TypeTheory.STT.Definition
open import Agora.TypeTheory.ParamSTT.Definition

open import KamiCore.Language.MTT.Definition


record ChorMTT : 𝒰₀ where
  field roles : ℕ

open ChorMTT public

macro Chor𝔐TT = #structureOn ChorMTT

module Chor𝔐TT/Definition (This : Chor𝔐TT) where

  private n = This .roles


-- (P : Preorder 𝑖) {{_ : hasDecidableEquality ⟨ P ⟩}} {{_ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)}} where

  P : Preorder _
  P = 𝒫ᶠⁱⁿ (𝔽 n)

  postulate instance
    hasDecidableEquality:P : hasDecidableEquality ⟨ P ⟩
    -- hasDecidableEquality:P = {!!}

  postulate instance
    isProp:≤ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)
    -- isProp:≤ = {!!}

  -- Getting the mode system
  import KamiTheory.Main.Generic.ModeSystem.2Graph.Example2 as 2GraphExample
  -- import KamiTheory.Main.Generic.ModeSystem.2Cell.Example as 2CellExample
  import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition as 2CellDefinition
  import KamiTheory.Main.Generic.ModeSystem.2Cell.Rewriting as 2CellRewriting
  import KamiTheory.Main.Generic.ModeSystem.2Cell.Linear as 2CellLinear
  open 2CellDefinition.2CellDefinition hiding (id)
  open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Example2
  open SendNarrow-ModeSystem P {{it}} {{it}}
  open 2GraphExample.SendNarrow-2Graph P
  open 2CellLinear.2CellLinear SN
  open 2CellRewriting.2CellRewriting SN
  -- open 2CellExample.SendNarrow-2Cells P {{it}} {{it}}



  open import KamiCore.Language.MTT.Definition

  instance
    MTT-Chor : 𝔐TT _
    MTT-Chor = record
      { 𝓂 = Mode SN-ModeSystem
      ; isCategory:𝓂 = isCategory:byModeSystem SN-ModeSystem
      ; is2Category:𝓂 = is2Category:byModeSystem SN-ModeSystem
      }


  -- Instantiating MTT with the 2category generated from the modesystem
  -- open import KamiCore.Typed.Variant.F.Definition3
  open 𝔐TT/Definition {{MTT-Chor}}
    renaming (ModeHom to ModeHom' ; _⊢_ to _⊢'_ ; Ctx to Ctx-MTT)

  instance
    isCategoryData:ModeHom : isCategoryData (Mode SN-ModeSystem) ModeHom'
    isCategoryData:ModeHom = HomData {{isCategory:𝓂 {{MTT-Chor}}}}

  instance
    isCategory:ModeHom : isCategory (Mode SN-ModeSystem)
    isCategory:ModeHom = record { Hom = ModeHom' }

  instance
    is2Category:ModeHom : is2Category ′(Mode SN-ModeSystem)′
    is2Category:ModeHom = is2Category:𝓂 {{MTT-Chor}}

  Param-Chor𝔐TT = Mode SN-ModeSystem

  private variable
    a a₀ b c d : Mode SN-ModeSystem
    μ ν η ω : ModeHom' a b

  private variable
    Γ : Ctx-MTT a
    A B : ⊢Type a

  data isBroadcast : ∀{a b} -> {μ ν : ModeHom' a b} -> μ ⟹ ν -> 𝒰₀ where

  data _⊢_ : Ctx a of MTT-Chor -> Type a of MTT-Chor -> 𝒰₀ where
    var : ∀{μ : _ ⟶ b} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> (α : μ ⟹ η) -> Γ ⊢ A
    tt : Γ ⊢ Unit

    -- modalities
    mod : ∀ μ -> Γ ∙! (μ ⨾ id') ⊢ A -> Γ ⊢ ⟨ A ∣ μ ⨾ id' ⟩
    letmod : ∀(μ : BaseModeHom-SN a b) -> (ν : b ⟶ c)
          -> Γ ∙! ν ⊢ ⟨ A ∣ μ ⨾ id' ⟩
          -> Γ ∙⟮ A ∣ μ ⨾ ν ⟯ ⊢ B
          -> Γ ⊢ B

    letmod' : ∀(μ : BaseModeHom-SN a b)
          -> Γ ⊢ ⟨ A ∣ μ ⨾ id' ⟩
          -> Γ ∙⟮ A ∣ μ ⨾ id' ⟯ ⊢ B
          -> Γ ⊢ B

    -- explicit transformations
    trans : ∀ {μ ν : a ⟶ b} -> (α : μ ⟹ ν) -> isBroadcast α -> Γ ⊢ ⟨ A ∣ μ ⟩ -> Γ ⊢ Tr ⟨ A ∣ ν ⟩

    -- transformations monad
    pure : Γ ⊢ A -> Γ ⊢ Tr A
    seq : ∀{A : ⊢Type a} -> Γ ⊢ Tr A -> Γ ∙⟮ A ∣ id ⟯ ⊢ B -> Γ ⊢ Tr B

    -- functions
    lam : Γ ∙⟮ A ∣ id' ⟯ ⊢ B -> Γ ⊢ ⟮ A ∣ id' ⟯⇒ B

    -- app : Γ ⊢ ⟮ A ∣ μ ⟯⇒ B -> Γ ∙! μ ⊢ A -> Γ ⊢ B
    app : Γ ⊢ ⟮ A ∣ id' ⟯⇒ B -> Γ ⊢ A -> Γ ⊢ B


  -- Our simple type theory

  module _ (a : 𝓂) where
    λChorMTT : STT (ℓ₀ , ℓ₀ , ℓ₀)
    λChorMTT = record
      { Ctx = Ctx a of MTT-Chor
      ; Type = Type a of MTT-Chor
      ; Term = λ Γ A -> Γ ⊢ A
      }




instance
  hasParamSTT:ChorMTT : hasParamSTT ChorMTT
  hasParamSTT:ChorMTT = record
    { Param = Chor𝔐TT/Definition.Param-Chor𝔐TT
    ; _at_ = λ n a -> Chor𝔐TT/Definition.λChorMTT n a
    }





