
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.StdProc.Translation where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.TypeTheory.STT.Definition
open import Agora.TypeTheory.ParamSTT.Definition

open import KamiTheory.Basics hiding (_⋆_)
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Order.StrictOrder.Base

open import KamiCore.Language.ChorProc.Definition
open import KamiCore.Language.StdProc.Definition



F₄ : Std𝔓roc -> Chor𝔓roc _
F₄ This = Std𝔓roc/Definition.[Std𝔓roc/Definition::Private].Super This

macro 𝔉₄ = #structureOn F₄

module _ (This : Std𝔓roc) where
  private
    Super = F₄ This
    -- open 𝔐TT/Definition Super
    -- open [𝔐TT/Definition::Type]

  par-𝔉₄ : Param Super -> Param This
  par-𝔉₄ x = x

  -- module _ {a : Param Super} where


  run-𝔉₄ : {a : Param Super} -> Hom-STT (Super at a) (This at a)
  run-𝔉₄ = record
    { ⟪_∣_Ctx⟫ = {!!}
    ; ⟪_∣_Type⟫ = {!!}
    ; ⟪_∣_Term⟫ = {!!}
    }


instance
  isReduction:F₄ : isParamSTTHom Std𝔓roc (Chor𝔓roc _) F₄
  isReduction:F₄ = record
    { param = par-𝔉₄
    ; runAt = run-𝔉₄
    }




