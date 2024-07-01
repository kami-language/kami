

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorProc.Translation where

open import Data.List using (drop)

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
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding (Mode)
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category

open import KamiCore.Language.ChorMTT.Definition
open import KamiCore.Language.ChorProc.Definition



F₃ : Chor𝔓roc 𝑗 -> Chor𝔐TT _
F₃ This = Chor𝔓roc/Definition.Super This


module _ (This : Chor𝔓roc 𝑗) where
  open Chor𝔓roc/Definition This

  par-𝔉₃ : Param Super -> Param This
  par-𝔉₃ _ = tt




instance
  isReduction:F₃ : isParamSTTHom (Chor𝔓roc 𝑗) (Chor𝔐TT _) F₃
  isReduction:F₃ = record
    { param = par-𝔉₃
    ; runAt = {!!}
    }

module _ 𝑗 where macro 𝔉₃ = #structureOn (F₃ {𝑗 = 𝑗})


