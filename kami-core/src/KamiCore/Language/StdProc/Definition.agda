

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.StdProc.Definition where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition

open import KamiTheory.Basics hiding (_⋆_)
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Order.StrictOrder.Base

open import KamiCore.Language.ChorProc.Definition


record StdProc : 𝒰₀ where
  field Roles : ℕ

open StdProc public
macro Std𝔓roc = #structureOn StdProc


module Std𝔓roc (This : Std𝔓roc) where

  private
    Super : Chor𝔓roc _
    Super = record { Proc = 𝔽 (This .Roles) }



