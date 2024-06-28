

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Pipeline.P2-MTT-specific where

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


open import Agora.TypeTheory.Notation

open import KamiCore.Language.MTT.Definition


record ChorMTT : 𝒰₀ where
  field roles : ℕ


module Definition-ChorMTT (n : ℕ) where
  ModeTheory : ⟨ 𝔐TT _ ⟩
  ModeTheory = {!!}

compile-Chor𝔐TT : ChorMTT -> MTT 𝑖
compile-Chor𝔐TT = {!!}

module _ (𝒯 : MTT 𝑖) where
  testaa : ∀{a : Param 𝒯} -> Ctx a of 𝒯 -> {!!}
  testaa = {!!}



