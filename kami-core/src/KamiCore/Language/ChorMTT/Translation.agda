

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorMTT.Translation where

open import Data.List using (drop)

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.TypeTheory.Notation

open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Basics hiding (_⋆_)

open import KamiCore.Language.MinMTT.Definition
open import KamiCore.Language.ChorMTT.Definition



F₂ : Chor𝔐TT -> MinMTT (ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀)
F₂ record { roles = roles } = record { ModeTheory = ⊤-𝒰 {ℓ₀} since {!!}  ; isSmall = {!!} ; split = {!!} }


instance
  isReduction:F₂ : isReduction (Chor𝔐TT) (Min𝔐TT _) F₂ -- (ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀)) F₂
  isReduction:F₂ = record
    { param = λ _ -> {!!}
    ; runAt = {!!}
    }

macro 𝔉₂ = #structureOn F₂

mytest : hasParamSTT ChorMTT
mytest = it

module _ (C : Chor𝔐TT) (D : MinMTT (ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀)) where
  -- testaa : ∀{a : Param (F₂ C)} -> Ctx (_at_ {𝑗 = (ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀ )} {{it}} (F₂ C) {!!}) -> 𝒰₀ -- Ctx (_at_ {{hasParamSTT:ChorMTT}} C (⟦_⟧-Param isReduction:F₂ a))

  testaa : ∀{a : Param (F₂ C)} -> (b : Param D) -> Ctx a of 𝔉₂ C -> Ctx (par 𝔉₂ a) of C -- (C at (param a))
  testaa {a = a} b Γ = ⟪ run 𝔉₂ to C ∣ Γ Ctx⟫
