

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

open import KamiCore.Language.MTT.Definition



F₁ : Chor𝔐TT -> MTT (ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀)
F₁ record { roles = roles } = record
  { 𝓂 = ⊤-𝒰 {ℓ₀}
  ; isCategory:𝓂 = {!!}
  ; is2Category:𝓂 = {!!}
  }


instance
  isReduction:compile-Chor𝔐TT : isReduction (Chor𝔐TT) (𝔐TT) F₁ -- (ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀)) F₁
  isReduction:compile-Chor𝔐TT = record
    { ⟦_⟧-Param = λ _ -> tt
    ; reduce = {!!}
    }

mytest : hasParamSTT ChorMTT
mytest = it

module _ (C : Chor𝔐TT) (D : MTT (ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀)) where
  -- testaa : ∀{a : Param (F₁ C)} -> Ctx (_at_ {𝑗 = (ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀ )} {{it}} (F₁ C) {!!}) -> 𝒰₀ -- Ctx (_at_ {{hasParamSTT:ChorMTT}} C (⟦_⟧-Param isReduction:compile-Chor𝔐TT a))

  testaa : ∀{a : Param (F₁ C)} -> (b : Param D) -> Ctx (F₁ C at a) -> Ctx (C at (⟦_⟧-Param isReduction:compile-Chor𝔐TT {A = C} a))
  testaa {a = a} b Γ = ⟪ reduce isReduction:compile-Chor𝔐TT {A = C} ∣ Γ Ctx⟫
