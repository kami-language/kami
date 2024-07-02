

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorMTT.Translation where

open import Data.List using (drop)

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.TypeTheory.STT.Definition
open import Agora.TypeTheory.ParamSTT.Definition

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



F₂ : Chor𝔐TT 𝑗 -> Min𝔐TT _
F₂ This = Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Private].Super This

module _ (This : Chor𝔐TT 𝑗) where
  open Chor𝔐TT/Definition This
  open [Chor𝔐TT/Definition::Private]
  open [Chor𝔐TT/Definition::Param]

  par-𝔉₂ : Param Super -> Param This
  par-𝔉₂ (x , a) = a


  ⟪𝔉₂∣_Type⟫ : {a : Param This} -> Type (◯ , a) of Super -> Type (a) of This
  ⟪𝔉₂∣_Type⟫ X = X

  ⟪𝔉₂∣_Ctx⟫ : {a : Param This} -> Ctx (◯ , a) of Super -> Ctx a of This
  ⟪𝔉₂∣_Ctx⟫ = {!!}

  ⟪𝔉₂∣_Term⟫ : {a : Param This} -> {Γ : Ctx (◯ , a) of Super} -> {X : Type (◯ , a) of Super}
               -> Γ ⊢ X at (◯ , a) of Super
               -> ⟪𝔉₂∣ Γ Ctx⟫ ⊢ ⟪𝔉₂∣ X Type⟫ at a of This
  ⟪𝔉₂∣_Term⟫ = {!!}

  run-𝔉₂ : ∀{a : Param Super} -> (pa : SubParam Super a) -> Hom-STT (Super at a) (This at (par-𝔉₂ a))
  run-𝔉₂ refl-≡ = record
    { ⟪_∣_Ctx⟫ = ⟪𝔉₂∣_Ctx⟫
    ; ⟪_∣_Type⟫ = ⟪𝔉₂∣_Type⟫
    ; ⟪_∣_Term⟫ = ⟪𝔉₂∣_Term⟫
    }

instance
  isReduction:F₂ : isParamSTTHom (Chor𝔐TT 𝑗) (Min𝔐TT _) F₂
  isReduction:F₂ = record
    { param = par-𝔉₂
    ; runAt = run-𝔉₂
    }

module _ {𝑗} where macro 𝔉₂ = #structureOn (F₂ {𝑗 = 𝑗})

{-
mytest : hasParamSTT ChorMTT
mytest = it

module _ (C : Chor𝔐TT) (D : MinMTT (ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀)) where
  -- testaa : ∀{a : Param (F₂ C)} -> Ctx (_at_ {𝑗 = (ℓ₀ , ℓ₀ , ℓ₀ , ℓ₀ )} {{it}} (F₂ C) {!!}) -> 𝒰₀ -- Ctx (_at_ {{hasParamSTT:ChorMTT}} C (⟦_⟧-Param isReduction:F₂ a))

  testaa : ∀{a : Param (F₂ C)} -> (b : Param D) -> Ctx a of 𝔉₂ C -> Ctx (par 𝔉₂ a) of C -- (C at (param a))
  testaa {a = a} b Γ = ⟪ run 𝔉₂ to C ∣ Γ Ctx⟫

-}
