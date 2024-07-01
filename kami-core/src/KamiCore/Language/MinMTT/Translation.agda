
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

--
-- Purpose: Function types don't have modalites,
-- mod introduces always single modalities
--

module KamiCore.Language.MinMTT.Translation where

open import Agora.Conventions hiding (m ; n ; k ; _∣_)
open import Agora.Data.Product.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.TypeTheory.STT.Definition
open import Agora.TypeTheory.ParamSTT.Definition


open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')

open import KamiCore.Language.MTT.Definition
open import KamiCore.Language.MinMTT.Definition


F₁ : Min𝔐TT 𝑖 -> 𝔐TT _
F₁ This = record { ModeTheory = This .ModeTheory }

module _ {𝑖} where
  macro 𝔉₁ = #structureOn (F₁ {𝑖 = 𝑖})

module _ (This : Min𝔐TT 𝑖) where
  private
    Super = F₁ This
    open 𝔐TT/Definition Super

  open [𝔐TT/Definition::Type]

  par-𝔉₁ : Param Super -> Param This
  par-𝔉₁ x = x

  module _ {a : Param Super} where
    ⟪𝔉₁∣_Ctx⟫ : Ctx a of Super -> Ctx a of This
    ⟪𝔉₁∣_Ctx⟫ = {!!}

    ⟪𝔉₁∣_Type⟫ : Type a of Super -> Type a of This
    ⟪𝔉₁∣ ⟨ X ∣ x ⟩ Type⟫ = {!!}
    ⟪𝔉₁∣ Unit Type⟫ = {!!}
    ⟪𝔉₁∣ Tr X Type⟫ = {!!}
    ⟪𝔉₁∣ Either X Y Type⟫ = Either ⟪𝔉₁∣ X Type⟫ ⟪𝔉₁∣ Y Type⟫
    ⟪𝔉₁∣ Lst X Type⟫ = {!!}
    ⟪𝔉₁∣ ⟮ X ∣ x ⟯⇒ X₁ Type⟫ = {!!}



  run-𝔉₁ : {a : Param Super} -> Hom-STT (Super at a) (This at a)
  run-𝔉₁ = record
    { ⟪_∣_Ctx⟫ = ⟪𝔉₁∣_Ctx⟫
    ; ⟪_∣_Type⟫ = {!!}
    ; ⟪_∣_Term⟫ = {!!}
    }



instance
  isReduction:F₁ : isParamSTTHom (Min𝔐TT 𝑖) (𝔐TT _) F₁
  isReduction:F₁ = record
    { param = par-𝔉₁
    ; runAt = run-𝔉₁
    }




