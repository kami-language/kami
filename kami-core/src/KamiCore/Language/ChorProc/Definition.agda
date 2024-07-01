
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorProc.Definition where

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



record ChorProc 𝑗 : 𝒰 (𝑗 ⁺) where
  field Proc : StrictOrder 𝑗

open ChorProc public


module _ 𝑗 where macro Chor𝔓roc = #structureOn (ChorProc 𝑗)

module Chor𝔓roc/Definition (This : Chor𝔓roc 𝑗) where
  postulate instance
    hasDecidableEquality:P : hasDecidableEquality (𝒫ᶠⁱⁿ (This .Proc))
    isProp:≤-P : ∀{a b : 𝒫ᶠⁱⁿ (This .Proc)} -> isProp (a ≤ b)

  Super : Chor𝔐TT _
  Super = record
    { Roles = 𝒫ᶠⁱⁿ (This .Proc)
    ; hasDecidableEquality:Roles = it
    ; isProp:≤-Roles = it
    }

  open Chor𝔐TT/Definition Super hiding (_⊢_)
  open [Chor𝔐TT/Definition::Param]

  private Mode = Param Super

  module [Chor𝔓roc/Definition::Type] where
    data ⊢Type : Mode -> 𝒰 𝑗

    data ⊢Type where
      ◻ : ⊢Type ◯ -> ⊢Type ▲
      -- [_∣_]◅_ : ⊢Type ◯ -> (𝒫ᶠⁱⁿ (Proc This)) ×-𝒰 List (𝒫ᶠⁱⁿ (Proc This)) -> ⊢Type ▲ -> ⊢Type ▲
      -- _∥_ : ⊢Type ▲ -> ⊢Type ▲ -> ⊢Type ▲
      NN : ∀{m} -> ⊢Type m
      Unit : ∀{m} -> ⊢Type m
      Either : ∀{m} -> ⊢Type m -> ⊢Type m -> ⊢Type m
      _⇒_ : ∀{m} -> ⊢Type m -> ⊢Type m -> ⊢Type m
      _××_ : ∀{m} -> ⊢Type m -> ⊢Type m -> ⊢Type m
      Tr : ∀{m} -> ⊢Type m -> ⊢Type m
      _＠_ : ⊢Type ▲ -> (l : 𝒫ᶠⁱⁿ (Proc This)) -> ⊢Type ◯

    infix 30 _＠_

  open [Chor𝔓roc/Definition::Type]


  module [Chor𝔓roc/Definition::Ctx] where
    data ⊢Ctx : 𝒰 𝑗 where
      ε : ⊢Ctx
      _,[_] : ⊢Ctx -> 𝒫ᶠⁱⁿ (Proc This) -> ⊢Ctx
      _,_ : ⊢Ctx -> ⊢Type ◯ -> ⊢Ctx

  open [Chor𝔓roc/Definition::Ctx]

  module [Chor𝔓roc/Definition::Term] where
    _⊢_ : ⊢Ctx -> ⊢Type ◯ -> 𝒰 𝑗
    _⊢_ = {!!}

  open [Chor𝔓roc/Definition::Term]


  λChorProc : STT _
  λChorProc = record
    { Ctx = ⊢Ctx
    ; Type = ⊢Type ◯
    ; Term = λ Γ A -> Γ ⊢ A
    }

instance
  hasParamSTT:ChorProc : hasParamSTT (ChorProc 𝑗)
  hasParamSTT:ChorProc = record
    { Param = λ _ -> ⊤-𝒰 {ℓ₀}
    ; _at_ = λ This _ -> Chor𝔓roc/Definition.λChorProc This
    }

