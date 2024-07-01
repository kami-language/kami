

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.StdProc.Definition where

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


record StdProc : 𝒰₀ where
  field Roles : ℕ

open StdProc public
macro Std𝔓roc = #structureOn StdProc


module Std𝔓roc/Definition (This : Std𝔓roc) where

  module [Std𝔓roc/Definition::Private] where
    n = This .Roles

    Super : Chor𝔓roc _
    Super = record { Proc = 𝔽 (This .Roles) }

  open [Std𝔓roc/Definition::Private]


  module [Std𝔓roc/Definition::Type] where

    data LType : 𝒰₀

    ⊢Type : 𝒰₀
    ⊢Type = 𝔽 n -> LType

    data LType where
      _⇒_ : LType -> LType -> LType
      ◻ : ⊢Type -> LType
      Unit : LType
      _××_ : LType -> LType -> LType

    variable
      A B : LType
      X : ⊢Type

  open [Std𝔓roc/Definition::Type]

  module [Std𝔓roc/Definition::Ctx] where

    data LCtx : 𝒰₀ where
      ε : LCtx
      _,_ : LCtx -> LType -> LCtx

    ⊢Ctx : 𝒰₀
    ⊢Ctx = 𝔽 n -> LCtx

    variable
      Γ : LCtx

  open [Std𝔓roc/Definition::Ctx]


  module [Std𝔓roc/Definition::Term] where
    data _⊢Var_Locally : LCtx -> LType -> 𝒰₀ where
      zero : Γ , A ⊢Var A Locally
      suc : Γ ⊢Var A Locally -> Γ , B ⊢Var A Locally

    data _⊢_Locally : LCtx -> LType -> 𝒰₀ where
      var : Γ ⊢Var A Locally -> Γ ⊢ A Locally
      lam : Γ , A ⊢ B Locally -> Γ ⊢ A ⇒ B Locally
      box : (∀ n -> Γ ⊢ X n Locally) -> Γ ⊢ ◻ X Locally
      proj : Γ ⊢ ◻ X Locally -> ∀ n -> Γ ⊢ X n Locally
      _,_ : Γ ⊢ A Locally -> Γ ⊢ B Locally -> Γ ⊢ A ×× B Locally
      tt : Γ ⊢ Unit Locally

    _⊢_ : ⊢Ctx -> ⊢Type -> 𝒰₀
    _⊢_ Γ X = ∀ n -> Γ n ⊢ X n Locally

  open [Std𝔓roc/Definition::Term]


  wk : Γ ⊢ A Locally -> Γ , B ⊢ A Locally
  wk = {!!}


  λStdProc : STT _
  λStdProc = record
    { Ctx = ⊢Ctx
    ; Type = ⊢Type
    ; Term = λ Γ A -> Γ ⊢ A
    }

instance
  hasParamSTT:StdProc : hasParamSTT (Std𝔓roc)
  hasParamSTT:StdProc = record
    { Param = λ This -> ⊤-𝒰 {ℓ₀}
    ; _at_ = λ This _ -> Std𝔓roc/Definition.λStdProc This
    }

