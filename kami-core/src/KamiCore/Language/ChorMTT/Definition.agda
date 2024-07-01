
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorMTT.Definition where

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
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category
import KamiTheory.Main.Generic.ModeSystem.2Graph.Example2 as 2GraphExample
import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition as 2CellDefinition
import KamiTheory.Main.Generic.ModeSystem.2Cell.Rewriting as 2CellRewriting
import KamiTheory.Main.Generic.ModeSystem.2Cell.Linear as 2CellLinear

open import KamiCore.Language.MTT.Definition
open import KamiCore.Language.MinMTT.Definition







record ChorMTT 𝑗 : 𝒰 (𝑗 ⁺) where
  field Roles : Preorder 𝑗
  field {{hasDecidableEquality:Roles}} : hasDecidableEquality ⟨ Roles ⟩
  field {{isProp:≤-Roles}} : ∀{a b : ⟨ Roles ⟩} -> isProp (a ≤ b)

open ChorMTT public

module _ 𝑗 where
  macro Chor𝔐TT = #structureOn (ChorMTT 𝑗)

module Chor𝔐TT/Definition (This : Chor𝔐TT 𝑗) where

  module [Chor𝔐TT/Definition::Param] where
    P : Preorder _
    P = This .Roles

  -- Getting the mode system
    open 2CellDefinition.2CellDefinition hiding (id) public
    open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Example2 public
    open SendNarrow-ModeSystem P {{it}} {{it}} public
    open 2GraphExample.SendNarrow-2Graph P public
    open 2CellLinear.2CellLinear SN public
    open 2CellRewriting.2CellRewriting SN public

    open ModeSystemAs2Category SN-ModeSystem public

    ⊢Param = Mode SN-ModeSystem

    variable
      a a₀ b c d : Mode SN-ModeSystem
      μ ν η ω : ModeHom SN-ModeSystem a b

  open [Chor𝔐TT/Definition::Param]



  module [Chor𝔐TT/Definition::Private] where
    Super : Min𝔐TT _
    Super = record
      { ModeTheory = ′ Mode SN-ModeSystem ′
      ; isSmall = {!!}
      ; split = {!!}
      ; isTargetMode = λ a -> a ≡ ◯
      }
  open [Chor𝔐TT/Definition::Private]


  open Min𝔐TT/Definition Super
  open [Min𝔐TT/Definition::Term] renaming (_⊢_ to _⊢'_)


  -- Import the required definitions from 𝔐TT itself
  open 𝔐TT/Definition [Min𝔐TT/Definition::Private].Super

  --------------------------------------------------------------------
  -- Types
  module [Chor𝔐TT/Definition::Type] where
    open [Min𝔐TT/Definition::Type] public

    variable
      A B : Type (_at_ {{hasParamSTT:MinMTT}} Super (◯ , b))
  open [Chor𝔐TT/Definition::Type]


  --------------------------------------------------------------------
  -- Contexts
  module [Chor𝔐TT/Definition::Ctx] where
    open [𝔐TT/Definition::Ctx] public

    variable
      Γ : Ctx (_at_ {{hasParamSTT:MinMTT}} Super (◯ , b))

    data isCtx₂ : Ctx (◯ , a) of Super -> 𝒰 𝑗 where
      ε : isCtx₂ {a = a} ε
      stepVar : {Γ : Ctx (◯ , ◯) of Super} -> isCtx₂ Γ -> {A : ⊢Type a} -> {μ : a ⟶ ◯} -> isCtx₂ (Γ ∙⟮ A ∣ μ ⟯)
      stepRes : ∀(x : Edge (of SN-ModeSystem .graph) b a) -> {Γ : Ctx (◯ , a) of Super} -> isCtx₂ Γ -> isCtx₂ (Γ ∙! (x ⨾ id))

  open [Chor𝔐TT/Definition::Ctx]




  --------------------------------------------------------------------
  -- Terms
  data isBroadcast : ∀{a b : ⊢Param} -> {μ ν : a ⟶ b} -> μ ⟹ ν -> 𝒰₀ where

  data _⊢_ : Ctx (◯ , a) of Super -> Type (◯ , a) of Super -> 𝒰 𝑗 where
    var : {Γ : Ctx (◯ , a) of Super} -> ∀{μ : _ ⟶ b} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> (α : μ ⟹ η) -> Γ ⊢ A
    tt : Γ ⊢ Unit

    -- modalities
    mod : ∀ μ -> Γ ∙! (μ ⨾ id') ⊢ A -> Γ ⊢ ⟨ A ∣ μ ⨾ id' ⟩
    letmod : ∀(μ : BaseModeHom-SN a b) -> (ν : b ⟶ c)
          -> Γ ∙! ν ⊢ ⟨ A ∣ μ ⨾ id' ⟩
          -> Γ ∙⟮ A ∣ μ ⨾ ν ⟯ ⊢ B
          -> Γ ⊢ B

    letmod' : ∀(μ : BaseModeHom-SN a b)
          -> Γ ⊢ ⟨ A ∣ μ ⨾ id' ⟩
          -> Γ ∙⟮ A ∣ μ ⨾ id' ⟯ ⊢ B
          -> Γ ⊢ B

    -- explicit transformations
    trans : ∀ {μ ν : a ⟶ b} -> (α : μ ⟹ ν) -> isBroadcast α -> Γ ⊢ ⟨ A ∣ μ ⟩ -> Γ ⊢ Tr ⟨ A ∣ ν ⟩

    -- transformations monad
    pure : Γ ⊢ A -> Γ ⊢ Tr A
    seq : ∀{A : ⊢Type a} -> Γ ⊢ Tr A -> Γ ∙⟮ A ∣ id ⟯ ⊢ B -> Γ ⊢ Tr B

    -- functions
    lam : Γ ∙⟮ A ∣ id' ⟯ ⊢ B -> Γ ⊢ ⟮ A ∣ id' ⟯⇒ B

    -- app : Γ ⊢ ⟮ A ∣ μ ⟯⇒ B -> Γ ∙! μ ⊢ A -> Γ ⊢ B
    app : Γ ⊢ ⟮ A ∣ id' ⟯⇒ B -> Γ ⊢ A -> Γ ⊢ B


  -- Our simple type theory

  module _ (a : ⊢Param) where
    λChorMTT : STT _
    λChorMTT = record
      { Ctx = ∑ λ (Γ : Ctx (◯ , a) of Super) -> isCtx₂ Γ
      ; Type = Type (◯ , a) of Super
      ; Term = λ Γ A -> fst Γ ⊢ A
      }


instance
  hasParamSTT:ChorMTT : hasParamSTT (ChorMTT 𝑗)
  hasParamSTT:ChorMTT = record
    { Param = Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Param].⊢Param
    ; SubParam = λ This a -> ⊤-𝒰 {ℓ₀}
    ; _at_ = λ n a -> Chor𝔐TT/Definition.λChorMTT n a
    }




