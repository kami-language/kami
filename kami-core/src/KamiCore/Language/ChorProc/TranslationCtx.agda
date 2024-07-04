

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorProc.TranslationCtx where

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
open import KamiTheory.Data.UniqueSortedList.NonEmpty
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding (Mode)
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category

open import KamiCore.Language.ChorMTT.Definition
open import KamiCore.Language.ChorMTT.Properties
open import KamiCore.Language.ChorProc.Definition
open import KamiCore.Language.ChorProc.Properties
open import KamiCore.Language.ChorProc.Properties2
open import KamiCore.Language.ChorProc.Properties3




module Chor𝔓roc/TranslationCtx (This : Chor𝔓roc 𝑗) where
  open Chor𝔓roc/Definition This
  open [Chor𝔓roc/Definition::Param]
  open [Chor𝔓roc/Definition::Type]
  open [Chor𝔓roc/Definition::Ctx]
  open [Chor𝔓roc/Definition::Term]
  open Chor𝔓roc/Properties This
  open Chor𝔓roc/Properties2 This
  open Chor𝔓roc/Properties3 This

  open Chor𝔐TT/Definition Super
  open [Chor𝔐TT/Definition::Type] renaming (⊢Type to Chor𝔐TT⊢Type)
  open [Chor𝔐TT/Definition::Ctx] renaming (⊢Ctx to Chor𝔐TT⊢Ctx)
  open [Chor𝔐TT/Definition::Term] renaming (_⊢_ to _Chor𝔐TT⊢_)
  open Chor𝔐TT/Properties Super


  -- TODO: currently these definitions
  -- have to be stated in multiple places,
  -- because otherwise the inference doesn't work.
  -- Merge in a single place.
  private
    pattern []ₛ = (`[]` ⨾ id' , incl `[]`)
    pattern ＠ₛ U  = (`＠` U ⨾ id' , incl (`＠` _))

  --------------------------------------------------------------------
  -- Types


  ⦋_⦌-Type : Type a of Super -> ⊢Type ⟦ a ⟧-Mode
  ⦋ ⟨ X ∣ μ ⟩ ⦌-Type = F-Type (fst μ) ⦋ X ⦌-Type
  ⦋ Unit ⦌-Type = Unit
  ⦋ Tr X ⦌-Type = Tr ⦋ X ⦌-Type
  ⦋ X ⇒ Y ⦌-Type = ⦋ X ⦌-Type ⇒ ⦋ Y ⦌-Type
  ⦋ Either X Y ⦌-Type = Either ⦋ X ⦌-Type ⦋ Y ⦌-Type
  ⦋ Lst X ⦌-Type = Lst ⦋ X ⦌-Type

  ⟪𝔉₃∣_Type⟫ : {a : Param Super} -> Type a of Super -> Type tt of This
  ⟪𝔉₃∣_Type⟫ {a = ▲ x} X = ⦋ X ⦌-Type ＠ x
  ⟪𝔉₃∣_Type⟫ {a = ◯} X = ⦋ X ⦌-Type

  -- End Types
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Types commutation proofs
  -- End Types commutation proofs
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Contexts

  transl-Ctx : (Γ : Chor𝔐TT⊢Ctx {◯} a) -> isCtx₂ Γ -> TargetCtx ⟦ a ⟧-Mode
  transl-Ctx (Γ ∙⟮ x ∣ μ ⟯) (stepVar Γp) = transl-Ctx Γ Γp , F-Type μ ⦋ x ⦌-Type
  transl-Ctx (_∙!_ Γ μ) (stepRes _ Γp) = addRestr (fst μ) (transl-Ctx Γ Γp)
  transl-Ctx ε Γp = ε

  transl-Ctx' : (Γ : Chor𝔐TT⊢Ctx {◯} a) -> isCtx₂ Γ -> ⊢Ctx
  transl-Ctx' Γ Γp = forget (transl-Ctx Γ Γp)

  ⟪𝔉₃∣_Ctx⟫ : Ctx a of Super -> Ctx tt of This
  ⟪𝔉₃∣_Ctx⟫ (Γ , Γp) = forget (transl-Ctx Γ Γp)

  -- End Contexts
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Context commutation proofs


  cong-,[] : ∀{Γ Δ : TargetCtx ▲} -> Γ ≡ Δ -> fst Γ ,[ snd Γ ] ≡ fst Δ ,[ snd Δ ]
  cong-,[] refl-≡ = refl-≡


  commute-transl,addRestr : {ν : a ⟶ ▲ U} -> ∀{Γ Γp} -> transl-Ctx
     (Γ ∙! ＠ₛ U ∙!* split-Min𝔐TT ν) (stepsRes _ (stepRes _ Γp))
     ≡ addRestr ν (transl-Ctx Γ Γp , U)
  commute-transl,addRestr {ν = id'} = refl-≡
  commute-transl,addRestr {ν = `＠` U ⨾ ν} = cong-≡ (_, U) (commute-transl,addRestr {ν = ν})
  commute-transl,addRestr {ν = `[]` ⨾ ν} = cong-,[] (commute-transl,addRestr {ν = ν})

  commute-transl,addRestr-2 : ∀{ν : a ⟶ ◯} -> ∀{Γ Γp} -> transl-Ctx
     (Γ ∙!* split-Min𝔐TT ν) (stepsRes _ Γp)
     ≡ addRestr ν (transl-Ctx Γ Γp)
  commute-transl,addRestr-2 {ν = id'} = refl-≡
  commute-transl,addRestr-2 {ν = `＠` U ⨾ ν} = cong-≡ (_, U) (commute-transl,addRestr-2 {ν = ν})
  commute-transl,addRestr-2 {ν = `[]` ⨾ ν} = cong-,[] (commute-transl,addRestr-2 {ν = ν})


  -- End Context commutation proofs
  --------------------------------------------------------------------
