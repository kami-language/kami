
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.StdProc.Translation where

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
open import KamiCore.Language.ChorProc.Properties
open import KamiCore.Language.StdProc.Definition



F₄ : Std𝔓roc -> Chor𝔓roc _
F₄ This = Std𝔓roc/Definition.[Std𝔓roc/Definition::Private].Super This

macro 𝔉₄ = #structureOn F₄

module _ (This : Std𝔓roc) where
  open Std𝔓roc/Definition This
  open [Std𝔓roc/Definition::Private] using (Super)
  open [Std𝔓roc/Definition::Type] hiding (A ; B)
  open [Std𝔓roc/Definition::Ctx] hiding (Γ)
  open [Std𝔓roc/Definition::Term]

  open Chor𝔓roc/Definition Super hiding (Super)
  open [Chor𝔓roc/Definition::Param]
  open [Chor𝔓roc/Definition::Type] renaming (⊢Type to Chor𝔓roc⊢Type)
  open [Chor𝔓roc/Definition::Ctx] renaming (⊢Ctx to Chor𝔓roc⊢Ctx)
  open [Chor𝔓roc/Definition::Term] renaming (_⊢_ to _Chor𝔓roc⊢_)
  open Chor𝔓roc/Properties Super

  par-𝔉₄ : Param Super -> Param This
  par-𝔉₄ x = x

  --------------------------------------------------------------------
  -- Types

  ⟦_⟧-FType : Chor𝔓roc⊢Type ◯ -> ⊢Type

  {-# TERMINATING #-}
  ⟦_⟧-LType : Chor𝔓roc⊢Type ▲ -> LType
  ⟦ ◻ T ⟧-LType = ◻ ⟦ T ⟧-FType
  ⟦ NN ⟧-LType = {!!}
  ⟦ Unit ⟧-LType = Unit
  ⟦ Either T S ⟧-LType = {!!}
  ⟦ T ⇒ S ⟧-LType = ⟦ T ⟧-LType ⇒ ⟦ S ⟧-LType
  ⟦ T ×× S ⟧-LType = {!!}
  ⟦ Tr T ⟧-LType = {!!}
  ⟦ Lst T ⟧-LType = {!!}

  ⟦_⟧-FType X n = ⟦ π-Type X (⦗ n ⦘ , []) ⟧-LType

  ⟪𝔉₁∣_Type⟫ : Chor𝔓roc⊢Type ◯ -> ⊢Type
  ⟪𝔉₁∣_Type⟫ = ⟦_⟧-FType

  -- End Types
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Ctx

  ⟦_⟧-LCtx : ∀ {Δ : Chor𝔓roc⊢Ctx} -> ∀{p} -> isLocal p Δ -> LCtx
  ⟦_⟧-LCtx ε = ε
  ⟦_⟧-LCtx (P , A) = ⟦ P ⟧-LCtx , ⟦ A ⟧-LType
  ⟦_⟧-LCtx (stepRes P) = ⟦ P ⟧-LCtx

  ⟦_⟧-FCtx : ∀ (Γ : Chor𝔓roc⊢Ctx) -> ⊢Ctx
  ⟦_⟧-FCtx Γ n = ⟦ local-Proof (π-Ctx-Proof Γ (⦗ n ⦘ ∷ [])) ⟧-LCtx

  ⟪𝔉₁∣_Ctx⟫ : Chor𝔓roc⊢Ctx -> ⊢Ctx
  ⟪𝔉₁∣_Ctx⟫ = ⟦_⟧-FCtx


  -- End Ctx
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Variables

  tπ' : ∀{X B p Γ} -> π X ∣ p , [] ↦ B Type -> Γ ⊢ ⟦ ◻ X ⟧-LType Locally -> Γ ⊢ ⟦ B ⟧-LType Locally
  tπ' {X = X} {p = p} P t with unique-π P (π-Type-Proof X (p , []))
  ... | refl-≡ = {!proj t !} -- proj t p

  tω : ∀{A B ps Γ} -> ω A ∣ ps ↦ B Type -> Γ ⊢ ⟦ A ⟧-LType Locally -> Γ ⊢ ⟦ B ⟧-LType Locally

  tπ : ∀{X B p ps Γ} -> π X ∣ p , ps ↦ B Type -> Γ ⊢ ⟦ ◻ X ⟧-LType Locally -> Γ ⊢ ⟦ B ⟧-LType Locally
  tπ {X = X} {p = p} P t = tω (split-π P) (tπ' (π-Type-Proof X (p , [])) t)

  tω done t = t
  tω (proj-◻ x) t = {!!} -- tπ x t
  tω Unit t = t

  tv  : ∀{Δ A p ps} -> (Δp : isLocal p Δ) -> Δ ⊢Var A GlobalFiber[ p ∷ ps ] -> ⟦ Δp ⟧-LCtx ⊢ ⟦ A ⟧-LType Locally
  tv (Δp , A) none = {!!} -- tϕ x₁ (tω x₂ (var zero))
  tv (Δp , A) (zero p q) = {!!} -- tϕ x₁ (tω x₂ (var zero))
  tv (Δp , A) (suc v) = let x = tv Δp v in wk x
  tv (stepRes Δp) (res v) = let x = tv Δp v in x

  -- End Variables
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Term

  ta : ∀ {Γ X} -> Γ ⊢ X GlobalFibered[ {!!} ] -> ⟦ Γ ⟧-FCtx ⊢ ⟦ X ⟧-FType


  tr : ∀ {Δ p A} -> (Δp : isLocal ⦗ p ⦘ Δ) -> Δ ⊢ A GlobalFiber[ p ] -> ⟦ Δp ⟧-LCtx ⊢ ⟦ A ⟧-LType Locally
  tr Δp (var v) = tv Δp v
  tr Δp (recv x) = {!!}
  tr Δp (send v t) = {!!}
  tr Δp (extern t) = {!!}
  tr Δp (box' x) = {!!}
  tr Δp (pure t) = {!!}
  tr Δp (seq t t₁) = {!!}
  tr Δp (lam t) = {!!}
  tr Δp (app t t₁) = {!!}
  tr Δp tt = {!!}
  tr Δp (left t) = {!!}
  tr Δp (right t) = {!!}
  tr Δp (either t t₁ t₂) = {!!}
  tr Δp [] = {!!}
  tr Δp (t ∷ t₁) = {!!}
  tr Δp (rec-Lst t t₁ t₂) = {!!}

  ta {Γ = Γ} {X} ts n = tr (local-Proof (π-Ctx-Proof Γ _)) (⟨ ts ⟩ n {!!} (π-Type-Proof X _) (π-Ctx-Proof Γ _))


  ⟪𝔉₁∣_Term⟫ : ∀ {Γ X} -> Γ ⊢ X GlobalFibered[ {!!} ] -> ⟦ Γ ⟧-FCtx ⊢ ⟦ X ⟧-FType
  ⟪𝔉₁∣_Term⟫ = ta

  -- End Term
  --------------------------------------------------------------------


  run-𝔉₄ : {a : Param Super} (p : SubParam Super a) -> Hom-STT (Super at a) (This at a)
  run-𝔉₄ p = record
    { ⟪_∣_Ctx⟫ = ⟪𝔉₁∣_Ctx⟫
    ; ⟪_∣_Type⟫ = ⟪𝔉₁∣_Type⟫
    ; ⟪_∣_Term⟫ = ⟪𝔉₁∣_Term⟫
    }


instance
  isReduction:F₄ : isParamSTTHom Std𝔓roc (Chor𝔓roc _) F₄
  isReduction:F₄ = record
    { param = par-𝔉₄
    ; runAt = run-𝔉₄
    }




