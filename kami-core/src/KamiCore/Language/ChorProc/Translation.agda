

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorProc.Translation where

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
open import KamiCore.Language.ChorProc.Definition




F₃ : Chor𝔓roc 𝑗 -> Chor𝔐TT _
F₃ This = Chor𝔓roc/Definition.Super This


module _ (This : Chor𝔓roc 𝑗) where
  open Chor𝔓roc/Definition This
  open [Chor𝔓roc/Definition::Type]
  open [Chor𝔓roc/Definition::Ctx]
  open [Chor𝔓roc/Definition::Term]

  open Chor𝔐TT/Definition Super
  open [Chor𝔐TT/Definition::Param]
  open [Chor𝔐TT/Definition::Type] hiding (⊢Type)
  open [Chor𝔐TT/Definition::Ctx] renaming (⊢Ctx to 𝔐TT⊢Ctx)
  open [Chor𝔐TT/Definition::Term] renaming (_⊢_ to _𝔐TT⊢_)

  par-𝔉₃ : Param Super -> Param This
  par-𝔉₃ _ = tt



  --------------------------------------------------------------------
  -- Types

  F-Type : (a ⟶ b) -> ⊢Type a -> ⊢Type b
  F-Type id' x = x
  F-Type (`＠` U ⨾ μ) x = F-Type μ (x ＠ U)
  F-Type (`[]` ⨾ μ) x = F-Type μ (◻ x)

  F-Type-map : ∀{X} {μ : a ⟶ b} {ν : b ⟶ c} -> F-Type (μ ◆ ν) X ≡ F-Type ν (F-Type μ X)
  F-Type-map {μ = id'} = refl-≡
  F-Type-map {μ = `＠` U ⨾ μ} = F-Type-map {μ = μ}
  F-Type-map {μ = `[]` ⨾ μ} = F-Type-map {μ = μ}

  ⦋_⦌-Type : Type a of Super -> ⊢Type a
  ⦋ ⟨ X ∣ μ ⟩ ⦌-Type = F-Type (fst μ) ⦋ X ⦌-Type
  ⦋ Unit ⦌-Type = Unit
  ⦋ Tr X ⦌-Type = Tr ⦋ X ⦌-Type
  ⦋ X ⇒ Y ⦌-Type = ⦋ X ⦌-Type ⇒ ⦋ Y ⦌-Type
  ⦋ Either x x₁ ⦌-Type = {!!}
  ⦋ Lst x ⦌-Type = {!!}

  ⟪𝔉₃∣_Type⟫ : {a : Param Super} -> Type a of Super -> Type tt of This
  ⟪𝔉₃∣_Type⟫ {a = ▲ x} X = ⦋ X ⦌-Type ＠ x
  ⟪𝔉₃∣_Type⟫ {a = ◯} X = ⦋ X ⦌-Type


  -- End Types
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Contexts

  TargetCtx : Param Super -> 𝒰 _
  TargetCtx (▲ _) = ⊢Ctx × ⟨ P ⟩
  TargetCtx ◯ = ⊢Ctx

  addRestr : (μ : a ⟶ b) -> TargetCtx b -> TargetCtx a
  addRestr id' Γ = Γ
  addRestr (`＠` U ⨾ μ) Γ = addRestr μ Γ , U
  addRestr (`[]` ⨾ μ) Γ = let Γ' , U = addRestr μ Γ in Γ' ,[ U ]

  transl-Ctx : (Γ : 𝔐TT⊢Ctx {◯} a) -> isCtx₂ Γ -> TargetCtx a
  transl-Ctx (Γ ∙⟮ x ∣ μ ⟯) (stepVar Γp) = transl-Ctx Γ Γp , F-Type μ ⦋ x ⦌-Type
  transl-Ctx (_∙!_ Γ μ) (stepRes _ Γp) = addRestr (fst μ) (transl-Ctx Γ Γp)
  transl-Ctx ε Γp = ε

  forget : TargetCtx a -> ⊢Ctx
  forget {a = ◯} Γ = Γ
  forget {a = ▲ x} Γ = fst Γ

  ⟪𝔉₃∣_Ctx⟫ : Ctx a of Super -> Ctx tt of This
  ⟪𝔉₃∣_Ctx⟫ (Γ , Γp) = forget (transl-Ctx Γ Γp)

  -- End Contexts
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Terms
  transl-Term-▲ : ∀{ps i} -> (Γ : 𝔐TT⊢Ctx {◯} ◯) -> (Γp : isCtx₂ Γ)
            -> ∀{A} -> Γ ∙! (`＠` i ⨾ id') 𝔐TT⊢ A
            -> transl-Ctx Γ Γp  ⊢ (⦋ A ⦌-Type ＠ i) GlobalFibered[ ps ]
  transl-Term-▲ = {!!}

  transl-Term-◯ : ∀{ps} -> (Γ : 𝔐TT⊢Ctx {◯} ◯) -> (Γp : isCtx₂ Γ)
            -> ∀{A} -> Γ 𝔐TT⊢ A
            -> transl-Ctx Γ Γp  ⊢ ⦋ A ⦌-Type GlobalFibered[ ps ]
  transl-Term-◯ = {!!}

  ⟪𝔉₃∣_Term⟫ : {a : Param Super} -> {Γ : Ctx a of Super} -> {X : Type a of Super}
               -> Γ ⊢ X at a of Super
               -> ⟪𝔉₃∣ Γ Ctx⟫ ⊢ ⟪𝔉₃∣ X Type⟫ at tt of This
  ⟪𝔉₃∣_Term⟫ {a = ▲ U} {Γ = (Γ ∙! (`＠` U ⨾ id')) , stepRes (`＠` U) Γp} {X} t = transl-Term-▲ Γ Γp t
  ⟪𝔉₃∣_Term⟫ {a = ◯} {Γ = Γ , Γp} {X} t = transl-Term-◯ Γ Γp t

  -- End Terms
  --------------------------------------------------------------------

  module _ {a : Param Super} where


  run-𝔉₃ : ∀{a : Param Super} -> (pa : SubParam Super a) -> Hom-STT (Super at a) (This at tt)
  run-𝔉₃ pa = record
    { ⟪_∣_Ctx⟫ = ⟪𝔉₃∣_Ctx⟫
    ; ⟪_∣_Type⟫ = ⟪𝔉₃∣_Type⟫
    ; ⟪_∣_Term⟫ = ⟪𝔉₃∣_Term⟫
    }


{-
instance
  isReduction:F₃ : isParamSTTHom (Chor𝔓roc 𝑗) (Chor𝔐TT _) F₃
  isReduction:F₃ = record
    { param = par-𝔉₃
    ; runAt = run-𝔉₃
    }

module _ {𝑗} where macro 𝔉₃ = #structureOn (F₃ {𝑗 = 𝑗})
-}

