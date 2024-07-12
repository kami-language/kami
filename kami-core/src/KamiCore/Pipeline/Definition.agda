
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Pipeline.Definition where

open import Agora.Conventions hiding (m ; n ; k ; _∣_)
open import Agora.Category.Std.Category.Definition
open import Agora.TypeTheory.ParamSTT.Definition
open import Agora.TypeTheory.ParamSTT.Instance.Category
open import Agora.Category.Std.2Category.Definition

open import KamiCore.Language.MTT.Definition
open import KamiCore.Language.MinMTT.Definition
open import KamiCore.Language.MinMTT.Translation
open import KamiCore.Language.ChorMTT.Definition
open import KamiCore.Language.ChorMTT.Translation
open import KamiCore.Language.ChorProc.Definition
open import KamiCore.Language.ChorProc.Translation
open import KamiCore.Language.StdProc.Definition
open import KamiCore.Language.StdProc.Translation

open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')


-- The inference & typechecking pipeline



-- The whole compilation pipeline
𝔉 : ParamSTTHom (Std𝔓roc) (𝔐TT _)
𝔉 = 𝔉₄ ◆-ParamSTT
    𝔉₃ ◆-ParamSTT
    𝔉₂ ◆-ParamSTT
    𝔉₁

----------------------------------------------------------
-- Examples

module Generic (n : ℕ) where
  Target : StdProc
  Target = record { Roles = n }

  Chor : ChorMTT _
  Chor = ⟨ 𝔉₄ ◆-ParamSTT 𝔉₃ ⟩ Target

  -- open Chor𝔐TT/Definition This
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Private] Chor
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Param] Chor

  Source : MTT _
  Source = ⟨ 𝔉 ⟩ Target

  open 𝔐TT/Definition Source
  open [𝔐TT/Definition::Type] --  renaming (⊢Type to 𝔐TT⊢Type)
  open [𝔐TT/Definition::Ctx] -- renaming (⊢Ctx to 𝔐TT⊢Ctx)
  open [𝔐TT/Definition::Term] -- renaming (_⊢_ to _𝔐TT⊢_ ; _⊢Var⟮_∣_⇒_⟯ to _𝔐TT⊢Var⟮_∣_⇒_⟯ ; _⊢Var⟮_∣_⇒∼_⟯ to _𝔐TT⊢Var⟮_∣_⇒∼_⟯)
  open Variables/Mode
  open Variables/Hom
  open Variables/Ctx
  open Variables/Type


  pattern _＠_ A u = ⟨ A ∣ `＠` u ⨾ id' ⟩
  pattern ◻ X = ⟨ X ∣ `[]` ⨾ id' ⟩

  infix 50 _＠_

  pattern Λ_ t = lam t
  pattern letmod_and_ t s = letmod id' t s
  pattern letmod[_]_and_ μ t s = letmod μ t s

  infix 10 Λ_
  pattern _∘_ t s = app t s

  pattern _⇒_ A B = ⟮ A ∣ id' ⟯⇒ B
  infixr 40 _⇒_

  _∘'_ : Γ ⊢ ⟮ A ∣ id' ⟯⇒ B -> Γ ⊢ A -> Γ ⊢ B
  _∘'_ = {!!}

  ev : ∀ (u : ⟨ P ⟩) -> `[]` ⨾ `＠` u ⨾ id' ⟹ id'
  ev = {!!}

  stage : ∀ (u : ⟨ P ⟩) -> id ⟹ `＠` u ⨾ `[]` ⨾ id'
  stage = {!!}
  



