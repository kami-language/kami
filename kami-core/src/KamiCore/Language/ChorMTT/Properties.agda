
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorMTT.Properties where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import Data.List using (drop)

open import KamiCore.Language.ChorMTT.Definition
open import KamiCore.Language.MinMTT.Definition
open import KamiCore.Language.MinMTT.Properties


module Chor𝔐TT/Properties (This : Chor𝔐TT 𝑗) where
  -- open Chor𝔐TT/Definition This
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Private] This
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Param] This
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Ctx] This
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Term] This
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Type] This

  open Min𝔐TT/Properties Super
  open Min𝔐TT/Definition Super
  open [Min𝔐TT/Definition::Private] using (_⟶ₛ_)

  ----------------------------------------------------------
  -- Ctx₂ proofs
  ----------------------------------------------------------

  -- stepsVar : ∀{μ : } -> isCtx₂ Γ -> isCtx₂ (Γ ∙!* μ)
  stepsRes : {Γ : ⊢Ctx c} -> (μs : Path _⟶ₛ_ b c)
             -> isCtx₂ Γ -> isCtx₂ (Γ ∙!* μs)
  stepsRes = {!!}


  ----------------------------------------------------------
  -- Working with the context
  --
  -- Various proofs which let us transfer terms from
  -- some context to a similar one.
  ----------------------------------------------------------
  --
  com-restr-single : ∀{x : BaseModeHom-PolySR a b} -> ∀{xp} -> {A : ⊢Type c}
                    -> {B : ⊢Type a}
                    -> (Γ ∙! ((x ⨾ id') , xp)) ∙⟮ A ∣ μ ⟯ ⊢ B
                    -> Γ ∙⟮ A ∣ μ ◆ (x ⨾ id') ⟯ ∙! ((x ⨾ id') , xp) ⊢ B
  com-restr-single = {!!}

  com⁻¹-restr-single : ∀{x : BaseModeHom-PolySR a b} -> ∀{xp} -> {A : ⊢Type c}
                    -> {B : ⊢Type a}
                    -> Γ ∙⟮ A ∣ μ ◆ (x ⨾ id') ⟯ ∙! ((x ⨾ id') , xp) ⊢ B
                    -> (Γ ∙! ((x ⨾ id') , xp)) ∙⟮ A ∣ μ ⟯ ⊢ B
  com⁻¹-restr-single = {!!}

  id-annotate : {μ : a ⟶ b} -> Γ ∙⟮ A ∣ μ ⟯ ⊢ B -> Γ ∙⟮ Mod-Type (split Super μ) A ∣ id' ⟯ ⊢ B
  id-annotate = {!!}




