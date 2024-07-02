

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorProc.Properties where

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




module Chor𝔓roc/Properties (This : Chor𝔓roc 𝑗) where
  open Chor𝔓roc/Definition This
  open [Chor𝔓roc/Definition::Param]
  open [Chor𝔓roc/Definition::Type]
  open [Chor𝔓roc/Definition::Ctx]
  open [Chor𝔓roc/Definition::Term]



  --------------------------------------------------------------
  -- Special properties of the ChorProc calculus
  --------------------------------------------------------------
  --
  commute-＠-Exp : ∀ ps -> Γ ⊢ ((A ＠ ps) ⇒ (B ＠ ps)) GlobalFibered[ qs ] -> Γ ⊢ (A ⇒ B) ＠ ps GlobalFibered[ qs ]
  ⟨ commute-＠-Exp ps t ⟩ q q∈qs (proj-＠ q∈ps done) Γp =
    let t' = (⟨ t ⟩ q q∈qs (proj-＠ q∈ps done ⇒ proj-＠ q∈ps done) Γp)
    in t'
  ⟨ commute-＠-Exp ps t ⟩ q q∈qs (proj-＠-≠ x) Γp = tt


  --------------------------------------------------------------
  -- Reproducing global term constructors, locally
  --------------------------------------------------------------
  --

  lam-GlobalFibered : Γ , X ⊢ Y GlobalFibered[ ps ] -> Γ ⊢ X ⇒ Y GlobalFibered[ ps ]
  lam-GlobalFibered t = incl λ {p p∈ps (X↦A ⇒ Y↦B) Γ↦Δ -> lam (⟨ t ⟩ p p∈ps Y↦B (Γ↦Δ , X↦A)) }





