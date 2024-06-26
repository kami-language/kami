
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Pipeline.Definition where

open import Agora.Conventions hiding (m ; n ; k ; _∣_)
open import Agora.Category.Std.Category.Definition
open import Agora.TypeTheory.ParamSTT.Definition
open import Agora.TypeTheory.ParamSTT.Instance.Category

open import KamiCore.Language.MTT.Definition
open import KamiCore.Language.MinMTT.Definition
open import KamiCore.Language.MinMTT.Translation
open import KamiCore.Language.ChorMTT.Definition
open import KamiCore.Language.ChorMTT.Translation
open import KamiCore.Language.ChorProc.Definition
open import KamiCore.Language.ChorProc.Translation
open import KamiCore.Language.StdProc.Definition
open import KamiCore.Language.StdProc.Translation


-- The inference & typechecking pipeline



-- The whole compilation pipeline
𝔉 : ParamSTTHom (Std𝔓roc) (𝔐TT _)
𝔉 = 𝔉₄ ◆-ParamSTT
    𝔉₃ ◆-ParamSTT
    𝔉₂ ◆-ParamSTT
    𝔉₁





