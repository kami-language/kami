
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.Kami.Check where

open import Agora.Conventions hiding (n ; _∣_)
open import Agora.Data.Sum.Definition
open import Agora.Data.Fin.Definition
open import Agora.Category.Std.Category.Definition
open import KamiCore.Foreign.Parser.Definition
open import KamiCore.Pipeline.Definition
open import KamiCore.Language.MTT.Definition
open import KamiCore.Language.MTT.Properties
open import KamiTheory.Basics
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding (Mode)
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import Agda.Builtin.String using () renaming (primStringEquality to _==-String_)
open import KamiCore.Language.Kami.Setup
open import KamiCore.Language.Kami.Raw

check-mode : ∀{m} -> {Γ : Ctx} -> {A : 𝔐TT⊢Type m}
             -> (Γ ⊢ A)
             -> Error +-𝒰 (∑ λ k -> ∑ λ (Γ' : 𝔐TT⊢Ctx {k} m) -> Γ' 𝔐TT⊢ A)
check-mode (var x) = {!!}
check-mode (var' x) = {!!}
check-mode (mod μ t) = {!!}
check-mode (letmod t t₁) = {!!}
check-mode (lam x t) = {!!}
check-mode (app t t₁) = {!!}
check-mode (left t) = {!!}
check-mode (right t) = {!!}
check-mode (rec-Either t t₁ t₂) = {!!}
check-mode (rec-Lst t t₁ t₂) = {!!}
check-mode nil = {!!}
check-mode (cons t t₁) = {!!}
check-mode tt = {!!}

