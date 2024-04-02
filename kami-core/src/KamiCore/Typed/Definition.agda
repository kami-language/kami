
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Definition where

open import Agora.Conventions hiding (m ; n)

open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition

open ModeSystem

module _ {M : ModeSystem 𝑖} where

  private variable
    m n : 0Cell (graph M)

  data ⊢Type_ : 0Cell (graph M) -> 𝒰 𝑖 where
    ⟨_∣_⟩ : ⊢Type m -> 1Cell (graph M) m n -> ⊢Type n
    NN : ⊢Type m
    ⟨_∣_⟩⇒_ : ⊢Type m -> 1Cell (graph M) m n -> ⊢Type n -> ⊢Type n




