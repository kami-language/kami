
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Definition where

open import Agora.Conventions hiding (m ; n)
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition

open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition

open import Data.Vec

open 2CellDefinition

open ModeSystem

module _ {M : ModeSystem 𝑖} where

  private variable
    m n : 0Cell (graph M)

  -- data PreType : 0Cell (graph M) -> 𝒰 (𝑖 ⁺) where

  --   -- the usual modal type
  --   ⟨_∣_⟩ : PreType m -> 1Cell (graph M) m n -> PreType n

  --   -- natural numbers
  --   NN : PreType m

  --   -- functions
  --   ⟨_∣_⟩⇒_ : PreType m -> 1Cell (graph M) m n -> PreType n -> PreType n



  data ⊢Type_ : 0Cell (graph M) -> 𝒰 𝑖 where
    -- the usual modal type
    ⟨_∣_⟩ : ⊢Type m -> 1Cell (graph M) m n -> ⊢Type n

    -- natural numbers
    NN : ⊢Type m

    -- functions
    _⇒_ : ⊢Type n -> ⊢Type n -> ⊢Type n



record MotiveMTT (M : ModeSystem 𝑖) (𝑗 : 𝔏 ^ 3) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field ⟦_⟧-Mode : 0Cell (graph M) -> Category 𝑗
  field ⟦_⟧-Modality : ∀{a b} -> 1Cell (graph M) a b -> Functor ⟦ a ⟧-Mode ⟦ b ⟧-Mode
  field ⟦_⟧-Transformation : ∀{a b} -> (μ ν : 1Cell (graph M) a b)
                             -> ∀{v} -> (ξ : 2Cell (graph M) v μ ν)
                             -> Natural ⟦ μ ⟧-Modality ⟦ ν ⟧-Modality


---------------------------------------------
-- A translation target for ChorMTT

mutual
  GlobalType : (n : ℕ) -> 𝒰₀
  GlobalType n = Vec (LocalType n) n

  data LocalType (n : ℕ) : 𝒰₀ where
    NN : LocalType n
    _⇒_ : LocalType n -> LocalType n -> LocalType n
    Quote : GlobalType n -> LocalType n


open import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Example
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding ([_])
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Example
open import KamiTheory.Main.Generic.ModeSystem.Modality
open import KamiTheory.Main.Generic.ModeSystem.Transition

open import Data.Fin using (#_ ; zero ; suc ; Fin)
open import Data.List using (_∷_ ; [])
open import Data.Vec using ([] ; _∷_ ; _++_) renaming (Vec to StdVec)

-- open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
open import Agora.Order.Preorder
open import Agora.Setoid.Definition

open import KamiTheory.Basics hiding (typed)
open import KamiTheory.Order.Preorder.Instances

module _ (n : ℕ) where

  PP : Preorder _
  PP = ′ StdVec 𝟚 n ′

  postulate instance
    _ : ∀{a b : ⟨ PP ⟩} -> isProp (a ≤ b)

  M : ModeSystem _
  M = SendReceiveNarrow-ModeSystem.SRN-ModeSystem PP {{it}} {{it}}


  target : MotiveMTT M {!!}
  target = {!!}


