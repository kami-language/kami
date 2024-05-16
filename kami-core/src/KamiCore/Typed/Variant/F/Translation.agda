
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.F.Translation where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category

open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Basics



module Translation (n : ℕ) where
-- (P : Preorder 𝑖) {{_ : hasDecidableEquality ⟨ P ⟩}} {{_ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)}} where

  P : Preorder _
  P = 𝒫ᶠⁱⁿ (𝔽 n)

  instance
    _ : hasDecidableEquality ⟨ P ⟩
    _ = {!!}

  instance
    _ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)
    _ = {!!}

  -- Getting the mode system
  open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Example
  open SendReceiveNarrow-ModeSystem P {{it}} {{it}}


  -- Instantiating MTT with the 2category generated from the modesystem
  open import KamiCore.Typed.Variant.F.Definition3

  Param : MTTꟳ _
  Param = record
    { 𝓂 = Mode SRN-ModeSystem
    ; isCategory:𝓂 = isCategory:byModeSystem SRN-ModeSystem
    ; is2Category:𝓂 = is2Category:byModeSystem SRN-ModeSystem
    }

  open Definition-MTTꟳ {{Param}}
    renaming (ModeHom to ModeHom')

  -- Instantiating the target language with the preorder
  open import KamiCore.Typed.Variant.F.Model6

  ρ : isProcessSet _
  ρ = record { Proc = 𝔽 n }

  open IR {{ρ}}
    renaming (Ctx to Ctx')


  private variable
    a b c : Mode SRN-ModeSystem
    μ ν : ModeHom' a b



  ⦋_⦌-Ctx : ∀{μ : ModeHom' a b} -> CtxExt μ -> Ctx'
  ⦋ ε ⦌-Ctx = ε
  ⦋ Γ ∙⟮ x ∣ μ ⟯ ⦌-Ctx = {!!}
  ⦋ Γ ∙! ω ⦌-Ctx = ⦋ Γ ⦌-Ctx



