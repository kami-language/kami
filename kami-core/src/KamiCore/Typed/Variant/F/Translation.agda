
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.F.Translation where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Category.Std.Category.Definition
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category


open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition hiding (_◆_)

open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Basics



module Translation (n : ℕ) where
-- (P : Preorder 𝑖) {{_ : hasDecidableEquality ⟨ P ⟩}} {{_ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)}} where

  P : Preorder _
  P = 𝒫ᶠⁱⁿ (𝔽 n)

  instance
    hasDecidableEquality:P : hasDecidableEquality ⟨ P ⟩
    hasDecidableEquality:P = {!!}

  instance
    isProp:≤ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)
    isProp:≤ = {!!}

  -- Getting the mode system
  import KamiTheory.Main.Generic.ModeSystem.2Graph.Example as 2GraphExample
  import KamiTheory.Main.Generic.ModeSystem.2Cell.Example as 2CellExample
  open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Example
  open SendReceiveNarrow-ModeSystem P {{it}} {{it}}
  open 2GraphExample.SendReceiveNarrow-2Graph P
  -- open 2CellExample.SendReceiveNarrow-2Cells P {{it}} {{it}}


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

  instance
    isCategoryData:ModeHom : isCategoryData (Mode SRN-ModeSystem) ModeHom'
    isCategoryData:ModeHom = HomData {{isCategory:𝓂 {{Param}}}}

  -- Instantiating the target language with the preorder
  open import KamiCore.Typed.Variant.F.Model6

  ρ : isProcessSet _
  ρ = record { Proc = 𝔽 n }

  open IR {{ρ}}
    renaming (Ctx to Ctx' ; Mode to Mode')


  private variable
    a b c : Mode SRN-ModeSystem
    μ ν : ModeHom' a b

  ⦋_⦌-Mode : Mode SRN-ModeSystem -> Mode'
  ⦋ ▲ ⦌-Mode = ▲
  ⦋ ◯ ⦌-Mode = ◯

  ⦋_⦌-Type : ⊢Type a -> Type ⦋ a ⦌-Mode
  ⦋ ⟨ X ∣ x ⟩ ⦌-Type = {!!}
  ⦋ Unit ⦌-Type = Unit
  ⦋ Tr X ⦌-Type = Wrap ⦋ X ⦌-Type
  ⦋ ⟮ X ∣ x ⟯⇒ X₁ ⦌-Type = {!!}

  F-Type : (ModeHom' a b) -> Type ⦋ a ⦌-Mode -> Type ⦋ b ⦌-Mode
  F-Type id x = x
  F-Type (`＠` U ⨾ μ) x = F-Type μ (x ＠ U)
  F-Type (`[]` ⨾ μ) x = F-Type μ (◻ x)


  ⦋_⦌-Ctx : ∀{μ : ModeHom' a ◯} -> CtxExt μ -> Ctx'
  ⦋ ε ⦌-Ctx = ε
  ⦋_⦌-Ctx {μ = μ} (Γ ∙⟮ x ∣ ν ⟯) = ⦋ Γ ⦌-Ctx , F-Type (ν ◆ μ) (⦋ x ⦌-Type)
  ⦋ Γ ∙! ω ⦌-Ctx = ⦋ Γ ⦌-Ctx









