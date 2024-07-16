-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Pipeline.P1-MTT-generic where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls ; _and_)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.UniqueSortedList.Instance.Preorder
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category


open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')

open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Basics hiding (_⋆_)



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
  import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition as 2CellDefinition
  open 2CellDefinition.2CellDefinition hiding (id)
  open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Example
  open SendReceiveNarrow-ModeSystem P {{it}} {{it}}
  open 2GraphExample.SendReceiveNarrow-2Graph P
  -- open 2CellExample.SendReceiveNarrow-2Cells P {{it}} {{it}}


  -- Instantiating MTT with the 2category generated from the modesystem
  open import KamiCore.Experiments.Definition3

  open ModeSystemAs2Category SRN-ModeSystem

  instance
    Param : MTTꟳ _
    Param = record
      { 𝓂 = Mode SRN-ModeSystem
      ; isCategory:𝓂 = isCategory:byModeSystem
      ; is2Category:𝓂 = is2Category:byModeSystem
      }


  open Definition-MTTꟳ {{Param}}
    renaming (ModeHom to ModeHom' ; _⊢_ to _⊢'_)

  instance
    isCategoryData:ModeHom : isCategoryData (Mode SRN-ModeSystem) ModeHom'
    isCategoryData:ModeHom = HomData {{isCategory:𝓂 {{Param}}}}

  instance
    isCategory:ModeHom : isCategory (Mode SRN-ModeSystem)
    isCategory:ModeHom = record { Hom = ModeHom' }

  instance
    is2Category:ModeHom : is2Category ′(Mode SRN-ModeSystem)′
    is2Category:ModeHom = is2Category:𝓂 {{Param}}

  id₂ : ∀{a b} -> {μ : ModeHom' a b} -> μ ⟹ μ
  id₂ = {!!}


  ----------------------------------------------------------
  -- Examples
  private variable
    m : Mode SRN-ModeSystem
    Γ : Ctx m
    A B X Y : ⊢Type m

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

  _∘'_ : Γ ⊢' ⟮ A ∣ id' ⟯⇒ B -> Γ ⊢' A -> Γ ⊢' B
  _∘'_ = {!!}

  ev : ∀ (u : ⟨ P ⟩) -> `[]` ⨾ `＠` u ⨾ id' ⟹ id'
  ev = {!!}

  stage : ∀ (u : ⟨ P ⟩) -> id ⟹ `＠` u ⨾ `[]` ⨾ id'
  stage = {!!}

  module _ (i j : 𝔽 n) where
    eval : Γ ⊢' ⟮ ◻ X ＠ ⦗ i ⦘ ∣ id' ⟯⇒ X
    eval = Λ letmod (var (suc! zero) id₂)
             and letmod[ `＠` ⦗ i ⦘ ⨾ id ] var (suc! zero) id₂
             and var zero (ev ⦗ i ⦘)

    eval' : Γ ⊢' ⟮ ◻ X ＠ ⦗ i ⦘ ∣ id' ⟯⇒ Tr X
    eval' = Λ letmod (var (suc! zero) id₂)
             and letmod[ `＠` ⦗ i ⦘ ⨾ id ] var (suc! zero) id₂
             and seq (trans (ev ⦗ i ⦘) (mod _ (var (suc! zero) id₂)))
                     (letmod (var (suc! zero) id₂)
                       and pure (var zero id₂))

    globalize'-Either : Γ ⊢' ⟮ Either A B ＠ ⦗ i ⦘ ∣ id' ⟯⇒ ◻ (Either (A ＠ ⦗ i ⦘) (B ＠ ⦗ i ⦘)) ＠ ⦗ i ⦘
    globalize'-Either = lam (letmod id' (var (suc! zero) id₂)
                            (mod _ (either (var (suc! zero) id₂)
                                       (mod _ (left (mod _ (var (suc! (suc! zero)) {!!}))))
                                       (mod _ (right (mod _ (var (suc! (suc! zero)) {!!}))))
                                       ))
                           )

    globalize-Either : Γ ⊢' ⟮ Either A B ＠ ⦗ i ⦘ ∣ id' ⟯⇒ Tr (Either (A ＠ ⦗ i ⦘) (B ＠ ⦗ i ⦘))
    globalize-Either = Λ (eval' ∘' (globalize'-Either ∘' var zero id₂))


    globalize'-Lst : Γ ⊢' ⟮ Lst A ＠ ⦗ i ⦘ ∣ id' ⟯⇒ ◻ (Lst (A ＠ ⦗ i ⦘)) ＠ ⦗ i ⦘
    globalize'-Lst = Λ letmod (var (suc! zero) id₂)
                       and mod _ (rec-Lst ((var (suc! zero) id₂))
                                 (mod _ [])
                                 (letmod (var (suc! zero) id₂)
                                 and mod _ (mod _ (var (suc! (suc! (suc (suc zero)))) (stage ⦗ i ⦘)) ∷ var (suc! zero) id₂)
                                 ))

    globalize-Lst : Γ ⊢' ⟮ Lst A ＠ ⦗ i ⦘ ∣ id' ⟯⇒ Tr (Lst (A ＠ ⦗ i ⦘))
    globalize-Lst = Λ (eval' ∘' (globalize'-Lst ∘' var zero id₂))

    com : ∀{i j} -> Γ ⊢' A ＠ i ⇒ Tr (A ＠ j)
    com = Λ trans {!!} (var zero id₂)

    single-map : Γ ⊢' (A ＠ ⦗ j ⦘ ⇒ B ＠ ⦗ j ⦘) ⇒ A ＠ ⦗ i ⦘ ⇒ Tr (B ＠ ⦗ i ⦘)
    single-map = Λ Λ seq (com ∘' var zero id₂) (seq (com ∘' (var (suc (suc zero)) id₂ ∘' var zero id₂)) (pure (var zero id₂)))


    remote-map : Γ ∙⟮ A ＠ ⦗ j ⦘ ⇒ B ＠ ⦗ j ⦘ ∣ id' ⟯
                   ∙⟮ Lst A ＠ ⦗ i ⦘ ∣ id' ⟯
                 ⊢' Tr (Lst B ＠ ⦗ i ⦘)
    remote-map = seq (globalize-Lst ∘' (var zero id₂))
                 (rec-Lst (var zero id₂)
                          (pure (mod _ []))
                          (seq ((single-map ∘' var (suc (suc (suc (suc zero)))) id₂) ∘' (var (suc zero) id₂))
                           (seq (var (suc zero) id₂)
                           (letmod (var (suc! (suc zero)) id₂)
                             and letmod (var (suc! (suc zero)) id₂)
                             and pure (mod _ (var (suc! (suc zero)) id₂ ∷ var (suc! zero) id₂))
                             )))
                 )



