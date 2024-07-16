-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Pipeline.Definition where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _and_)
open import Agora.Category.Std.Category.Definition
open import Agora.TypeTheory.ParamSTT.Definition
open import Agora.TypeTheory.ParamSTT.Instance.Category
open import Agora.Category.Std.2Category.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Data.Fin.Definition
open import Agora.TypeTheory.STT.Definition
open import Agora.TypeTheory.ParamSTT.Definition

-- open import KamiTheory.Data.UniqueSortedList.Definition
-- open import KamiTheory.Data.UniqueSortedList.Properties
open import KamiTheory.Data.UniqueSortedList.NonEmpty
open import KamiTheory.Data.UniqueSortedList.Properties
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.UniqueSortedList.Instance.Preorder

open import KamiCore.Language.MTT.Definition
open import KamiCore.Language.MinMTT.Definition
open import KamiCore.Language.MinMTT.Translation
open import KamiCore.Language.ChorMTT.Definition
open import KamiCore.Language.ChorMTT.Translation
open import KamiCore.Language.ChorProc.Definition
open import KamiCore.Language.ChorProc.Translation
open import KamiCore.Language.ChorProc.TranslationCtx
open import KamiCore.Language.StdProc.Definition
open import KamiCore.Language.StdProc.Translation

open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category


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
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Private] Chor public
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Param] Chor public

  instance
    abc : hasDecidableEquality ⟨ P ⟩
    abc = hasDecidableEquality:Roles Chor

  instance
    i2 : isSetoid ⟨ P ⟩
    i2 = of (↳ P)

  instance
    xyz : isPreorder _ ′ ⟨ P ⟩ ′
    xyz = of P

  instance
    def : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)
    def = isProp:≤-Roles Chor

  Source : MTT _
  Source = ⟨ 𝔉 ⟩ Target

  open 𝔐TT/Definition Source public
  open [𝔐TT/Definition::Type] public --  renaming (⊢Type to 𝔐TT⊢Type) public
  open [𝔐TT/Definition::Ctx] public -- renaming (⊢Ctx to 𝔐TT⊢Ctx) public
  open [𝔐TT/Definition::Term] public -- renaming (_⊢_ to _𝔐TT⊢_ ; _⊢Var⟮_∣_⇒_⟯ to _𝔐TT⊢Var⟮_∣_⇒_⟯ ; _⊢Var⟮_∣_⇒∼_⟯ to _𝔐TT⊢Var⟮_∣_⇒∼_⟯) public
  open Variables/Mode public
  -- open Variables/Hom public
  open Variables/Ctx public
  open Variables/Type public
  variable X Y Z : ⊢Type m

  pattern id₂ = [ incl [] ∣ incl [] ]


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

  ev : ∀ (u : ⟨ Roles Chor ⟩) -> `[]` ⨾ `＠` u ⨾ id' ⟹ id'
  ev u = [ incl [] ∣ incl (incl (id' ⌟[ recv u ]⌞ id' ⌟) ∷ [] ) ]

  stage : ∀ (u : ⟨ P ⟩) -> id ⟹ `＠` u ⨾ `[]` ⨾ id'
  stage = {!!}

  -- eval : ∀ i -> Γ ⊢ ⟮ ◻ X ＠ ⦗ i ⦘₊ ∣ id' ⟯⇒ X
  -- eval {X = X} i = Λ letmod (var (suc! zero) id₂ {!!})
  --           and (letmod {A = X} {μ = `[]` ⨾ id'} (`＠` ⦗ i ⦘₊ ⨾ id')  (var {μ = (`＠` ⦗ i ⦘₊ ⨾ id')} (suc! {!zero!}) {!!} {!!})
  --           {!!})
  --           -- var zero (ev ⦗ i ⦘₊) {!!}

  eval' : ∀ i -> Γ ⊢ ⟮ ◻ X ＠ ⦗ i ⦘₊ ∣ id' ⟯⇒ Tr X
  eval' i = Λ letmod (var (suc! zero) id₂ {!!})
              and letmod[ `＠` ⦗ i ⦘₊ ⨾ id ] var (suc! zero) id₂ {!!}
              and seq (trans (ev ⦗ i ⦘₊) {!!} (mod _ (var (suc! zero) id₂ {!!})))
                      (letmod (var (suc! zero) id₂ {!!})
                        and pure (var zero id₂ {!!}))


open Generic 2

M0Type : ⊢Type _
M0Type = ⟮ ◻ (Either Unit Unit ＠ ⦗ suc zero ⦘₊ ) ＠ ⦗ zero ⦘₊ ∣ id' ⟯⇒ Tr (Either Unit Unit ＠ ⦗ suc zero ⦘₊ )

ex1 : ε ⊢ M0Type
ex1 = eval' zero

-- res1 : M1⊢Type _
res1 = ⟪ runAt {{of 𝔉}} Target refl-≡  ∣ ex1 Term⟫






--------------------------------------------------------------------
-- Helpers for running individual compilation steps
--------------------------------------------------------------------
{-

M1 : MinMTT _
M1 = (⟨ 𝔉₄ ◆-ParamSTT 𝔉₃ ◆-ParamSTT 𝔉₂ ⟩ Target)
open Min𝔐TT/Definition M1
open [Min𝔐TT/Definition::Term] renaming (_⊢_ to _M1⊢_)
open [Min𝔐TT/Definition::Ctx] using (ε)
open [Min𝔐TT/Definition::Type] renaming (⊢Type to M1⊢Type)

M1Type : M1⊢Type _
M1Type = ⟪ runAt {F = F₁} {{isReduction:F₁}} M1 {a = (◯ , ◯)} refl-≡  ∣ M0Type Type⟫

M1Type' : M1⊢Type _
M1Type' = ⟪𝔉₁∣_Type⟫ M1 {a = (◯)} M0Type

M1Term : ε M1⊢ M1Type
M1Term = ⟪𝔉₁∣_Term⟫ M1 ex1

M2 : ChorMTT _
M2 = (⟨ 𝔉₄ ◆-ParamSTT 𝔉₃ ⟩ Target)
open Chor𝔐TT/Definition M2
open [Chor𝔐TT/Definition::Term] renaming (_⊢_ to _M2⊢_)
open [Chor𝔐TT/Definition::Ctx] using (ε)
open [Chor𝔐TT/Definition::Type] renaming (⊢Type to M2⊢Type)


M2Type : M1⊢Type _
M2Type = ⟪𝔉₂∣_Type⟫ M2 {a = (◯)} M1Type

M2Term : _ M2⊢ M2Type
M2Term = ⟪𝔉₂∣_Term⟫ M2 M1Term


M3 : ChorProc _
M3 = (F₄ Target)
open Chor𝔓roc/Definition M3
open [Chor𝔓roc/Definition::Term] renaming (_⊢_ to _M3⊢_)
open [Chor𝔓roc/Definition::Ctx] using (ε)
open [Chor𝔓roc/Definition::Type] renaming (⊢Type to M3⊢Type)
open Chor𝔓roc/TranslationCtx


M3Type : M3⊢Type _
M3Type = ⟪𝔉₃∣_Type⟫ M3 {a = (◯)} M2Type

M3Term : ε M3⊢ M3Type
M3Term = KamiCore.Language.ChorProc.Translation.transl-Term-◯ M3 _ ε M2Term


-----------------------------------------
-- target

M4 : StdProc
M4 = Target
open Std𝔓roc/Definition M4
open [Std𝔓roc/Definition::Term] renaming (_⊢_ to _M4⊢_)
-- open [Std𝔓roc/Definition::Ctx] using (ε)
open [Std𝔓roc/Definition::Type] renaming (⊢Type to M4⊢Type)

M4Type : M4⊢Type
M4Type = ⟪𝔉₄∣_Type⟫ M4 M3Type

M4Term : _ M4⊢ M4Type
M4Term = ⟪𝔉₄∣_Term⟫ M4 M3Term

-- ex10 : ε M1⊢ ⟪ runAt {{of 𝔉₁}} M1 refl-≡ ∣ ⟮ ◻ (Either Unit Unit ＠ ⦗ suc zero ⦘₊ ) ＠ ⦗ zero ⦘₊ ∣ id' ⟯⇒ Tr (Either Unit Unit ＠ ⦗ suc zero ⦘₊ ) Type⟫
-- ex10 = {!!}

-- ? ⟪ runAt {{of 𝔉₁}} M1 refl-≡ ∣ ex1 Term⟫
-}

