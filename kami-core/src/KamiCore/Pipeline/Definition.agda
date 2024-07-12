
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

open import KamiCore.Language.MTT.Definition
open import KamiCore.Language.MinMTT.Definition
open import KamiCore.Language.MinMTT.Translation
open import KamiCore.Language.ChorMTT.Definition
open import KamiCore.Language.ChorMTT.Translation
open import KamiCore.Language.ChorProc.Definition
open import KamiCore.Language.ChorProc.Translation
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

ex1 : ε ⊢ ⟮ ◻ (Either Unit Unit ＠ ⦗ suc zero ⦘₊ ) ＠ ⦗ zero ⦘₊ ∣ id' ⟯⇒ Tr (Either Unit Unit ＠ ⦗ suc zero ⦘₊ )
ex1 = eval' zero


ex1' = ⟪ runAt {{of 𝔉}} _ refl-≡ ∣ ex1 Term⟫


