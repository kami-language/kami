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

----------------------------------------------------------
-- The Kami compilation pipeline
----------------------------------------------------------
--
-- # Compiling Kami to process languages
--
-- The compilation process is quite involved, in particular
-- since the target language itself is typed and the well-typedness
-- relation has to be preserved intrinsincally. This requires
-- to do much more work up-front to implement the pipeline,
-- but gives very strong correctness guarantees for the compilation,
-- in particular when future changes are going require updates to
-- the pipeline.
--
-- We compile a single Kami term, which represents a choreography
-- between n participating roles into separate programs; one for each
-- participant. The complications arise from the fact that MTT,
-- the language that Kami is based on, is very flexible and general.
-- This generality has to be reduced before the term can be projected
-- to the participants. Additionally, nested modalities and their context
-- restriction operations increase the difficulty of projections, as it is
-- not straightforward to project the context to the participants: the result
-- depends on the current nesting of modalities we are under.
--
-- ## The intermediate languages
--
-- The compilation pipeline is implemented as translations between various
-- intermediate representations (IR). The dedicated IRs enforce that each step
-- in fact did its job, and serve as induction basis for the next step.
-- They are available in the submodules of `KamiCore.Language`. In particular,
-- the languages are the following:
--
--  - MTT: The source language. Parametric over arbitrary 2-categorical mode theories,
--    this is mostly the original Modal Type Theory by Daniel Gratzer. The only addition
--    is an explicit term for unevaluated transformations. This language is going to
--    be the target of the typechecker, and the pipeline takes MTT terms as input for compilation.
--
--  - MinMTT: This is "Minimal MTT", an optimized representation of MTT which has the same expressive
--    power as MTT but removes some syntactic sugar. In particular:
--      1) Function types do no longer have a modality annotation. Instead this is simulated by modal
--      types and `letmod` bindings.
--      2) All modal types are restricted to a subclass of "small" arrows in the mode theory. This means
--      that modal types under compositions of modalities are represented as nested modal types,
--      e.g., `⟨ A ∣ μ ◆ ν ⟩` is translated to `⟨ ⟨ A ∣ μ ⟩ ∣ ν ⟩`.
--      This means that the modal terms, `mod` and `letmod`, if they involving compositions,
--      have to be translated into iterations of singletons.
--
--  - ChorMTT: This is the first representation of Kami which is specialized to the choreographic modetheory.
--    There is a condition on the form of contexts which requires `[]` restrictions to follow directly after
--    `＠` restrictions. The effect is that variables are only allowed to occur in the global mode. Such a
--    property is required for the following step to go through. The translation from MinMTT thus shifts
--    `＠` annotations upwards until the next `[]` restriction.
--
--  - ChorProc: This is the first process-calculus-like intermediate language, and the translation step from ChorMTT
--    is the essential part of the whole compilation. Context and types remain globally defined, but terms are families
--    of local terms, one for each participant. We retain a context restriction operation, but it represents the composition
--    `[] ◆ ＠ U` of modalities. This means that we don't have the concept of a local mode anymore in this language.
--    In its core, the translation from ChorMTT to ChorProc follows the standard paradigm of choreographic projections.
--    Complications arise only from the fact that we have nested modalities, and thus communications/transformations can appear
--    arbitrary deep in the context.
--
--  - StdProc: This is a standard lambda calculus with send and receive operations, and is the final target of our pipeline.
--    from here it is straightforward to translate to various real-world programming languages such as Elixir or Rust, as no
--    fancy types or context structures exist in this language. The translation from ChorProc elides all context restrictions,
--    and projects the contexts and types to their local variants. Boxed choreographies are represented as tuples of their projections.
--    The terms themselves are already projected, only the variables have to be dealt with. The specialized relation for accessing boxed
--    variables in ChorProc is translated into standard projection terms to access elements of tuples.
--
-- ## Implementation details
--
-- The IR-languages are defined in the `.Definition` submodules of their respective directories. The translation from their "parent" language
-- is given in the ".Translation" subdirectory. The translation itself is a framework of "parametrized simple-type-theory" morphisms, an abstractions
-- which allows us to model the fact that the IRs have different parameter spaces, and the compilation pipeline is a composition of smaller steps,
-- where a generic language is translated to a more specific language. This means that the choice of parameters flows in the opposite direction
-- of the actual compilation: choices in the target language influence which concrete source language is being compiled from.
--
-- The four compilation steps are given by four ParamSTT morphisms: 𝔉₁ ,  ⃨ , 𝔉₄
-- ```
--    MTT -[ 𝔉₁ ]-> MinMTT -[ 𝔉₂ ]-> ChorMTT -[ 𝔉₃ ]-> ChorProc -[ 𝔉₄ ]-> ChorStd
-- ```
--
-- We compose the steps into a single ParamSTT morphism, 𝔉:

𝔉 : ParamSTTHom (Std𝔓roc) (𝔐TT _)
𝔉 = 𝔉₄ ◆-ParamSTT
    𝔉₃ ◆-ParamSTT
    𝔉₂ ◆-ParamSTT
    𝔉₁

--
-- Now 𝔉 can be used to translate contexts, types and terms from MTT to StdProc.
--


----------------------------------------------------------
-- Example
----------------------------------------------------------
--
-- In order to show that the 


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

