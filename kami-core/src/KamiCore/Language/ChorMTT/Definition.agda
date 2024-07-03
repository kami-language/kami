
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorMTT.Definition where

open import Data.List using (drop)

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.Category.Std.Category.Structured.Classified.Definition
open import Agora.TypeTheory.STT.Definition
open import Agora.TypeTheory.ParamSTT.Definition

open import KamiTheory.Basics hiding (_⋆_)
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category
import KamiTheory.Main.Generic.ModeSystem.2Graph.Example3 as 2GraphExample
import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition as 2CellDefinition
import KamiTheory.Main.Generic.ModeSystem.2Cell.Rewriting as 2CellRewriting
import KamiTheory.Main.Generic.ModeSystem.2Cell.Linear as 2CellLinear

open import KamiCore.Language.MTT.Definition
open import KamiCore.Language.MinMTT.Definition
open import KamiCore.Language.MinMTT.Properties







record ChorMTT 𝑗 : 𝒰 (𝑗 ⁺) where
  field Roles : Preorder 𝑗
  field {{hasDecidableEquality:Roles}} : hasDecidableEquality ⟨ Roles ⟩
  field {{isProp:≤-Roles}} : ∀{a b : ⟨ Roles ⟩} -> isProp (a ≤ b)

open ChorMTT public

module _ 𝑗 where
  macro Chor𝔐TT = #structureOn (ChorMTT 𝑗)

module Chor𝔐TT/Definition (This : Chor𝔐TT 𝑗) where

  module [Chor𝔐TT/Definition::Param] where
    P : Preorder _
    P = This .Roles

  -- Getting the mode system
    open 2CellDefinition.2CellDefinition hiding (id) public
    open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Example3 public
    open PolySendReceive-ModeSystem P {{it}} {{it}} public
    open 2GraphExample.PolySendReceive-2Graph P public
    open 2CellLinear.2CellLinear PolySR public
    open 2CellRewriting.2CellRewriting PolySR public

    open ModeSystemAs2Category PolySR-ModeSystem public

    ⊢Param = Mode PolySR-ModeSystem

    ⊢ModeHom : (a b : Mode PolySR-ModeSystem) -> 𝒰 _
    ⊢ModeHom a b = a ⟶ᵘ b

    variable
      a a₀ b c d : Mode PolySR-ModeSystem
      μ ν η ω : ModeHom PolySR-ModeSystem a b
      U V : ⟨ This .Roles ⟩

    -----------------------------------------
    -- Arrow classification
    -----------------------------------------
    classify-Single : {a b : Mode PolySR-ModeSystem}
                      -> {μ ν : ⊢ModeHom a b}
                      -> SingleFace' vis μ ν -> (𝒫ᶠⁱⁿ (𝟙 {ℓ₀}))
    classify-Single (singleFace (idₗ₁ ⌟[ send U ]⌞ idᵣ₁) top₁ bot) = ⊥
    classify-Single (singleFace (idₗ₁ ⌟[ recv U ]⌞ idᵣ₁) top₁ bot) = ⦗ tt ⦘

    classify-Linear : {a b : Mode PolySR-ModeSystem}
                      -> {μ ν : ⊢ModeHom a b}
                      -> Linear2Cell vis μ ν -> (𝒫ᶠⁱⁿ (𝟙 {ℓ₀}))
    classify-Linear [] = ⊥
    classify-Linear (x ∷ xs) = classify-Single x ∨ classify-Linear xs

    classify : {a b : Mode PolySR-ModeSystem}
               -> {μ ν : ⊢ModeHom a b}
               -> (α : μ ⟹ ν)
               -> (𝒫ᶠⁱⁿ (𝟙 {ℓ₀}))
    classify [ incl α₀ ∣ incl α₁ ] = classify-Linear (linearize α₁)

    module _ {a b : Mode PolySR-ModeSystem} where

      instance
        isClassified:PolySR : isClassified (𝒫ᶠⁱⁿ (𝟙 {ℓ₀})) (HomCategory a b)
        isClassified:PolySR = record
          { class = classify
          ; preserve-◆ = {!!}
          ; preserve-id = {!!}
          }

    data isSmall-Min𝔐TT : (⊢ModeHom a b) -> 𝒰 (𝑗 ⌄ 0) where
      incl : ∀(x : BaseModeHom-PolySR a b) -> isSmall-Min𝔐TT (x ⨾ id')

    split-Min𝔐TT : (⊢ModeHom a b) -> Path (λ a b -> ∑ λ (ϕ : ⊢ModeHom a b) -> isSmall-Min𝔐TT ϕ) a b
    split-Min𝔐TT id' = id'
    split-Min𝔐TT (μ ⨾ μs) = ((μ ⨾ id') , incl μ) ⨾ split-Min𝔐TT μs

  open [Chor𝔐TT/Definition::Param]


  module [Chor𝔐TT/Definition::Private] where
    Super : Min𝔐TT _
    Super = record
      { ModeTheory = ′ Mode PolySR-ModeSystem ′
      ; isSmall = isSmall-Min𝔐TT
      ; split = split-Min𝔐TT
      ; isTargetMode = λ a -> a ≡ ◯
      ; Classification = 𝒫ᶠⁱⁿ 𝟙
      ; isClassified:Transformation = isClassified:PolySR
      }
  open [Chor𝔐TT/Definition::Private]


  open Min𝔐TT/Definition Super
  open [Min𝔐TT/Definition::Private] using (_⟶ₛ_)


  -- Import the required definitions from 𝔐TT itself
  open 𝔐TT/Definition [Min𝔐TT/Definition::Private].Super

  --------------------------------------------------------------------
  -- Types
  module [Chor𝔐TT/Definition::Type] where
    open [Min𝔐TT/Definition::Type] public

    -- variable
    --   A B : Type (_at_ {{hasParamSTT:MinMTT}} Super (◯ , b))
  open [Chor𝔐TT/Definition::Type]


  --------------------------------------------------------------------
  -- Contexts
  module [Chor𝔐TT/Definition::Ctx] where
    open [Min𝔐TT/Definition::Ctx] public

    -- variable
    --   Γ : Ctx (_at_ {{hasParamSTT:MinMTT}} Super (◯ , b))

    data isCtx₂ : ⊢Ctx {◯} a -> 𝒰 𝑗 where
      ε : isCtx₂ ε
      stepVar : {Γ : ⊢Ctx {◯} ◯} -> isCtx₂ Γ -> {A : ⊢Type a} -> {μ : ⊢ModeHom a ◯} -> isCtx₂ (Γ ∙⟮ A ∣ μ ⟯)
      stepRes : ∀(x : Edge (of PolySR-ModeSystem .graph) b a) -> {Γ : ⊢Ctx {◯} a} -> isCtx₂ Γ -> isCtx₂ (Γ ∙! ((x ⨾ id) , incl x))


  open [Chor𝔐TT/Definition::Ctx]




  --------------------------------------------------------------------
  -- Terms


  module [Chor𝔐TT/Definition::Term] where
    open [Min𝔐TT/Definition::Term] renaming (_⊢_ to _⊢'_) public
    open Min𝔐TT/Properties Super

    private
      pattern []ₛ = (`[]` ⨾ id' , incl `[]`)
      pattern ＠ₛ U  = (`＠` U ⨾ id' , incl (`＠` _))

    data isBroadcast : ∀{a b : ⊢Param} -> {μ ν : ⊢ModeHom a b} -> μ ⟹ ν -> 𝒰₀ where
      
    data _⊢_ : ∀{a} -> ⊢Ctx {◯} a -> ⊢Type a -> 𝒰 𝑗 where
      var : {Γ : ⊢Ctx {◯} a} -> ∀{μ : ⊢ModeHom _ b} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> (α : μ ⟹ η) -> Γ ⊢ A
      tt : Γ ⊢ Unit

      -- modalities
      mod : ∀ μ -> Γ ∙! μ ⊢ A -> Γ ⊢ ⟨ A ∣ μ ⟩

      letmod : ∀(μ : c ⟶ₛ b) -> (ν : ⊢ModeHom b ◯)
            -> Γ ∙!* (split-Min𝔐TT ν) ⊢ ⟨ A ∣ μ ⟩
            -> Γ ∙⟮ A ∣ fst μ ◆ ν ⟯ ⊢ B
            -> Γ ⊢ B

      letmod-＠ :  ∀(μ : c ⟶ₛ b) -> (ν : ⊢ModeHom b (▲ U))
            -> Γ ∙! ＠ₛ U ∙!* (split-Min𝔐TT ν) ⊢ ⟨ A ∣ μ ⟩
            -> Γ ∙⟮ A ∣ fst μ ◆ ν ◆ (`＠` U ⨾ id') ⟯ ∙! ＠ₛ U ⊢ B
            -> Γ ∙! ＠ₛ U ⊢ B

      -- explicit transformations
      trans : ∀ {μ ν : _ ⟶ b} -> (α : μ ⟹ ν) -> isBroadcast α
            -> Γ ⊢ Mod-Type (split-Min𝔐TT μ) A
            -> Γ ⊢ Tr (Mod-Type (split-Min𝔐TT ν) A)

      -- transformations monad
      pure : Γ ⊢ A -> Γ ⊢ Tr A
      seq : ∀{A : ⊢Type ◯} -> Γ ⊢ Tr A -> Γ ∙⟮ A ∣ id' ⟯ ⊢ Tr B -> Γ ⊢ Tr B
      seq-＠ : Γ ∙! ＠ₛ U ⊢ Tr A
              -> Γ ∙⟮ A ∣ `＠` U ⨾ id ⟯ ∙! ＠ₛ U ⊢ Tr B
              -> Γ ∙! ＠ₛ U ⊢ Tr B

      -- functions
      lam-＠ : Γ ∙⟮ A ∣ `＠` U ⨾ id' ⟯ ∙! ＠ₛ U ⊢ B -> Γ ∙! ＠ₛ U ⊢ A ⇒ B
      lam : Γ ∙⟮ A ∣ id' {m = ◯} ⟯ ⊢ B -> Γ ⊢ A ⇒ B
      app : Γ ⊢ A ⇒ B -> Γ ⊢ A -> Γ ⊢ B

      -- sum types
      left : Γ ⊢ A -> Γ ⊢ Either A B
      right : Γ ⊢ B -> Γ ⊢ Either A B
      either-＠ : Γ ∙! ＠ₛ U ⊢ Either A B
             -> Γ ∙⟮ A ∣ `＠` U ⨾ id' ⟯ ∙! ＠ₛ U ⊢ C
             -> Γ ∙⟮ B ∣ `＠` U ⨾ id' ⟯ ∙! ＠ₛ U ⊢ C
             -> Γ ∙! ＠ₛ U ⊢ C
      either : {Γ : ⊢Ctx {◯} ◯} -> Γ ⊢ Either A B -> Γ ∙⟮ A ∣ id ⟯ ⊢ C -> Γ ∙⟮ B ∣ id ⟯ ⊢ C -> Γ ⊢ C

      -- list types
      [] : Γ ⊢ Lst A
      _∷_ : Γ ⊢ A -> Γ ⊢ Lst A -> Γ ⊢ Lst A
      rec-Lst-＠ : Γ ∙! ＠ₛ U ⊢ Lst A
                  -> Γ ∙! ＠ₛ U ⊢ C
                  -> Γ ∙⟮ A ∣ `＠` U ⨾ id' ⟯ ∙⟮ C ∣ `＠` U ⨾ id' ⟯ ∙! ＠ₛ U ⊢ C
                  -> Γ ∙! ＠ₛ U ⊢ C
      rec-Lst : {Γ : ⊢Ctx {◯} ◯} -> Γ ⊢ Lst A -> Γ ⊢ C -> Γ ∙⟮ A ∣ id ⟯ ∙⟮ C ∣ id ⟯ ⊢ C -> Γ ⊢ C

  open [Chor𝔐TT/Definition::Term]


  -- Our simple type theory

  module _ (a : ⊢Param) where
    λChorMTT : STT _
    λChorMTT = record
      { Ctx = ∑ λ (Γ : Ctx (◯ , a) of Super) -> isCtx₂ Γ
      ; Type = Type (◯ , a) of Super
      ; Term = λ Γ A -> fst Γ ⊢ A
      }


instance
  hasParamSTT:ChorMTT : hasParamSTT (ChorMTT 𝑗)
  hasParamSTT:ChorMTT = record
    { Param = Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Param].⊢Param
    ; SubParam = λ This a -> ⊤-𝒰 {ℓ₀}
    ; _at_ = λ n a -> Chor𝔐TT/Definition.λChorMTT n a
    }



