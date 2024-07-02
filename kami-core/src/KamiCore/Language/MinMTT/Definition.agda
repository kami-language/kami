
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

--
-- Purpose: Function types don't have modalites,
-- mod introduces always single modalities
--

module KamiCore.Language.MinMTT.Definition where

open import Agora.Conventions hiding (m ; n ; k ; _∣_)
open import Agora.Data.Product.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Category.Structured.Classified.Definition
open import Agora.TypeTheory.STT.Definition
open import Agora.TypeTheory.ParamSTT.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice

open import KamiCore.Language.MTT.Definition

open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')


record MinMTT (𝑖 : 𝔏 ^ 6) : 𝒰 (𝑖 ⁺) where
  field ModeTheory : 2Category (𝑖 ⌄ 0 ⋯ 4)
  field isSmall : ∀{a b : ⟨ ModeTheory ⟩} -> a ⟶ b -> 𝒰₀
  field split : ∀{a b : ⟨ ModeTheory ⟩} -> a ⟶ b -> Path (λ a b -> ∑ λ (ϕ : a ⟶ b) -> isSmall ϕ) a b
  field isTargetMode : ⟨ ModeTheory ⟩ -> 𝒰 (𝑖 ⌄ 5)
  field Classification : JoinSemilattice (ℓ₀ , ℓ₀ , ℓ₀)
  field {{isClassified:Transformation}} : ∀{a b : ⟨ ModeTheory ⟩} -> isClassified Classification (HomCategory a b)

open MinMTT public

  -- TODO: We need extra information here
  -- about how to split the arrows into singletons

open MinMTT public

module _ 𝑖 where macro
  Min𝔐TT = #structureOn (MinMTT 𝑖)

module Min𝔐TT/Definition (This : Min𝔐TT 𝑖) where

  module [Min𝔐TT/Definition::Private] where
    Super : 𝔐TT 𝑖
    Super = record
      { ModeTheory = This .ModeTheory
      ; isTargetMode = This .isTargetMode
      }

    𝓂 = ⟨ This .ModeTheory ⟩

    _⟶ₛ_ : (a b : ⟨ This .ModeTheory ⟩) -> 𝒰 _
    _⟶ₛ_ a b = ∑ λ (ϕ : a ⟶ b) -> isSmall This ϕ


  open [Min𝔐TT/Definition::Private]

  open 𝔐TT/Definition Super
  open Variables/Mode
  open Variables/Hom
  -- open Variables/Type
  -- open Variables/Ctx

  module [Min𝔐TT/Definition::Type] where

    -- open [𝔐TT/Definition::Type] public

    data ⊢Type : ⟨ This .ModeTheory ⟩ -> 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
      ⟨_∣_⟩ : ⊢Type m -> m ⟶ₛ n -> ⊢Type n
      Unit : ⊢Type m
      Tr : ⊢Type m -> ⊢Type m
      Either : ⊢Type m -> ⊢Type m -> ⊢Type m
      Lst : ⊢Type m -> ⊢Type m
      _⇒_ : ⊢Type m -> ⊢Type m -> ⊢Type m

    infix 30 ⟨_∣_⟩ _⇒_

    variable
      A B C : ⊢Type m

  open [Min𝔐TT/Definition::Type]

  module [Min𝔐TT/Definition::Ctx] where

    data ⊢Ctx {a : 𝓂} : 𝓂 -> 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
      ε : ⊢Ctx {a} a
      _∙⟮_∣_⟯ : ⊢Ctx {a} n -> ⊢Type m -> m ⟶ n -> ⊢Ctx {a} n
      _∙!_ : ⊢Ctx {a} n -> m ⟶ n -> ⊢Ctx m

    infix 32 _∙⟮_∣_⟯
    infixl 30 _∙!_

    variable
      Γ Δ : ⊢Ctx {m} n

  open [Min𝔐TT/Definition::Ctx]


  module [Min𝔐TT/Definition::Term] where

    data _⊢Var⟮_∣_⇒_⟯ : (Γ : ⊢Ctx {k} o) (A : ⊢Type m) (μ : m ⟶ l) (η : o ⟶ l) → 𝒰 𝑖 where
      zero : {μ : m ⟶ l} -> (Γ ∙⟮ A ∣ μ ⟯) ⊢Var⟮ A ∣ μ ⇒ id ⟯
      suc! : {μ : m ⟶ l} {η : k ⟶ l} {ω : o ⟶ k} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> Γ ∙! ω ⊢Var⟮ A ∣ μ ⇒ ω ◆ η ⟯
      suc : Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> Γ ∙⟮ B ∣ ω ⟯ ⊢Var⟮ A ∣ μ ⇒ η ⟯


    data _⊢_ {m : Param Super} : ⊢Ctx {fst m} (snd m) -> ⊢Type (snd m) -> 𝒰 𝑖 where
      var : ∀{μ : _ ⟶ o}
            -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯
            -> (α : μ ⟹ η)
            -> class α ∼ ⊥
            -> Γ ⊢ A

      tt : Γ ⊢ Unit

      -- modalities
      mod : ∀ μ -> Γ ∙! fst μ ⊢ A -> Γ ⊢ ⟨ A ∣ μ ⟩

      letmod : ∀{μ : o ⟶ₛ n} -> (ν : n ⟶ snd m)
            -> Γ ∙! ν ⊢ ⟨ A ∣ μ ⟩
            -> Γ ∙⟮ A ∣ fst μ ◆ ν ⟯ ⊢ B
            -> Γ ⊢ B

      -- explicit transformations
      -- trans : ∀ {μ ν : n ⟶ snd m}
      --         -> (α : μ ⟹ ν)
      --         -> (¬ class α ∼ ⊥)
      --         -> Γ ⊢ ⟨ A ∣ μ ⟩ -> Γ ⊢ Tr ⟨ A ∣ ν ⟩

      -- transformations monad
      pure : Γ ⊢ A -> Γ ⊢ Tr A
      seq : ∀{A : ⊢Type (snd m)} -> Γ ⊢ Tr A -> Γ ∙⟮ A ∣ id ⟯ ⊢ Tr B -> Γ ⊢ Tr B

      -- functions
      -- lam : Γ ∙⟮ A ∣ μ ⟯ ⊢ B -> Γ ⊢ ⟮ A ∣ μ ⟯⇒ B
      -- app : Γ ⊢ ⟮ A ∣ μ ⟯⇒ B -> Γ ∙! μ ⊢ B -> Γ ⊢ B

      lam : Γ ∙⟮ A ∣ id ⟯ ⊢ B -> Γ ⊢ A ⇒ B
      app : Γ ⊢ A ⇒ B -> Γ ⊢ A -> Γ ⊢ B

      -- sum types
      left : Γ ⊢ A -> Γ ⊢ Either A B
      right : Γ ⊢ B -> Γ ⊢ Either A B
      either : Γ ⊢ Either A B -> Γ ∙⟮ A ∣ id ⟯ ⊢ C -> Γ ∙⟮ B ∣ id ⟯ ⊢ C -> Γ ⊢ C

      -- list types
      [] : Γ ⊢ Lst A
      _∷_ : Γ ⊢ A -> Γ ⊢ Lst A -> Γ ⊢ Lst A
      rec-Lst : Γ ⊢ Lst A -> Γ ⊢ C -> Γ ∙⟮ A ∣ id ⟯ ∙⟮ C ∣ id ⟯ ⊢ C -> Γ ⊢ C


  open [Min𝔐TT/Definition::Term]

  module _ (m : Param Super) where
    λMinMTT : STT _
    λMinMTT = record
      { Ctx = ⊢Ctx {fst m} (snd m)
      ; Type = ⊢Type (snd m)
      ; Term = λ Γ A -> Γ ⊢ A
      }

instance
  hasParamSTT:MinMTT : hasParamSTT (Min𝔐TT 𝑖)
  hasParamSTT:MinMTT = record
    { Param = λ This -> ⟨ This .ModeTheory ⟩ ×-𝒰 ⟨ This .ModeTheory ⟩
    ; SubParam = λ 𝒯 (x , a) -> isTargetMode 𝒯 x
    ; _at_ = λ This m -> Min𝔐TT/Definition.λMinMTT This m
    }

