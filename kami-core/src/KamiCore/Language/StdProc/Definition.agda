

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.StdProc.Definition where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.TypeTheory.STT.Definition
open import Agora.TypeTheory.ParamSTT.Definition

open import KamiTheory.Basics hiding (_⋆_)
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.UniqueSortedList.Properties
open import KamiTheory.Data.UniqueSortedList.NonEmpty
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Order.StrictOrder.Base

open import KamiCore.Language.ChorProc.Definition

open import Data.Fin.Base using (zero ; suc)


record StdProc : 𝒰₀ where
  field Roles : ℕ

open StdProc public
macro Std𝔓roc = #structureOn StdProc


module _  {n : ℕ} where
  macro 𝑠𝑢𝑐 = #structureOn (Data.Fin.Base.Fin.suc {n = n})

  instance
    isStrictOrderHom:suc : isStrictOrderHom {A = 𝔽 n} {B = 𝔽 (suc n)} suc
    isStrictOrderHom:suc = record { homPreserves = λ x → s<s x }

enumerate : ∀ n -> 𝒫ᶠⁱⁿ (𝔽 n)
enumerate zero = ⊥
enumerate (suc n) = ⦗ zero ⦘ ∨ mapᵘ-𝒫ᶠⁱⁿ 𝑠𝑢𝑐 (enumerate n)

hasAll : ∀{n} -> (i : 𝔽 n) -> ⦗ i ⦘ ≤ enumerate n
hasAll {n = suc n} zero = ι₀-∨ {b = mapᵘ-𝒫ᶠⁱⁿ 𝑠𝑢𝑐 (enumerate n)}
hasAll {n = suc n} (suc i) = mapᵘ-𝒫ᶠⁱⁿ-≤ 𝑠𝑢𝑐 (hasAll i) ⟡ ι₁-∨ {a = ⦗ zero ⦘}

hasAll-∈ : ∀{n} -> (i : 𝔽 n) -> i ∈ ⟨ enumerate n ⟩
hasAll-∈ i = ⟨ hasAll i ⟩ _ here

notEmptyByElement : ∀{A : 𝒰 𝑖} -> ∀{a} {as : List A} -> a ∈ as -> ¬ as ≡ []
notEmptyByElement () refl-≡

enumerate₊ : ∀ n -> 𝒫₊ᶠⁱⁿ (𝔽 (suc n))
enumerate₊ n = enumerate (suc n) , λ p -> notEmptyByElement (hasAll-∈ zero) (cong-≡ ⟨_⟩ p)


module Std𝔓roc/Definition (This : Std𝔓roc) where

  module [Std𝔓roc/Definition::Private] where
    n = This .Roles

    Super : Chor𝔓roc _
    Super = record
      { Proc = 𝔽 (suc (This .Roles))
      ; allProcs = enumerate₊ (This .Roles)
      ; inAllProcs = hasAll-∈ _
      }

  open [Std𝔓roc/Definition::Private]


  module [Std𝔓roc/Definition::Type] where

    data LType : 𝒰₀

    ⊢Type : 𝒰₀
    ⊢Type = 𝔽 n -> LType

    data LType where
      _⇒_ : LType -> LType -> LType
      ◻ : ⊢Type -> LType
      Unit : LType
      NN : LType
      _××_ : LType -> LType -> LType
      Either : LType -> LType -> LType
      Lst : LType -> LType
      Tr : LType -> LType

    variable
      A B C : LType
      X : ⊢Type

  open [Std𝔓roc/Definition::Type]

  module [Std𝔓roc/Definition::Ctx] where

    data LCtx : 𝒰₀ where
      ε : LCtx
      _,_ : LCtx -> LType -> LCtx

    ⊢Ctx : 𝒰₀
    ⊢Ctx = 𝔽 n -> LCtx

    variable
      Γ : LCtx
      Δ : LCtx

  open [Std𝔓roc/Definition::Ctx]


  module [Std𝔓roc/Definition::Term] where
    data _⊢Var_Locally : LCtx -> LType -> 𝒰₀ where
      zero : Γ , A ⊢Var A Locally
      suc : Γ ⊢Var A Locally -> Γ , B ⊢Var A Locally

    data _⊢_Locally : LCtx -> LType -> 𝒰₀ where
      var : Γ ⊢Var A Locally -> Γ ⊢ A Locally

      -- sending and receiving
      recv : 𝔽 n -> Γ ⊢ Tr A Locally
      send : ∀{i} -> Γ ⊢ ◻ X Locally -> Γ ⊢ Tr (X i) Locally

      -- Tr monad
      pure : Γ ⊢ A Locally -> Γ ⊢ Tr A Locally
      seq : Γ ⊢ Tr A Locally
          -> Γ , A ⊢ Tr B Locally
          -> Γ ⊢ Tr B Locally

      -- tuples/modalities
      proj : Γ ⊢ ◻ X Locally -> ∀ n -> Γ ⊢ X n Locally
      box : (∀ n -> Γ ⊢ X n Locally) -> Γ ⊢ ◻ X Locally

      -- functions
      lam : Γ , A ⊢ B Locally -> Γ ⊢ A ⇒ B Locally
      app : Γ ⊢ A ⇒ B Locally -> Γ ⊢ A Locally -> Γ ⊢ B Locally

      -- products
      _,_ : Γ ⊢ A Locally -> Γ ⊢ B Locally -> Γ ⊢ A ×× B Locally
      fst-×× : Γ ⊢ A ×× B Locally -> Γ ⊢ A Locally
      snd-×× : Γ ⊢ A ×× B Locally -> Γ ⊢ B Locally
      tt : Γ ⊢ Unit Locally

      -- coproducts
      left : Γ ⊢ A Locally -> Γ ⊢ Either A B Locally
      right : Γ ⊢ B Locally -> Γ ⊢ Either A B Locally
      either : Γ ⊢ Either A B Locally
               -> Γ , A ⊢ C Locally
               -> Γ , B ⊢ C Locally
               -> Γ ⊢ C Locally

      -- lists
      [] : Γ ⊢ Lst A Locally
      _∷_ : Γ ⊢ A Locally -> Γ ⊢ Lst A Locally -> Γ ⊢ Lst A Locally
      rec-Lst : Γ ⊢ Lst A Locally
                -> Γ ⊢ C Locally
                -> (Γ , A) , C ⊢ C Locally
                -> Γ ⊢ C Locally

    _⊢_ : ⊢Ctx -> ⊢Type -> 𝒰₀
    _⊢_ Γ X = ∀ n -> Γ n ⊢ X n Locally

  open [Std𝔓roc/Definition::Term]

  _⋆-LCtx_ : LCtx -> LCtx -> LCtx
  _⋆-LCtx_ Γ Δ = {!!}


  wk : Γ ⊢ A Locally -> Γ , B ⊢ A Locally
  wk = {!!}

  subst : (∀ B -> Γ ⊢Var B Locally -> Δ ⊢ B Locally) -> Γ ⊢ A Locally -> Δ ⊢ A Locally
  subst = {!!}



  λStdProc : STT _
  λStdProc = record
    { Ctx = ⊢Ctx
    ; Type = ⊢Type
    ; Term = λ Γ A -> Γ ⊢ A
    }

instance
  hasParamSTT:StdProc : hasParamSTT (Std𝔓roc)
  hasParamSTT:StdProc = record
    { Param = λ This -> ⊤-𝒰 {ℓ₀}
    ; _at_ = λ This _ -> Std𝔓roc/Definition.λStdProc This
    ; SubParam = λ _ _ -> ⊤-𝒰 {ℓ₀}
    }

