
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.F.Model4 where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder


module _ {Loc : Preorder 𝑖} where

  private variable
    k l : ⟨ Loc ⟩

  data LocalType : 𝒰 𝑖
  data Type : ⟨ Loc ⟩ -> 𝒰 𝑖

  data Comm (l : ⟨ Loc ⟩) : 𝒰 𝑖 where
    comm : Type l -> ⟨ Loc ⟩ -> Comm l
    _∥_ : Comm l -> Comm l -> Comm l
    _≫_ : Comm l -> Comm l -> Comm l
    𝟘 : Comm l

  data LocalType where
    box : Type l -> LocalType
    NN : LocalType
    Either : LocalType -> LocalType -> LocalType

  data Type where
    _at_ : LocalType -> (l : ⟨ Loc ⟩) -> Type l
    _[_]⇒_ : Type l -> Comm l -> Type l -> Type l

  infix 30 _at_
  infix 45 _[_]⇒_

  data Ctx : 𝒰 𝑖 where
    ε : Ctx
    _,_ : Ctx -> Type l -> Ctx

  private variable
    Γ Δ : Ctx
    A B C : Type l
    K L M N : LocalType
    c d : Comm l
    -- r s :  Loc

  data _⊢[_]_ : Ctx -> Comm l -> Type l -> 𝒰 𝑖
  data _⊢_//_ : Ctx -> LocalType -> ⟨ Loc ⟩ -> 𝒰 𝑖
  data _⇛[_]_ : Ctx -> Comm l -> Ctx -> 𝒰 𝑖


  _⊢_ : Ctx -> Type l -> 𝒰 𝑖
  _⊢_ Γ A = Γ ⊢[ 𝟘 ] A

  data _⊢[_]_ where
    broadcast : Γ ⊢ box A at l -> Γ ⊢[ comm A l ] A
    lam : Γ , A ⊢[ c ] B -> Γ ⊢ A [ c ]⇒ B
    app : Γ ⊢ A [ c ]⇒ B -> Γ ⊢ A -> Γ ⊢[ c ] B
    seq : Γ ⊢[ c ] A -> Γ , A ⊢[ d ] B -> Γ ⊢[ c ≫ d ] B

  data _⊢_//_ where
    rec-Either : Γ ⊢ Either K L // l
               -> Γ , K at l ⊢ M // l
               -> Γ , L at l ⊢ M // l
               -> Γ ⊢ M // l

  data _⇛[_]_ where
    ε : Γ ⇛[ 𝟘 {l = l} ] ε
    _,_ : Γ ⇛[ c ] Δ -> Γ ⊢[ d ] A -> Γ ⇛[ c ∥ d ] Δ , A





