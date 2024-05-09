
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.F.Model4 where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder


module _ {Loc : Preorder 𝑖} where

  private variable
    k l : ⟨ Loc ⟩
    ks ls : List ⟨ Loc ⟩

  data LocalType : 𝒰 𝑖
  data Type : ⟨ Loc ⟩ -> 𝒰 𝑖

  data Comm (l : ⟨ Loc ⟩) : 𝒰 𝑖 where
    comm : Type l -> ⟨ Loc ⟩ -> Comm l
    _∥_ : Comm l -> Comm l -> Comm l
    _≫_ : Comm l -> Comm l -> Comm l
    𝟘 : Comm l

  data LocalType where
    -- the boxing operator:
    -- actually the list of locations should be the
    -- partition of `l`.
    ◻_∣_ : Type l -> List ⟨ Loc ⟩ -> LocalType
    NN : LocalType
    Either : LocalType -> LocalType -> LocalType

  infix 40 ◻_∣_

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
    X Y Z : Type l
    A B C D : LocalType
    c d : Comm l
    -- r s :  Loc

  data _⊢[_]_ : Ctx -> Comm l -> Type l -> 𝒰 𝑖
  data _⊢_//_ : Ctx -> LocalType -> ⟨ Loc ⟩ -> 𝒰 𝑖
  data _⇛[_]_ : Ctx -> Comm l -> Ctx -> 𝒰 𝑖


  _⊢_ : Ctx -> Type l -> 𝒰 𝑖
  _⊢_ Γ A = Γ ⊢[ 𝟘 ] A

  data _⊢[_]_ where
    broadcast : Γ ⊢ ◻ X ∣ ks at l -> Γ ⊢[ comm X l ] X
    lam : Γ , X ⊢[ c ] Y -> Γ ⊢ X [ c ]⇒ Y
    app : Γ ⊢ X [ c ]⇒ Y -> Γ ⊢ X -> Γ ⊢[ c ] Y
    seq : Γ ⊢[ c ] X -> Γ , X ⊢[ d ] Y -> Γ ⊢[ c ≫ d ] Y

  data _＠_↦_ : Type l -> ⟨ Loc ⟩ -> LocalType -> 𝒰 𝑖 where

  data _⊢◻_∣_//_ : Ctx -> Type l -> List ⟨ Loc ⟩ -> ⟨ Loc ⟩ -> 𝒰 𝑖 where
    [] : Γ ⊢◻ X ∣ [] // l
    _,_by_ : Γ ⊢◻ X ∣ ks // l -> X ＠ k ↦ A -> Γ ⊢ A // l -> Γ ⊢◻ X ∣ (k ∷ ks) // l

  data _⊢_//_ where
    rec-Either : Γ ⊢ Either A B // l
               -> Γ , A at l ⊢ C // l
               -> Γ , B at l ⊢ C // l
               -> Γ ⊢ C // l

    box : Γ ⊢◻ X ∣ ks // l -> Γ ⊢ ◻ X ∣ ks // l






  data _⇛[_]_ where
    ε : Γ ⇛[ 𝟘 {l = l} ] ε
    _,_ : Γ ⇛[ c ] Δ -> Γ ⊢[ d ] X -> Γ ⇛[ c ∥ d ] Δ , X





