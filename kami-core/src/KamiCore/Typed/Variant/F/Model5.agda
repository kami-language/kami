
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.F.Model5 where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice

module _ {Loc : Preorder 𝑖} {{_ : hasFiniteMeets Loc}} (split : ⟨ Loc ⟩ -> List ⟨ Loc ⟩) where


  private variable
    k l : ⟨ Loc ⟩
    ks ls : List ⟨ Loc ⟩

  data ▲Type : 𝒰 𝑖
  data ◯Type : ⟨ Loc ⟩ -> 𝒰 𝑖

  data Comm (l : ⟨ Loc ⟩) : 𝒰 𝑖 where
    comm : ◯Type l -> ⟨ Loc ⟩ -> Comm l
    _∥_ : Comm l -> Comm l -> Comm l
    _≫_ : Comm l -> Comm l -> Comm l
    𝟘 : Comm l

  data ▲Type where
    -- the boxing operator:
    -- actually the list of locations should be the
    -- partition of `l`.
    ◻_∣_ : ◯Type l -> List ⟨ Loc ⟩ -> ▲Type
    NN : ▲Type
    Either : ▲Type -> ▲Type -> ▲Type

  infix 40 ◻_∣_

  data ◯Type where
    _＠_ : ▲Type -> (l : ⟨ Loc ⟩) -> ◯Type l
    _⇒_ : ◯Type l -> ◯Type l -> ◯Type l

  infix 30 _＠_
  infix 45 _⇒_

  data ◯Ctx : 𝒰 𝑖 where
    ε : ◯Ctx
    _,_ : ◯Ctx -> ◯Type l -> ◯Ctx

  data ▲Ctx : 𝒰 𝑖 where
    ε : ▲Ctx
    _,_ : ▲Ctx -> ▲Type -> ▲Ctx

  private variable
    Γ Δ : ◯Ctx
    X Y Z : ◯Type l
    A B C D : ▲Type
    c d : Comm l
    -- r s :  Loc

  data _⊢_ : ◯Ctx -> ◯Type l -> 𝒰 𝑖
  data _⊢_//_ : ◯Ctx -> ▲Type -> ⟨ Loc ⟩ -> 𝒰 𝑖
  data _⇛_ : ◯Ctx -> ◯Ctx -> 𝒰 𝑖


  -- _⊢_ : ◯Ctx -> ◯Type l -> 𝒰 𝑖
  -- _⊢_ Γ A = Γ ⊢[ 𝟘 ] A

  data _⊢_ where
    broadcast : Γ ⊢ ◻ X ∣ ks ＠ l -> Γ ⊢ X
    lam : Γ , X ⊢ Y -> Γ ⊢ X ⇒ Y
    app : Γ ⊢ X ⇒ Y -> Γ ⊢ X -> Γ ⊢ Y
    -- seq : Γ ⊢ X -> Γ , X ⊢ Y -> Γ ⊢ Y

  data _＠_↦_ : ◯Type l -> ⟨ Loc ⟩ -> ▲Type -> 𝒰 𝑖 where


  data _⊢◻_∣_//_ : ◯Ctx -> ◯Type l -> List ⟨ Loc ⟩ -> ⟨ Loc ⟩ -> 𝒰 𝑖 where
    [] : Γ ⊢◻ X ∣ [] // l
    _,_by_ : Γ ⊢◻ X ∣ ks // l -> X ＠ k ↦ A -> Γ ⊢ A // l -> Γ ⊢◻ X ∣ (k ∷ ks) // l

  data _⊢_//_ where
    rec-Either : Γ ⊢ Either A B // l
               -> Γ , A ＠ l ⊢ C // l
               -> Γ , B ＠ l ⊢ C // l
               -> Γ ⊢ C // l

    box : Γ ⊢◻ X ∣ ks // l -> Γ ⊢ ◻ X ∣ ks // l


  data _⇛_ where
    ε : Γ ⇛ ε
    _,_ : Γ ⇛ Δ -> Γ ⊢ X -> Γ ⇛ Δ , X


  ----------------------------------------------------------
  -- Constructing the categories
  --
  -- The local categories.
  -- Note that the Loc here is the location where the local
  -- type should be located (ergo we don't have ∨, but have
  -- an ∧ operation)
  ▲Obj : ⟨ Loc ⟩ -> 𝒰 𝑖
  ▲Obj _ = ▲Type


  -- The global category.
  -- Note that the loc here is the range of processes that
  -- participate in the choreography, thus only should contain
  -- ∨ operations).
  ◯Obj : 𝒰 𝑖
  ◯Obj = ∑ λ l -> ◯Type l

  ----------------------------------------------------------
  -- Constructing the functors
  --
  -- 1) from local to global by using "＠"
  --
  -- The object map
  F＠ : ∀ l -> ▲Obj l -> ◯Obj
  F＠ l A = _ , A ＠ l
  --
  -- The arrow map
  -- map-F＠ : ∀{l} -> 

  -- 2) from global to local by using ◻
  F◻ : ∀ l -> ◯Obj -> ▲Obj l
  F◻ l (k , X) = ◻ X ∣ split k



