
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorProc.Definition where

open import Data.List using (drop)

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
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding (Mode)
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category

open import KamiCore.Language.ChorMTT.Definition


module _ {A : 𝒰 𝑖} where
  data _≼_ : List A -> List A -> 𝒰 𝑖 where
    done : ∀{as} -> [] ≼ as
    take : ∀{x as bs} -> as ≼ bs -> x ∷ as ≼ x ∷ bs
    skip : ∀{x as bs} -> as ≼ bs -> as ≼ x ∷ bs

  split-≼ : ∀ ps qs -> ∀{U V} -> (ps <> (U ∷ [])) ≼ (qs <> (V ∷ [])) -> (ps ≼ qs ×-𝒰 U ≡ V) +-𝒰 (ps <> (U ∷ []) ≼ qs)
  split-≼ [] [] (take P) = left (done , refl-≡)
  split-≼ [] (x ∷ qs) (take P) = yes (take (done))
  split-≼ [] (x ∷ qs) (skip P) with split-≼ [] qs P
  ... | no (P , Q) = no (skip P , Q)
  ... | yes P = yes (skip P)
  split-≼ (x ∷ ps) (.x ∷ qs) (take P) with split-≼ (ps) qs P
  ... | no (P , Q) = no (take P , Q)
  ... | yes P = yes (take P)
  split-≼ (x ∷ ps) (x₁ ∷ qs) (skip P) with split-≼ (x ∷ ps) qs P
  ... | no (P , Q) = no (skip P , Q)
  ... | yes P = yes (skip P)
  split-≼ (x ∷ []) [] (take ())
  split-≼ (x ∷ []) [] (skip ())
  split-≼ (x ∷ x₁ ∷ ps) [] (take ())
  split-≼ (x ∷ x₁ ∷ ps) [] (skip ())

  data _≼'_ : List A -> List A -> 𝒰 𝑖 where
    [] : [] ≼' []
    _∷_ : ∀ a -> ∀{as bs} -> as ≼ bs -> a ∷ as ≼' a ∷ bs



record ChorProc 𝑗 : 𝒰 (𝑗 ⁺) where
  field Proc : StrictOrder 𝑗
  field allProcs : 𝒫ᶠⁱⁿ Proc

open ChorProc public


module _ 𝑗 where macro Chor𝔓roc = #structureOn (ChorProc 𝑗)

module Chor𝔓roc/Definition (This : Chor𝔓roc 𝑗) where
  postulate instance
    hasDecidableEquality:P : hasDecidableEquality (𝒫ᶠⁱⁿ (This .Proc))
    isProp:≤-P : ∀{a b : 𝒫ᶠⁱⁿ (This .Proc)} -> isProp (a ≤ b)

  Super : Chor𝔐TT _
  Super = record
    { Roles = 𝒫ᶠⁱⁿ (This .Proc)
    ; hasDecidableEquality:Roles = it
    ; isProp:≤-Roles = it
    }

  open Chor𝔐TT/Definition Super

  module [Chor𝔓roc/Definition::Param] where
    open [Chor𝔐TT/Definition::Param] public
    variable
      p q k l : ⟨ Proc This ⟩
      ps qs ks ls : 𝒫ᶠⁱⁿ (Proc This)
      -- is js : List ⟨ Proc L ⟩

    data ProcMode : 𝒰₀ where
      ◯ ▲ : ProcMode

    ⟦_⟧-Mode : Param Super -> ProcMode
    ⟦_⟧-Mode ◯ = ◯
    ⟦_⟧-Mode (▲ U) = ▲


  open [Chor𝔓roc/Definition::Param]

  private Mode = Param Super

  module [Chor𝔓roc/Definition::Type] where
    data ⊢Type : ProcMode -> 𝒰 𝑗

    data ⊢Type where
      ◻ : ⊢Type ◯ -> ⊢Type ▲
      -- [_∣_]◅_ : ⊢Type ◯ -> (𝒫ᶠⁱⁿ (Proc This)) ×-𝒰 List (𝒫ᶠⁱⁿ (Proc This)) -> ⊢Type ▲ -> ⊢Type ▲
      -- _∥_ : ⊢Type ▲ -> ⊢Type ▲ -> ⊢Type ▲
      NN : ∀{m} -> ⊢Type m
      Unit : ∀{m} -> ⊢Type m
      Either : ∀{m} -> ⊢Type m -> ⊢Type m -> ⊢Type m
      _⇒_ : ∀{m} -> ⊢Type m -> ⊢Type m -> ⊢Type m
      _××_ : ∀{m} -> ⊢Type m -> ⊢Type m -> ⊢Type m
      Tr : ∀{m} -> ⊢Type m -> ⊢Type m
      located : (l : 𝒫ᶠⁱⁿ (Proc This)) -> ⊢Type ▲ -> ⊢Type ◯

    syntax located l A = A ＠ l

    infix 30 located

    variable
      -- U : 𝒫ᶠⁱⁿ (Proc This)
      X Y : ⊢Type ◯
      A B C : ⊢Type ▲

    mutual
      data π_∣_↦_Type : ⊢Type ◯ -> ((𝒫ᶠⁱⁿ (Proc This)) ×-𝒰 List (𝒫ᶠⁱⁿ (Proc This))) -> ⊢Type ▲ -> 𝒰 (𝑗) where
        proj-＠ : ∀{ps pps qs A B} -> ps ≤ qs -> ω A ∣ pps ↦ B Type -> π A ＠ qs ∣ ps , pps ↦ B Type
        proj-＠-≠ : ∀{ps pps qs A} -> (¬ ps ≤ qs) -> π A ＠ qs ∣ ps , pps ↦ Unit Type
        _⇒_ : ∀{p ps A B} -> π X ∣ p , ps ↦ A Type -> π Y ∣ p , ps ↦ B Type -> π (X ⇒ Y) ∣ p , ps ↦ (A ⇒ B) Type
        _××_ : ∀{p ps A B} -> π X ∣ p , ps ↦ A Type -> π Y ∣ p , ps ↦ B Type -> π (X ×× Y) ∣ p , ps ↦ (A ×× B) Type
        Either : ∀{p ps A B} -> π X ∣ p , ps ↦ A Type -> π Y ∣ p , ps ↦ B Type -> π (Either X Y) ∣ p , ps ↦ Either A B Type
        Tr : ∀{p ps A } -> π X ∣ p , ps ↦ A Type -> π (Tr X) ∣ p , ps ↦ Tr A Type
        Unit : ∀{p ps} -> π Unit ∣ p , ps ↦ Unit Type

      data ω_∣_↦_Type : ⊢Type ▲ -> List (𝒫ᶠⁱⁿ (Proc This)) -> ⊢Type ▲ -> 𝒰 (𝑗) where
        done : ∀{A} -> ω A ∣ [] ↦ A Type
        proj-◻ : ∀{p ps A} -> π X ∣ p , ps ↦ A Type -> ω ◻ X ∣ p ∷ ps ↦ A Type
        Unit : ∀{p ps} -> ω Unit ∣ p ∷ ps ↦ Unit Type

  open [Chor𝔓roc/Definition::Type]


  module [Chor𝔓roc/Definition::Ctx] where
    data ⊢Ctx : 𝒰 𝑗 where
      ε : ⊢Ctx
      _,[_] : ⊢Ctx -> 𝒫ᶠⁱⁿ (Proc This) -> ⊢Ctx
      _,_ : ⊢Ctx -> ⊢Type ◯ -> ⊢Ctx

    variable
      Γ Δ : ⊢Ctx

    data _∣_↦_Ctx : ⊢Ctx -> (l : List (𝒫ᶠⁱⁿ (Proc This))) -> ⊢Ctx -> 𝒰 (𝑗) where
      ε : ∀{p} -> ε ∣ ⦗ p ⦘ ∷ [] ↦ ε Ctx
      _,_ : ∀{p ps A} -> Γ ∣ p ∷ ps ↦ Δ Ctx -> π X ∣ p , [] ↦ A Type -> Γ , X ∣ p ∷ ps ↦ (Δ , A ＠ p) Ctx
      stepRes : ∀{p ps} -> Γ ∣ p ∷ ps ↦ Δ Ctx -> Γ ,[ p ] ∣ ps ↦ Δ ,[ p ] Ctx


  open [Chor𝔓roc/Definition::Ctx]

  module [Chor𝔓roc/Definition::Term] where

    data _⊢Var_GlobalFiber[_] : (Γ : ⊢Ctx) -> (A : ⊢Type ▲) -> List (𝒫ᶠⁱⁿ (Proc This)) -> 𝒰 (𝑗) where
      zero : ∀{p qs ps} -> ps ≼ qs -> π X ∣ p , ps ↦ A Type -> Γ , X ⊢Var A GlobalFiber[ p ∷ qs ]
      suc : ∀{ps} -> Γ ⊢Var A GlobalFiber[ ps ] -> Γ , X ⊢Var A GlobalFiber[ ps ]
      res : ∀{p ps} -> Γ ⊢Var A GlobalFiber[ p ∷ ps ] -> Γ ,[ p ] ⊢Var A GlobalFiber[ ps ]
      none : ∀{p ps} -> Γ , X ⊢Var Unit GlobalFiber[ p ∷ ps ]


    record _⊢_GlobalFibered[_] (Γ : ⊢Ctx) (X : ⊢Type ◯) (ps : 𝒫ᶠⁱⁿ (Proc This)) : 𝒰 (𝑗)


    data _⊢_GlobalFiber[_] : (Γ : ⊢Ctx) -> (A : ⊢Type ▲) -> ⟨ Proc This ⟩ -> 𝒰 (𝑗) where
      var : ∀{p} -> (v : Γ ⊢Var A GlobalFiber[ ⦗ p ⦘ ∷ [] ]) -> Γ ⊢ A GlobalFiber[ p ]

      recv : π X ∣ ⦗ p ⦘ , [] ↦ A Type -> Γ ⊢ Tr A GlobalFiber[ p ]

      send : (v : π X ∣ ⦗ p ⦘ , [] ↦ A Type)
            -- -> unbox δ₀ ∣ p ↦ δ₁ Com
            -> Γ ⊢ ◻ X GlobalFiber[ p ]
            -> Γ ⊢ Tr A GlobalFiber[ p ]

      extern : Γ ,[ ⦗ q ⦘ ] ⊢ A GlobalFiber[ p ] -> Γ ⊢ A GlobalFiber[ p ]

      lam : Γ , A ＠ ⦗ p ⦘ ⊢ B GlobalFiber[ p ] -> Γ ⊢ A ⇒ B GlobalFiber[ p ]
      app : Γ ⊢ A ⇒ B GlobalFiber[ p ] -> Γ ⊢ A GlobalFiber[ p ] -> Γ ⊢ B GlobalFiber[ p ]

      tt : Γ ⊢ Unit GlobalFiber[ p ]

      box' : Γ ,[ ⦗ p ⦘ ] ⊢ X GlobalFibered[ ps ]
            -> Γ ⊢ ◻ X GlobalFiber[ p ]


    record _⊢_GlobalFibered[_] Γ X ps where
      inductive ; constructor incl
      field ⟨_⟩ : ∀ p -> p ∈ ⟨ ps ⟩ -> ∀ {A} -> (Xp : π X ∣ ⦗ p ⦘ , [] ↦ A Type)
                  -> ∀ {Δ} -> (Γp : Γ ∣ ⦗ p ⦘ ∷ [] ↦ Δ Ctx)
                  -- -> ∑ λ δ' -> δ ∣ p ↦ δ' Com ×-𝒰
                  -> Δ ⊢ A GlobalFiber[ p ]

    open _⊢_GlobalFibered[_] public


    _⊢_ : ⊢Ctx -> ⊢Type ◯ -> 𝒰 𝑗
    _⊢_ Γ X = Γ ⊢ X GlobalFibered[ allProcs This ]

  open [Chor𝔓roc/Definition::Term]


  λChorProc : STT _
  λChorProc = record
    { Ctx = ⊢Ctx
    ; Type = ⊢Type ◯
    ; Term = λ Γ A -> Γ ⊢ A
    }


instance
  hasParamSTT:ChorProc : hasParamSTT (ChorProc 𝑗)
  hasParamSTT:ChorProc = record
    { Param = λ _ -> ⊤-𝒰 {ℓ₀}
    ; SubParam = λ _ _ -> ⊤-𝒰 {ℓ₀}
    ; _at_ = λ This _ -> Chor𝔓roc/Definition.λChorProc This
    }

