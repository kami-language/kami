
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
open import KamiTheory.Data.UniqueSortedList.Properties
open import KamiTheory.Data.UniqueSortedList.NonEmpty
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding (Mode)
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category

open import KamiCore.Language.ChorMTT.Definition


module _ {A : 𝒰 𝑖} where
  -- data _≼_ : List A -> List A -> 𝒰 𝑖 where
  --   done : ∀{as} -> [] ≼ as
  --   take : ∀{x as bs} -> as ≼ bs -> x ∷ as ≼ x ∷ bs
  --   skip : ∀{x as bs} -> as ≼ bs -> as ≼ x ∷ bs

  split-≼ : ∀ (ps qs : List A) -> ∀{U V} -> (ps <> (U ∷ [])) ≼ (qs <> (V ∷ [])) -> (ps ≼ qs ×-𝒰 U ≡ V) +-𝒰 (ps <> (U ∷ []) ≼ qs)
  split-≼ [] [] (take P) = left (done , refl-≡)
  split-≼ [] (x ∷ qs) (take P) = yes (take ([]≼))
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
  field {{isFiniteStrictOrder:Proc}} : isFiniteStrictOrder Proc
  field {{hasDecidableEquality:Proc}} : hasDecidableEquality ⟨ Proc ⟩
  field allProcs : 𝒫₊ᶠⁱⁿ Proc
  field inAllProcs : ∀{a} -> a ∈ ⟨ fst allProcs ⟩

open ChorProc public


module _ 𝑗 where macro Chor𝔓roc = #structureOn (ChorProc 𝑗)

module Chor𝔓roc/Definition (This : Chor𝔓roc 𝑗) where
  postulate instance
    -- hasDecidableEquality:Proc : hasDecidableEquality ⟨(This .Proc)⟩
    -- hasDecidableEquality:P : hasDecidableEquality (𝒫₊ᶠⁱⁿ (This .Proc))
    isProp:≤-P : ∀{a b : 𝒫₊ᶠⁱⁿ (This .Proc)} -> isProp (a ≤ b)

  Super : Chor𝔐TT _
  Super = record
    { Roles = 𝒫₊ᶠⁱⁿ (This .Proc)
    ; hasDecidableEquality:Roles = it
    ; isProp:≤-Roles = it
    }

  open Chor𝔐TT/Definition Super

  module [Chor𝔓roc/Definition::Param] where
    open [Chor𝔐TT/Definition::Param] public
    variable
      p q k l : ⟨ Proc This ⟩
      ps qs ks ls : 𝒫₊ᶠⁱⁿ (Proc This)
      -- is js : List ⟨ Proc L ⟩

    data ProcMode : 𝒰₀ where
      ◯ ▲ : ProcMode

    ⟦_⟧-Mode : Param Super -> ProcMode
    ⟦_⟧-Mode ◯ = ◯
    ⟦_⟧-Mode (▲ U) = ▲

    -- record Intersected (ps qs : 𝒫₊ᶠⁱⁿ (Proc This)) : 𝒰 𝑗 where
    --   field ⟨_⟩ : ∑ λ p -> ⦗ p ⦘₊ ≤ ps ∧ qs
    -- open Intersected public
    -- findCommon : ∀ (ps qs : 𝒫₊ᶠⁱⁿ (Proc This)) -> (ps ∧ qs ∼ ⊥) +-𝒰 Intersected ps qs
    -- findCommon = {!!}

  open [Chor𝔓roc/Definition::Param]

  private Mode = Param Super

  module [Chor𝔓roc/Definition::Type] where
    data ⊢Type : ProcMode -> 𝒰 𝑗

    data ⊢Type where
      ◻ : ⊢Type ◯ -> ⊢Type ▲
      -- [_∣_]◅_ : ⊢Type ◯ -> (𝒫₊ᶠⁱⁿ (Proc This)) ×-𝒰 List (𝒫₊ᶠⁱⁿ (Proc This)) -> ⊢Type ▲ -> ⊢Type ▲
      -- _∥_ : ⊢Type ▲ -> ⊢Type ▲ -> ⊢Type ▲
      -- NN : ∀{m} -> ⊢Type m
      Unit : ∀{m} -> ⊢Type m
      Either : ∀{m} -> ⊢Type m -> ⊢Type m -> ⊢Type m
      Lst : ∀{m} -> ⊢Type m -> ⊢Type m
      _⇒_ : ∀{m} -> ⊢Type m -> ⊢Type m -> ⊢Type m
      _××_ : ∀{m} -> ⊢Type m -> ⊢Type m -> ⊢Type m
      Tr : ∀{m} -> ⊢Type m -> ⊢Type m
      _＠_ : ⊢Type ▲ -> (𝒫₊ᶠⁱⁿ (Proc This))-> ⊢Type ◯

    infix 30 _＠_

    variable
      -- U : 𝒫₊ᶠⁱⁿ (Proc This)
      X Y Z : ⊢Type ◯
      A B C : ⊢Type ▲

    mutual
      data π_∣_↦_Type : ⊢Type ◯ -> ((𝒫₊ᶠⁱⁿ (Proc This)) ×-𝒰 List (𝒫₊ᶠⁱⁿ (Proc This))) -> ⊢Type ▲ -> 𝒰 (𝑗) where
        proj-＠ : ∀{ps pps qs A B} -> ps ≤ qs -> ω A ∣ pps ↦ B Type -> π A ＠ qs ∣ ps , pps ↦ B Type
        proj-＠-≠ : ∀{ps pps qs A} -> ¬ (ps ≤ qs) -> π A ＠ qs ∣ ps , pps ↦ Unit Type
        _⇒_ : ∀{p A B} -> π X ∣ ⦗ p ⦘₊ , [] ↦ A Type -> π Y ∣ ⦗ p ⦘₊ , [] ↦ B Type -> π (X ⇒ Y) ∣ ⦗ p ⦘₊ , [] ↦ (A ⇒ B) Type
        _××_ : ∀{p A B} -> π X ∣ ⦗ p ⦘₊ , [] ↦ A Type -> π Y ∣ ⦗ p ⦘₊ , [] ↦ B Type -> π (X ×× Y) ∣ ⦗ p ⦘₊ , [] ↦ (A ×× B) Type
        Either : ∀{p A B} -> π X ∣ ⦗ p ⦘₊ , [] ↦ A Type -> π Y ∣ ⦗ p ⦘₊ , [] ↦ B Type -> π (Either X Y) ∣ ⦗ p ⦘₊ , [] ↦ Either A B Type
        Tr : ∀{p A } -> π X ∣ ⦗ p ⦘₊ , [] ↦ A Type -> π (Tr X) ∣ ⦗ p ⦘₊ , [] ↦ Tr A Type
        Lst : ∀{p A } -> π X ∣ ⦗ p ⦘₊ , [] ↦ A Type -> π (Lst X) ∣ ⦗ p ⦘₊ , [] ↦ Lst A Type
        Unit : ∀{p } -> π Unit ∣ ⦗ p ⦘₊ , [] ↦ Unit Type
        break-π : ∀{p q rs Ps Qs} -> isNot＠ X -> π X ∣ (((p ∷ q ∷ rs) since Ps) , Qs) , [] ↦ Unit Type

      data πS_∣_↦_Type : ⊢Type ◯ -> ((𝒫₊ᶠⁱⁿ (Proc This)) ×-𝒰 List (𝒫₊ᶠⁱⁿ (Proc This))) -> ⊢Type ▲ -> 𝒰 (𝑗) where
        proj-＠ : ∀{ps pps qs A B} -> ps ≤ qs -> ω A ∣ pps ↦ B Type -> πS A ＠ qs ∣ ps , pps ↦ B Type
        proj-＠-≠ : ∀{ps pps qs A} -> ¬ (ps ≤ qs) -> πS A ＠ qs ∣ ps , pps ↦ Unit Type
        break-π : ∀{ps rs} -> isNot＠ X -> πS X ∣ ps , rs ↦ Unit Type

        -- _⇒_ : ∀{p ps A B} -> π X ∣ p , ps ↦ A Type -> π Y ∣ p , ps ↦ B Type -> π (X ⇒ Y) ∣ p , ps ↦ (A ⇒ B) Type
        -- _××_ : ∀{p ps A B} -> π X ∣ p , ps ↦ A Type -> π Y ∣ p , ps ↦ B Type -> π (X ×× Y) ∣ p , ps ↦ (A ×× B) Type
        -- Either : ∀{p ps A B} -> π X ∣ p , ps ↦ A Type -> π Y ∣ p , ps ↦ B Type -> π (Either X Y) ∣ p , ps ↦ Either A B Type
        -- Tr : ∀{p ps A } -> π X ∣ p , ps ↦ A Type -> π (Tr X) ∣ p , ps ↦ Tr A Type
        -- Lst : ∀{p ps A } -> π X ∣ p , ps ↦ A Type -> π (Lst X) ∣ p , ps ↦ Lst A Type
        -- Unit : ∀{p ps} -> π Unit ∣ p , ps ↦ Unit Type

      data ω_∣_↦_Type : ⊢Type ▲ -> List (𝒫₊ᶠⁱⁿ (Proc This)) -> ⊢Type ▲ -> 𝒰 (𝑗) where
        done : ∀{A} -> ω A ∣ [] ↦ A Type
        proj-◻ : ∀{p ps A} -> π X ∣ p , ps ↦ A Type -> ω ◻ X ∣ p ∷ ps ↦ A Type
        Unit : ∀{p ps} -> ω Unit ∣ p ∷ ps ↦ Unit Type
        -- _⇒_ : ∀{p ps A₀ A₁ B₀ B₁} -> ω A₀ ∣ p ∷ ps ↦ A₁ Type -> ω B₀ ∣ p ∷ ps ↦ B₁ Type -> ω (A₀ ⇒ B₀) ∣ p ∷ ps ↦ (A₁ ⇒ B₁) Type
        -- _××_ : ∀{p ps A₀ A₁ B₀ B₁} -> ω A₀ ∣ p ∷ ps ↦ A₁ Type -> ω B₀ ∣ p ∷ ps ↦ B₁ Type -> ω (A₀ ×× B₀) ∣ p ∷ ps ↦ (A₁ ×× B₁) Type

    -- data α_∣_↦_Type : ⊢Type ◯ -> (𝒫₊ᶠⁱⁿ (Proc This) ×-𝒰 List (𝒫₊ᶠⁱⁿ (Proc This))) -> ⊢Type ▲ -> 𝒰 (𝑗) where
    --   proj-＠ : ∀{ps pps qs A B} -> ps ≤ qs -> ω A ∣ pps ↦ B Type -> α A ＠ qs ∣ ps , pps ↦ B Type
    --   proj-＠-≠ : ∀{ps pps qs A} -> ¬ (ps ≤ qs) -> α A ＠ qs ∣ ps , pps ↦ Unit Type
      -- proj-＠ : ∀{ps pps qs A B} -> ⦗ qs ⦘₊ ≤ ps -> ω A ∣ pps ↦ B Type -> α A ＠ ⦗ qs ⦘₊ ∣ ps , pps ↦ B Type
      -- proj-＠-≠ : ∀{ps pps qs A} -> (¬ ⦗ qs ⦘₊ ≤ ps) -> α A ＠ ⦗ qs ⦘₊ ∣ ps , pps ↦ Unit Type


      data isNot＠ : ⊢Type ◯ -> 𝒰 𝑗 where
        is-⇒ : isNot＠ (X ⇒ Y)
        is-×× : isNot＠ (X ×× Y)
        is-Either : isNot＠ (Either X Y)
        is-Tr : isNot＠ ((Tr X))
        is-Lst : isNot＠ ((Lst X))
        is-Unit : isNot＠ (Unit)

      -- Idea: if we are on a sublevel (p , (r ∷ rs)) then everything which is a global type which is not an ＠, gets projected to Unit.
      data γ_∣_↦_Type : ⊢Type ◯ -> ((𝒫₊ᶠⁱⁿ (Proc This)) ×-𝒰 List (𝒫₊ᶠⁱⁿ (Proc This))) -> ⊢Type ▲ -> 𝒰 (𝑗) where
        toplevel : ∀{p X A} -> π X ∣ p , [] ↦ A Type -> γ X ∣ p , [] ↦ A Type
        sublevel-＠ : ∀{ps qs r rs A} -> ps ≤ qs -> γ A ＠ qs ∣ ps , (r ∷ rs) ↦ A Type
        sublevel-＠-≠ : ∀{ps qs r rs A} -> ¬ (ps ≤ qs) -> γ A ＠ qs ∣ ps , (r ∷ rs) ↦ Unit Type
        sublevel-break : ∀{ps r rs} -> isNot＠ X -> γ X ∣ ps , (r ∷ rs) ↦ Unit Type
        -- sublevel-break-⇒ : ∀{X Y ps r rs} -> γ X ⇒ Y ∣ ps , (r ∷ rs) ↦ Unit Type
        -- sublevel-break-×× : ∀{p r rs} -> γ (X ×× Y) ∣ isNot＠
        -- sublevel-break-Either : ∀{p r rs} -> γ (Either X Y) ∣ isNot＠
        -- sublevel-break-Tr : ∀{p r rs} -> γ (Tr X) ∣ isNot＠
        -- sublevel-break-Lst : ∀{p r rs} -> γ (Lst X) ∣ isNot＠
        -- sublevel-break-Unit : ∀{p r rs} -> γ Unit ∣ isNot＠



  open [Chor𝔓roc/Definition::Type]


  module [Chor𝔓roc/Definition::Ctx] where
    data ⊢Ctx : 𝒰 𝑗 where
      ε : ⊢Ctx
      _,[_] : ⊢Ctx -> 𝒫₊ᶠⁱⁿ (Proc This) -> ⊢Ctx
      _,_ : ⊢Ctx -> ⊢Type ◯ -> ⊢Ctx

    variable
      Γ Δ : ⊢Ctx

    data _∣_↦_Ctx : ⊢Ctx -> (l : List (𝒫₊ᶠⁱⁿ (Proc This))) -> ⊢Ctx -> 𝒰 (𝑗) where
      done : Γ ∣ [] ↦ Γ Ctx
      ε : ∀{p ps} -> ε ∣ p ∷ ps ↦ ε Ctx
      _,_ : ∀{p ps A} -> Γ ∣ p ∷ ps ↦ Δ Ctx -> γ X ∣ p , ps ↦ A Type -> Γ , X ∣ p ∷ ps ↦ (Δ , A ＠ p) Ctx
      stepRes : ∀{p ps} -> Γ ∣ p ∷ ps ↦ Δ Ctx -> Γ ,[ p ] ∣ ps ↦ Δ ,[ p ] Ctx


    data isLocal : (l : (𝒫₊ᶠⁱⁿ (Proc This))) -> ⊢Ctx -> 𝒰 (𝑗) where
      ε : ∀{l} -> isLocal l ε
      _,_ : ∀{Γ l} -> isLocal l Γ -> ∀ A -> isLocal l (Γ , A ＠ l )
      stepRes : ∀{Γ k l} -> isLocal l Γ -> isLocal k (Γ ,[ l ])

  open [Chor𝔓roc/Definition::Ctx]

  module [Chor𝔓roc/Definition::Term] where

    data _⊢Var_GlobalFiber[_] : (Γ : ⊢Ctx) -> (A : ⊢Type ▲) -> List (𝒫₊ᶠⁱⁿ (Proc This)) -> 𝒰 (𝑗) where
      zero : ∀{p qs ps} -> ps ≼ qs -> π X ∣ p , ps ↦ A Type -> Γ , X ⊢Var A GlobalFiber[ p ∷ qs ]
      suc : ∀{ps} -> Γ ⊢Var A GlobalFiber[ ps ] -> Γ , X ⊢Var A GlobalFiber[ ps ]
      res : ∀{p ps} -> Γ ⊢Var A GlobalFiber[ p ∷ ps ] -> Γ ,[ p ] ⊢Var A GlobalFiber[ ps ]
      none : ∀{p ps} -> Γ , X ⊢Var Unit GlobalFiber[ p ∷ ps ]


    record _⊢_GlobalFibered[_] (Γ : ⊢Ctx) (X : ⊢Type ◯) (ps : 𝒫₊ᶠⁱⁿ (Proc This)) : 𝒰 (𝑗)


    data _⊢_GlobalFiber[_] : (Γ : ⊢Ctx) -> (A : ⊢Type ▲) -> ⟨ Proc This ⟩ -> 𝒰 (𝑗) where
      var : ∀{p} -> (v : Γ ⊢Var A GlobalFiber[ ⦗ p ⦘₊ ∷ [] ]) -> Γ ⊢ A GlobalFiber[ p ]

      -- communication

      recv : π X ∣ ⦗ p ⦘₊ , [] ↦ A Type -> Γ ⊢ Tr A GlobalFiber[ p ]

      send : (v : π X ∣ ⦗ p ⦘₊ , [] ↦ A Type)
            -- -> unbox δ₀ ∣ p ↦ δ₁ Com
            -> Γ ⊢ ◻ X GlobalFiber[ p ]
            -> Γ ⊢ Tr A GlobalFiber[ p ]

      -- box' : ∀ {qs} -> ⦗ p ⦘₊ ≤ qs -> Γ ,[ qs ] ⊢ X GlobalFibered[ allProcs This ]
      --      -> Γ ∣ ⦗ p ⦘₊ ∷ [] ↦ Δ Ctx
      --       -> Δ ⊢ ◻ X GlobalFiber[ p ]

      box' : Γ ,[ ⦗ p ⦘₊ ] ⊢ X GlobalFibered[ allProcs This ]
            -> Γ ⊢ ◻ X GlobalFiber[ p ]

      -- transformations
      pure : Γ ⊢ A GlobalFiber[ p ] -> Γ ⊢ Tr A GlobalFiber[ p ]
      seq : Γ ⊢ Tr A GlobalFiber[ p ]
            -> Γ , A ＠ ⦗ p ⦘₊  ⊢ Tr B GlobalFiber[ p ]
            -> Γ ⊢ Tr B GlobalFiber[ p ]

      -- functions
      lam : Γ , A ＠ ⦗ p ⦘₊ ⊢ B GlobalFiber[ p ] -> Γ ⊢ A ⇒ B GlobalFiber[ p ]
      app : Γ ⊢ A ⇒ B GlobalFiber[ p ] -> Γ ⊢ A GlobalFiber[ p ] -> Γ ⊢ B GlobalFiber[ p ]

      -- unit type
      tt : Γ ⊢ Unit GlobalFiber[ p ]

      -- sum types
      left : Γ ⊢ A GlobalFiber[ p ] -> Γ ⊢ Either A B GlobalFiber[ p ]
      right : Γ ⊢ B GlobalFiber[ p ] -> Γ ⊢ Either A B GlobalFiber[ p ]
      either : Γ ⊢ Either A B GlobalFiber[ p ]
        -> Γ , A ＠ ⦗ p ⦘₊ ⊢ C GlobalFiber[ p ]
        -> Γ , B ＠ ⦗ p ⦘₊ ⊢ C GlobalFiber[ p ]
        -> Γ ⊢ C GlobalFiber[ p ]

      -- list types
      [] : Γ ⊢ Lst A GlobalFiber[ p ]
      _∷_ : Γ ⊢ A GlobalFiber[ p ] -> Γ ⊢ Lst A GlobalFiber[ p ] -> Γ ⊢ Lst A GlobalFiber[ p ]
      rec-Lst : Γ ⊢ Lst A GlobalFiber[ p ]
        -> Γ ⊢ C GlobalFiber[ p ]
        -> (Γ , A ＠ ⦗ p ⦘₊) , C ＠ ⦗ p ⦘₊ ⊢ C GlobalFiber[ p ]
        -> Γ ⊢ C GlobalFiber[ p ]



    record _⊢_GlobalFibered[_] Γ X ps where
      inductive ; constructor incl
      field ⟨_⟩ : ∀ p -> p ∈ ⟨ fst ps ⟩ -> ∀ {A} -> (Xp : π X ∣ ⦗ p ⦘₊ , [] ↦ A Type)
                  -> ∀ {Δ} -> (Γp : Γ ∣ ⦗ p ⦘₊ ∷ [] ↦ Δ Ctx)
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

