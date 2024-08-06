
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.Kami.Raw where

open import Agora.Conventions hiding (n ; _∣_)
open import Agora.Data.Sum.Definition
open import Agora.Data.Fin.Definition
open import Agora.Category.Std.Category.Definition
open import KamiCore.Foreign.Parser.Definition
open import KamiCore.Pipeline.Definition
open import KamiCore.Language.MTT.Definition
open import KamiCore.Language.MTT.Properties
open import KamiTheory.Basics
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding (Mode)
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import Agda.Builtin.String using () renaming (primStringEquality to _==-String_)

cmp-Name : Name -> Name -> Bool
cmp-Name x y = getName x ==-String getName y

n : ℕ
n = 2

_>>=_ = bind-+-𝒰

return : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} -> B -> A + B
return = right

open Generic n using (Source ; Chor)

𝓂 = ModeTheory Source 

open 𝔐TT/Definition Source
open [𝔐TT/Definition::Type] renaming (⊢Type to 𝔐TT⊢Type)
open [𝔐TT/Definition::Ctx] renaming (⊢Ctx to 𝔐TT⊢Ctx)
open [𝔐TT/Definition::Term] renaming (_⊢_ to _𝔐TT⊢_)
open Variables/Type
open 𝔐TT/Properties Source


open import KamiCore.Language.ChorMTT.Definition
open Chor𝔐TT/Definition Chor
open [Chor𝔐TT/Definition::Param]


open import KamiCore.Language.StdProc.Definition
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.UniqueSortedList.Properties
open import KamiTheory.Data.UniqueSortedList.NonEmpty
open import KamiTheory.Data.UniqueSortedList.Instance.Preorder

-- well-scoped but not typed

RR = P

Error = String


-- data Mode : 𝒰₀ where
--   Local Global : Mode
Mode = ⟨ 𝓂 ⟩

-- data ⊢Type_ : Mode -> 𝒰₀ where

Modality' : Mode -> Mode -> 𝒰₀
Modality' a b = Hom {{(of ↳ 𝓂)}} a b

data Ctx : 𝒰₀ where
  ε : Ctx
  _,_ : Ctx -> Name ×-𝒰 (∑ λ m -> ∑ λ n -> Modality' m n ×-𝒰 𝔐TT⊢Type m) -> Ctx

private variable Γ : Ctx
private variable x y : Name

tr-loc : Location -> 𝒫₊ᶠⁱⁿ (𝔽 (suc n))
tr-loc L0 = ⦗ zero ⦘₊
tr-loc L1 = ⦗ suc zero ⦘₊
tr-loc L2 = ⦗ suc (suc zero) ⦘₊

modecheck' : TypeVal -> (m : Mode) -> Error +-𝒰 (∑ λ n -> (Modality' n m) ×-𝒰 𝔐TT⊢Type n)
modecheck : TypeVal -> (m : Mode) -> Error +-𝒰 (𝔐TT⊢Type m)
modecheck-modality : Modality -> (m : Mode) -> Error +-𝒰 (∑ λ n -> Modality' n m)
modecheck-modality (At x) m with m ≟ ◯ -- (▲ (tr-loc x))
... | no x₁ = left "encountered an ＠ modality but target mode is not global "
... | yes refl-≡ = right $ _ , (`＠` (tr-loc x) ⨾ id')
modecheck-modality Box (▲ x) = right $ _ , `[]` ⨾ id'
modecheck-modality Box ◯ = left "encountered a {} modality but target mode is not local"

modecheck (Fun A B) m = do
  n , μ , A'  <- modecheck' A m
  B' <- modecheck B m
  return (⟮ A' ∣ μ ⟯⇒ B')
modecheck (Prod A B) m = do
  A' <- modecheck A m
  B' <- modecheck B m
  left "Products currently not implemented" -- {!A' ×× B'!}
modecheck (Sum A B) m = do
  A' <- modecheck A m
  B' <- modecheck B m
  return (Either A' B')
modecheck (Modal A B) m = do
  n , μ <- modecheck-modality A m
  B' <- modecheck B n
  return ⟨ B' ∣ μ ⟩
modecheck (Lst A) m = do
  A' <- modecheck A m
  return (Lst A')
modecheck Unit m = do
  return Unit

modecheck' (Modal A B) m = do
  n , μ <- modecheck-modality A m
  k , ν , B' <- modecheck' B n
  return $ _ , (ν ◆' μ) , B'
modecheck' A m = do
  A' <- modecheck A m
  return $ m , id , A'

data _⊢Var_ : Ctx -> ∀{a} -> 𝔐TT⊢Type a -> 𝒰₀ where
  zero : ∀{m n μ A} -> Γ , (x , (m , n , μ , A)) ⊢Var A
  suc : ∀{m} -> ∀{A : 𝔐TT⊢Type m} -> ∀{y} -> Γ ⊢Var A -> Γ , y ⊢Var A

data _⊢_ : Ctx -> ∀{m} -> 𝔐TT⊢Type m -> 𝒰₀ where
  var : Γ ⊢Var A -> Γ ⊢ A

  lam : ∀ x  -> Γ , (x , (_ , _ , μ , A)) ⊢ B -> Γ ⊢ ⟮ A ∣ μ ⟯⇒ B
  app : Γ ⊢ ⟮ A ∣ μ ⟯⇒ B -> Γ ⊢ A -> Γ ⊢ B

  tt : ∀{m} -> Γ ⊢ Unit {m}

typecheck-Var : (x : Name) (m : Mode) -> Error +-𝒰 (∑ λ (A : 𝔐TT⊢Type m) -> Γ ⊢Var A)
typecheck-Var {Γ = ε} x m = no $ "No variable " <> show x <> " in scope"
typecheck-Var {Γ = Γ , (y , (n , _ , μ , A))} x m =
  if cmp-Name x y
    then (withModeEquality m n λ {refl-≡ -> right $ A , zero})
    else do
      A' , v <- typecheck-Var {Γ = Γ} x m
      return $ A' , suc v


withArrow : ∀{m} {X : 𝒰 𝑖}
          -> (F : 𝔐TT⊢Type m)
          -> ((∑ λ n -> ∑ λ μ -> ∑ λ (A : 𝔐TT⊢Type n) -> ∑ λ (B : 𝔐TT⊢Type m) -> F ≡ ⟮ A ∣ μ ⟯⇒ B) -> Error +-𝒰 X)
          -> Error +-𝒰 X
withArrow (⟮ A ∣ μ ⟯⇒ B) t = t (_ , μ , A , B , refl-≡)
withArrow X t = left "Expected function type on left side of application"


typecheck : TermVal -> (m : Mode) -> Error +-𝒰 (∑ λ (A : 𝔐TT⊢Type m) -> Γ ⊢ A)
typecheck (Var x) m = mapRight (λ (A , v) -> (A , var v)) (typecheck-Var x m)
typecheck (Lam (mkFunArg x A) t) m = do
  n , μ , A' <- modecheck' A m
  B' , t' <- typecheck t m
  right (⟮ A' ∣ μ ⟯⇒ B' , lam x t')
typecheck (App t s) m = do
  F , t' <- typecheck t m
  withArrow F λ {(n , μ , A , B , refl-≡) -> do
    A' , s' <- typecheck s n
    withTypeEquality A A' λ {refl-≡ -> do
      return (B , app t' s')}}

typecheck (Fst t) = {!!}
typecheck (Snd t) = {!!}
typecheck (MkProd t t₁) = {!!}
typecheck (Left t) = {!!}
typecheck (Right t) = {!!}
typecheck (Either t t₁ t₂) = {!!}
typecheck Nil = {!!}
typecheck (Cons t t₁) = {!!}
typecheck (ListRec t t₁ t₂) = {!!}
typecheck TT m = right $ _ , tt
typecheck (Check t x) = {!!}


