
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

Local : Location -> Mode
Local l = ▲ (tr-loc l)

Global : Mode
Global = ◯

show-Mode : Mode -> String
show-Mode ◯ = "Global"
show-Mode (▲ _) = "Local ?"

instance
  IShow:Mode : IShow Mode
  IShow:Mode = record { show = show-Mode }

-- show-Modality : ∀{m n : Mode} -> m ⟶ n -> String
-- show-Modality = {!!}

-- instance
--   IShow:Modality : ∀{m n : Mode} -> IShow (m ⟶ n)
--   IShow:Modality = record { show = show-Modality }

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



⟨_∣*_⟩ : ∀{m n} -> 𝔐TT⊢Type m -> m ⟶ n -> 𝔐TT⊢Type n
⟨ A ∣* id' ⟩ = A
⟨ A ∣* `＠` U ⨾ x₁ ⟩ = ⟨ ⟨ A ∣ `＠` U ⨾ id' ⟩ ∣* x₁ ⟩
⟨ A ∣* `[]` ⨾ x₁ ⟩ = ⟨ ⟨ A ∣ `[]` ⨾ id' ⟩ ∣* x₁ ⟩

-- deconstruct : ∀{a} -> (A : 𝔐TT⊢Type a) -> ∑ λ b -> ∑ λ (μ : b ⟶ a) -> ∑ λ B -> ⟨ B ∣* μ ⟩ ≡ A
-- deconstruct ⟨ A ∣ x ⟩
--   with (_ , μ , B , refl-≡) <- deconstruct A
--   = {!!}
--   -- let _ , μ , B , p = deconstruct A
--   -- in _ , (μ ◆' x) , {!!}
-- deconstruct Unit = {!!}
-- deconstruct (Tr A) = {!!}
-- deconstruct (Either A A₁) = {!!}
-- deconstruct (Lst A) = {!!}
-- deconstruct (⟮ A ∣ x ⟯⇒ A₁) = {!!}

withDeconstruct : ∀{X : 𝒰 𝑖} -> ∀{a} -> (A : 𝔐TT⊢Type a) -> ((∑ λ b -> ∑ λ (μ : b ⟶ a) -> ∑ λ B -> ⟨ B ∣* μ ⟩ ≡ A) -> X) -> X
withDeconstruct ⟨ A ∣ id' ⟩ F = F (_ , id' , ⟨ A ∣ id' ⟩ , refl-≡)
withDeconstruct ⟨ A ∣ x ⨾ id' ⟩ F = withDeconstruct A λ {(_ , μ , B , refl-≡) -> F (_ , (μ ◆' (x ⨾ id')) , B , {!!})}
withDeconstruct ⟨ A ∣ x ⨾ xs ⨾ ys ⟩ F = F (_ , id' , ⟨ A ∣ x ⨾ xs ⨾ ys ⟩ , refl-≡)
-- withDeconstruct A λ {(_ , μ , B , refl-≡) -> F (_ , μ , B , {!!})}
withDeconstruct Z F = F (_ , id' , Z , refl-≡)
-- withDeconstruct Unit F = {!!}
-- withDeconstruct (Tr A) F = {!!}
-- withDeconstruct (Either A A₁) F = {!!}
-- withDeconstruct (Lst A) F = {!!}
-- withDeconstruct (⟮ A ∣ x ⟯⇒ A₁) F = {!!}

data _⊢Var_ : Ctx -> ∀{a} -> 𝔐TT⊢Type a -> 𝒰₀ where
  zero : ∀{m n μ A} -> Γ , (x , (m , n , μ , A)) ⊢Var A
  suc : ∀{m} -> ∀{A : 𝔐TT⊢Type m} -> ∀{y} -> Γ ⊢Var A -> Γ , y ⊢Var A


data _⊢_ : Ctx -> ∀{m} -> 𝔐TT⊢Type m -> 𝒰₀ where
  var : Γ ⊢Var A -> Γ ⊢ A
  var' : Γ ⊢Var A -> Γ ⊢ ⟨ A ∣* μ ⟩

  mod : ∀{m n : Mode} {A : 𝔐TT⊢Type m} -> (μ : m ⟶ n) -> Γ ⊢ A -> Γ ⊢ ⟨ A ∣ μ ⟩

  lam : ∀ x  -> Γ , (x , (_ , _ , μ , A)) ⊢ B -> Γ ⊢ ⟮ A ∣ μ ⟯⇒ B
  app : Γ ⊢ ⟮ A ∣ μ ⟯⇒ B -> Γ ⊢ A -> Γ ⊢ B

  left : Γ ⊢ A -> Γ ⊢ Either A B
  right : Γ ⊢ B -> Γ ⊢ Either A B

  rec-Either : Γ ⊢ Either ⟨ A ∣* μ ⟩ ⟨ B ∣* ν ⟩
               -> Γ , (x , (_ , _ , μ , A)) ⊢ C
               -> Γ , (x , (_ , _ , ν , B)) ⊢ C
               -> Γ ⊢ C

  rec-Lst : Γ ⊢ Lst ⟨ A ∣* μ ⟩
               -> Γ ⊢ ⟨ C ∣* ν ⟩
               -> (Γ , (x , (_ , _ , μ , A))) , (x , (_ , _ , ν , C)) ⊢ ⟨ C ∣* ν ⟩
               -> Γ ⊢ ⟨ C ∣* ν ⟩

  nil : Γ ⊢ Lst A
  cons : Γ ⊢ A -> Γ ⊢ Lst A -> Γ ⊢ Lst A

  tt : ∀{m} -> Γ ⊢ Unit {m}

wk : ∀{x Y} -> Γ ⊢ A -> Γ , (x , Y) ⊢ A
wk = {!!}

infer-Var : (x : Name) (m : Mode) -> Error +-𝒰 (∑ λ (A : 𝔐TT⊢Type m) -> Γ ⊢Var A)
infer-Var {Γ = ε} x m = no $ "No variable " <> show x <> " in scope"
infer-Var {Γ = Γ , (y , (n , _ , μ , A))} x m =
  if cmp-Name x y
    then (withModeEquality m n λ {refl-≡ -> right $ A , zero})
    else do
      A' , v <- infer-Var {Γ = Γ} x m
      return $ A' , suc v


withArrow : ∀{m} {X : 𝒰 𝑖}
          -> (F : 𝔐TT⊢Type m)
          -> ((∑ λ n -> ∑ λ μ -> ∑ λ (A : 𝔐TT⊢Type n) -> ∑ λ (B : 𝔐TT⊢Type m) -> F ≡ ⟮ A ∣ μ ⟯⇒ B) -> Error +-𝒰 X)
          -> Error +-𝒰 X
withArrow (⟮ A ∣ μ ⟯⇒ B) t = t (_ , μ , A , B , refl-≡)
withArrow X t = left $ "Expected function type, but got: " <> show X

withModal : ∀{m} {X : 𝒰 𝑖}
          -> (F : 𝔐TT⊢Type m)
          -> ((∑ λ n -> ∑ λ μ -> ∑ λ (A : 𝔐TT⊢Type n) -> F ≡ ⟨ A ∣ μ ⟩) -> Error +-𝒰 X)
          -> Error +-𝒰 X
withModal (⟨ A ∣ μ ⟩) t = t (_ , μ , A , refl-≡)
withModal X t = left $ "Expected modal type, but got: " <> show X

withSum : ∀{m} {X : 𝒰 𝑖}
          -> (F : 𝔐TT⊢Type m)
          -> ((∑ λ (A : 𝔐TT⊢Type m) -> ∑ λ (B : 𝔐TT⊢Type m) -> F ≡ Either A B) -> Error +-𝒰 X)
          -> Error +-𝒰 X
withSum (Either A B) t = t (A , B , refl-≡)
withSum X t = left "Expected sum type"

withLst : ∀{m} {X : 𝒰 𝑖}
          -> (F : 𝔐TT⊢Type m)
          -> ((∑ λ (A : 𝔐TT⊢Type m) -> F ≡ Lst A) -> Error +-𝒰 X)
          -> Error +-𝒰 X
withLst (Lst A) t = t (A , refl-≡)
withLst X t = left "Expected list type"

_&&_ : {X : 𝒰 𝑖} {A : 𝒰 𝑗} {B : 𝒰 𝑘}
     -> (∀ {X : 𝒰 𝑖} -> (A -> Error +-𝒰 X) -> Error +-𝒰 X)
     -> (∀ {X : 𝒰 𝑖} -> (B -> Error +-𝒰 X) -> Error +-𝒰 X)
     -> (((A ×-𝒰 B) -> Error +-𝒰 X) -> Error +-𝒰 X)
_&&_ F G ϕ = F λ a -> G λ b -> ϕ (a , b)

infixr 30 _&&_


check : TermVal -> (m : Mode) -> (A : 𝔐TT⊢Type m) -> Error +-𝒰 (Γ ⊢ A)

infer : TermVal -> (m : Mode) -> Error +-𝒰 (∑ λ (A : 𝔐TT⊢Type m) -> Γ ⊢ A)
infer (Var x) m = mapRight (λ (A , v) -> (A , var v)) (infer-Var x m)
infer (Mod μ t) m = do
  n , μ' <- modecheck-modality μ m
  A , t' <- infer t n
  return $ _ , mod μ' t'
infer (Lam (NameFunArg x) t) m = left "encountered lambda without type annotation in a place where it is required"
infer (Lam (TypeFunArg x A) t) m = do
  n , μ , A' <- modecheck' A m
  B' , t' <- infer t m
  right (⟮ A' ∣ μ ⟯⇒ B' , lam x t')
infer (App t s) m = do
  F , t' <- infer t m
  withArrow F λ {(n , μ , A , B , refl-≡) -> do
    s' <- check s n A
    return (B , app t' s')
    }
    -- withTypeEquality A A' λ {refl-≡ -> do
    --   return (B , app t' s')}}

infer (Fst t) m = left "not implemented: product types"
infer (Snd t) m = left "not implemented: product types"
infer (MkProd t t₁) m = left "not implemented: product types"
infer (Left t) m = left "encountered `left` in a place where the required type is unknown"
infer (Right t) m = left "encountered `right` in a place where the required type is unknown"
infer {Γ = Γ} (Either x f g) m = do
  X , x' <- infer x m
  withSum X λ {(A , B , refl-≡) -> do
    F , f' <- infer f m
    G , g' <- infer {Γ = Γ} g m
    (withArrow F && withArrow G) λ {((_ , μ , A' , Y' , refl-≡) , (_ , ν , B' , Z' , refl-≡)) -> do
      (withTypeEquality ⟨ A' ∣* μ ⟩ A && withTypeEquality ⟨ B' ∣* ν ⟩ B && withTypeEquality Y' Z') λ {(refl-≡ , refl-≡ , refl-≡) -> do
        return $ Z' , rec-Either {μ = μ} {ν = ν} {x = mkName "either-var"} x' (app (wk f') (var zero)) ((app (wk g') (var zero))) 
        }
      }
    }
infer Nil m = left "encountered `Nil` in a place where the required type is unknown"
infer (Cons x xs) m = do
  X , x' <- infer x m
  xs' <- check xs m (Lst X)
  return (Lst X , cons x' xs' )
infer (ListRec xs fnil fcons) m = do
  XS , xs' <- infer xs m
  withLst XS λ {(X , refl-≡) -> do
    Z , fnil' <- infer fnil m
    Fcons , fcons' <- infer fcons m
    withArrow Fcons λ {(_ , μ0 , F0 , F12 , refl-≡) -> do
      withArrow F12 λ {(_ , μ1 , F1 , F2 , refl-≡) -> do
        (withTypeEquality ⟨ F0 ∣* μ0 ⟩ X && withTypeEquality F2 Z && withTypeEquality ⟨ F1 ∣* μ1 ⟩ F2) λ {(refl-≡ , refl-≡ , refl-≡) -> do
          return $ F2 , rec-Lst {μ = μ0} {ν = μ1} {x = mkName "lstrec-var"} xs' fnil' (app (app (wk (wk fcons')) (var (suc zero))) (var zero))
          }
        }
      }
    }
infer TT m = right $ _ , tt
infer (Check t x) m = do
  X <- modecheck x m
  x' <- check t m X
  return $ X , x'



-- check (Var x) m A = do
--   withDeconstruct A λ {(n , μ , A' , refl-≡) -> do
--     A'' , v <- infer-Var x n
--     withTypeEquality A'' A' λ {refl-≡ -> do
--       right $ var' {μ = μ} v
--       }
--     }

check (Var x) m A = do
    A'' , v <- infer-Var x m
    withTypeEquality A'' A λ {refl-≡ -> do
      right $ var v
      }
check (Mod μ t) m A = do
  n , μ' <- modecheck-modality μ m
  withModal A λ {(n'' , μ'' , A'' , refl-≡) -> do
    withModeEquality n n'' λ {refl-≡ -> do
      withModalityEquality μ' μ'' λ {refl-≡ -> do
        t' <- check t n'' A''
        return $ mod μ' t'
        }
      }
    }
check {Γ = Γ} (Lam (NameFunArg x) t) m F = do
  withArrow F λ {(_ , μ₀ , A2 , B , refl-≡) -> do
    t' <- check {Γ = Γ , (x , (_ , _ , μ₀ , A2))} t m B
    right (lam x t')
    }
check {Γ = Γ} (Lam (TypeFunArg x A) t) m F = do
  n , μ , A' <- modecheck' A m
  withArrow F λ {(_ , μ₀ , A2 , B , refl-≡) -> do
    t' <- check {Γ = Γ , (x , (_ , _ , μ , A'))} t m B
    (withTypeEquality ⟨ A' ∣ μ ⟩ ⟨ A2 ∣ μ₀ ⟩) λ {refl-≡ -> do
        right (lam x t')
      }
    }
check (App t s) m B = do
  F , t' <- infer t m
  withArrow F λ {(n , μ , A' , B' , refl-≡) -> do
    s' <- check s n A'
    withTypeEquality B B' λ {refl-≡ -> do
      return (app t' s')
      }}
check (Fst t) m A = left "not implemented"
check (Snd t) m A = left "not implemented"
check (MkProd t t₁) m A = left "not implemented"
check (Left t) m X = do
  withSum X λ {(A , B , refl-≡) -> do
    t' <- check t m A
    return (left t')
    }
check (Right t) m X = do
  withSum X λ {(A , B , refl-≡) -> do
    t' <- check t m B
    return (right t')
    }
check {Γ = Γ} (Either x f g) m Res = do
  X , x' <- infer x m
  withSum X λ {(A , B , refl-≡) -> do
    (withDeconstruct A && withDeconstruct B) λ {((_ , μ' , A' , refl-≡) , (_ , ν' , B' , refl-≡)) -> do
      f' <- check f m (⟮ A' ∣ μ' ⟯⇒ Res)
      g' <- check g m (⟮ B' ∣ ν' ⟯⇒ Res)
      return $ rec-Either {μ = μ'} {ν = ν'} {x = mkName "either-var"} x' (app (wk f') (var zero)) ((app (wk g') (var zero)))
      }
    }
check Nil m A = left "not implemented"
check (Cons t t₁) m A = left "not implemented"
check (ListRec t t₁ t₂) m A = left "not implemented"
check TT m A = do
  withTypeEquality A Unit λ {refl-≡ ->
    return tt
    }
check (Check t x) m A = do
  X <- modecheck x m
  withTypeEquality X A λ {refl-≡ -> do
      x' <- check t m X
      return $ x'
    }

