module KamiCore.FFI.Parser.Definition where

open import Agora.Conventions

{-# FOREIGN GHC import Parser.Definition #-}

record Name : 𝒰₀ where
  constructor mkName
  field getName : Text
{-# COMPILE GHC Name = data Name (Name) #-}

data Location : 𝒰₀ where
  L0 L1 L2 : Location
{-# COMPILE GHC Location = data Location (L0 | L1 | L2) #-}

data Modality : 𝒰₀ where
    At : Location -> Modality
    Box : Modality
{-# COMPILE GHC Modality = data Modality (At | Box) #-}

data TypeVal : 𝒰₀ where
    Fun Prod Sum : TypeVal -> TypeVal -> TypeVal
    Modal : Modality -> TypeVal -> TypeVal
    Lst : TypeVal -> TypeVal
    Unit : TypeVal
{-# COMPILE GHC TypeVal = data TypeVal (Fun | Prod | Sum | Modal | List | Unit) #-}

data FunArg : 𝒰₀ where
  mkFunArg : Name -> TypeVal -> FunArg
{-# COMPILE GHC FunArg = data FunArg (FunArg) #-}

data TermVal : 𝒰₀ where
  Var : Name -> TermVal
  Lam : FunArg -> TermVal -> TermVal
  App : TermVal -> TermVal -> TermVal

  Fst Snd : TermVal -> TermVal
  MkProd : TermVal -> TermVal -> TermVal

  Left Right : TermVal -> TermVal
  Either : TermVal -> TermVal -> TermVal -> TermVal

  Nil : TermVal
  Cons : TermVal -> TermVal -> TermVal
  ListRec : TermVal -> TermVal -> TermVal -> TermVal

  TT : TermVal
  Check : TermVal -> TypeVal -> TermVal

{-# COMPILE GHC TermVal = data TermVal (Var | Lam | App | Fst | Snd | MkProd | Left' | Right' | Either' | Nil | Cons | ListRec | TT | Check) #-}

-- data Statement : 𝒰₀ where
--   TypeDef : Name -> TypeVal -> Statement
--   TermDef : Name -> List Name -> TermVal -> Statement
-- Toplevel = List Statement


