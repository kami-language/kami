
module KamiCore.Pipeline.Main where

open import Agora.Conventions

sayhello : Text -> Text
sayhello xs = "hello, " <> xs
{-# COMPILE GHC sayhello as sayhello #-}

open import KamiCore.FFI.Parser.Definition

{-# FOREIGN GHC import qualified Data.Text as T #-}
postulate
  showTerm : TermVal -> Text
{-# COMPILE GHC showTerm = T.pack . show #-}

isLambda : TermVal -> Text
isLambda t@(Lam x xs) = "Lambda!"
isLambda (_) = "No lambda :("
{-# COMPILE GHC isLambda as isLambda #-}

