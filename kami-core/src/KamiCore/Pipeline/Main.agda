
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Pipeline.Main where

open import Agora.Conventions

sayhello : Text -> Text
sayhello xs = "hello, " <> xs
{-# COMPILE GHC sayhello as sayhello #-}

open import KamiCore.Foreign.Parser.Definition

{-# FOREIGN GHC import qualified Data.Text as T #-}
postulate
  showTerm : TermVal -> Text
{-# COMPILE GHC showTerm = T.pack . show #-}

isLambda : TermVal -> Text
isLambda t@(Lam x xs) = "Lambda!"
isLambda (_) = "No lambda :("
{-# COMPILE GHC isLambda as isLambda #-}


open import KamiCore.Language.Kami.Raw

approximateTypecheck : TermVal -> Text
approximateTypecheck t with infer {Γ = ε} t Global
... | left e = e
... | right _ = "done"
{-# COMPILE GHC approximateTypecheck as approximateTypecheck #-}
