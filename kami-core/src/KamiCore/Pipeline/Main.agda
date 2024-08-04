
module KamiCore.Pipeline.Main where

open import Agora.Conventions

sayhello : Text -> Text
sayhello xs = "hello, " <> xs
{-# COMPILE GHC sayhello as sayhello #-}
