

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

--
-- Purpose: Function types don't have modalites,
-- mod introduces always single modalities
--

module KamiCore.Language.MinMTT.Properties where

open import Agora.Conventions hiding (m ; n ; k ; _∣_)
open import Agora.Data.Product.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.TypeTheory.STT.Definition
open import Agora.TypeTheory.ParamSTT.Definition


open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')

open import KamiCore.Language.MTT.Definition
open import KamiCore.Language.MinMTT.Definition




module Min𝔐TT/Properties (This : Min𝔐TT 𝑖) where
  open Min𝔐TT/Definition This
  open [Min𝔐TT/Definition::Private]
  open [Min𝔐TT/Definition::Type]
  open [Min𝔐TT/Definition::Ctx]
  open [Min𝔐TT/Definition::Term]

  private variable
    a b c : 𝓂


  preserve-◆-Mod-Type : {μ : Path _⟶ₛ_ a b} {ν : Path _⟶ₛ_ b c}
                      -> Mod-Type (μ ◆' ν) A ≡ Mod-Type ν (Mod-Type μ A)
  preserve-◆-Mod-Type {μ = id'} = refl-≡
  preserve-◆-Mod-Type {μ = x ⨾ μ} = preserve-◆-Mod-Type {μ = μ}


