
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.Kami.Setup where

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

open 𝔐TT/Definition Source public
open [𝔐TT/Definition::Type] renaming (⊢Type to 𝔐TT⊢Type) public
open [𝔐TT/Definition::Ctx] renaming (⊢Ctx to 𝔐TT⊢Ctx) public
open [𝔐TT/Definition::Term] renaming (_⊢_ to _𝔐TT⊢_) public
open Variables/Type public
open 𝔐TT/Properties Source public


open import KamiCore.Language.ChorMTT.Definition public
open Chor𝔐TT/Definition Chor public
open [Chor𝔐TT/Definition::Param] public


open import KamiCore.Language.StdProc.Definition public
open import KamiTheory.Data.UniqueSortedList.Definition public
open import KamiTheory.Data.UniqueSortedList.Properties public
open import KamiTheory.Data.UniqueSortedList.NonEmpty public
open import KamiTheory.Data.UniqueSortedList.Instance.Preorder public

-- well-scoped but not typed

RR = P

Error = String


-- data Mode : 𝒰₀ where
--   Local Global : Mode
Mode = ⟨ 𝓂 ⟩


-- data ⊢Type_ : Mode -> 𝒰₀ where

Modality' : Mode -> Mode -> 𝒰₀
Modality' a b = Hom {{(of ↳ 𝓂)}} a b
