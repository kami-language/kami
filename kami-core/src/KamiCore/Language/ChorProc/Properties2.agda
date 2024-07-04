


{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorProc.Properties2 where

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
open import KamiCore.Language.ChorProc.Definition
open import KamiCore.Language.ChorProc.Properties




module Chor𝔓roc/Properties2 (This : Chor𝔓roc 𝑗) where
  open Chor𝔓roc/Definition This
  open [Chor𝔓roc/Definition::Param]
  open [Chor𝔓roc/Definition::Type]
  open [Chor𝔓roc/Definition::Ctx]
  open [Chor𝔓roc/Definition::Term]
  open Chor𝔓roc/Properties This


  --------------------------------------------------------------------
  -- Helpers for the variable cases
  --------------------------------------------------------------------

  cons : ∀{A : 𝒰 𝑙} -> A × List A -> List A
  cons (a , as) = a ∷ as


  postpend : ∀{A : 𝒰 𝑙} -> (List A) -> A -> A × List A
  postpend [] x = x , []
  postpend (x ∷ xs) z = x , cons (postpend xs z)

  rev' : ∀{A : 𝒰 𝑙} -> List A -> List A
  rev' [] = []
  rev' (x ∷ xs) = cons (postpend (rev' xs) x)

  transl-Mod3 : ◯ ⟶ a -> (List (𝒫ᶠⁱⁿ (Proc This)))
  transl-Mod3 id' = []
  transl-Mod3 (`[]` ⨾ id') = []
  transl-Mod3 (`[]` ⨾ `＠` U ⨾ ω) = U ∷ transl-Mod3 ω

  F2-Type : (List (𝒫ᶠⁱⁿ (Proc This))) -> ⊢Type ◯ -> ⊢Type ◯
  F2-Type [] X = X
  F2-Type (x ∷ xs) X = ◻ (F2-Type xs X) ＠ x

  F2-comp : ∀{X } -> ∀ xs ys -> F2-Type (xs <> ys) X ≡ F2-Type xs (F2-Type ys X)
  F2-comp [] ys = refl-≡
  F2-comp (x ∷ xs) ys = cong-≡ (λ X -> ◻ X ＠ x) (F2-comp xs ys)

  -------------------------
  -- properties

  F-prop : ∀{X} -> F-Type μ X ≡ F2-Type (rev (transl-Mod3 μ)) X
  F-prop {μ = id'} = refl-≡
  F-prop {μ = `[]` ⨾ `＠` U ⨾ μ} {X = X} =
    let Z = F-prop {μ = μ} {X = (◻ X ＠ U)}
    in Z ∙-≡ sym-≡ (F2-comp (rev (transl-Mod3 μ)) _ )

  rev≡rev' : ∀{A : 𝒰 𝑖} (as : List A) -> rev as ≡ rev' as
  rev≡rev' = {!!}


  private
    split-ψ : (ψ : ⊢ModeHom (▲ U) ◯) -> ∑ λ V -> ∑ λ ψ' -> ψ ≡ ψ' ◆' (`＠` V ⨾ id')
    split-ψ (`＠` W ⨾ id') = W , id' , refl-≡
    split-ψ (`＠` W ⨾ `[]` ⨾ ϕ) with split-ψ ϕ
    ... | V , ϕ' , refl-≡ = V , `＠` W ⨾ `[]` ⨾ ϕ' , refl-≡

    into-≼' : {ϕ₀ ϕ₁ : ⊢ModeHom ◯ (▲ V)}
            -> rev (transl-Mod3 ϕ₀) ≼ rev (transl-Mod3 ϕ₁)
            -> rev (transl-Mod3 (ϕ₀ ◆' (`＠` V ⨾ id'))) ≼' rev (transl-Mod3 (ϕ₁ ◆' (`＠` V ⨾ id')))
    into-≼' = {!!}

    module _ {A : 𝒰 𝑖} where
      add-element : {xs ys zs : List A} -> xs ≼ ys -> xs <> zs ≼ ys <> zs
      add-element done = id-≼
      add-element (skip p) = skip (add-element p)
      add-element (take p) = take (add-element p)

      ι₀-<> : {as bs : List A} -> as ≼ as <> bs
      ι₀-<> {as = []} = []≼
      ι₀-<> {as = x ∷ as} = take ι₀-<>

  preserve-◆-transl-Mod-3-2 : ∀{ϕ : ⊢ModeHom ◯ (▲ U)} {ψ : ⊢ModeHom (▲ U) (▲ V)}
              -> rev (transl-Mod3 (ϕ ◆' ψ))
                  ≼
                  rev (transl-Mod3 (ϕ ◆' `＠` U ⨾ `[]` ⨾ ψ))
  preserve-◆-transl-Mod-3-2 {ϕ = `[]` ⨾ id'} = ι₀-<>
  preserve-◆-transl-Mod-3-2 {ϕ = `[]` ⨾ `＠` W ⨾ ϕ} {ψ = ψ} = add-element (preserve-◆-transl-Mod-3-2 {ϕ = ϕ} {ψ = ψ})

  preserve-◆-transl-Mod-3 : ∀{ϕ : ⊢ModeHom ◯ (▲ U)} {ψ : ⊢ModeHom (▲ U) ◯}
    -> rev (transl-Mod3 (ϕ ◆' ψ))
        ≼'
        rev (transl-Mod3 (ϕ ◆' `＠` U ⨾ `[]` ⨾ ψ))
  preserve-◆-transl-Mod-3 {U = U} {ϕ = ϕ} {ψ} with split-ψ ψ
  ... | V , ψ' , refl-≡ = into-≼' {ϕ₀ = ϕ ◆' ψ'} {ϕ₁ = ϕ ◆' `＠` U ⨾ `[]` ⨾ ψ'} (preserve-◆-transl-Mod-3-2 {ϕ = ϕ} {ψ = ψ'})


-- Goal: rev (transl-Mod3 (idₗ₁ ◆' idᵣ₁)) ≼'
--       rev
--       (transl-Mod3
--        (idₗ₁ ◆'
--         BaseModeHom-PolySR.`＠` U ⨾ BaseModeHom-PolySR.`[]` ⨾ idᵣ₁))


-- Goal: (rev (transl-Mod3 μ) ++-List
--        Agora.Conventions.Prelude.Data.List.Base._.[ i ])
--       ≼' cons (postpend (rev' (transl-Mod3 η)) i)


-- Goal: rev (transl-Mod3 μ) ≼' rev' (transl-Mod3 η)


{-
  --------------------------------------------------------------------
  -- Interactions with transformations
  --------------------------------------------------------------------
  module _ {A : 𝒰 𝑖} where
    -- id-≼ : ∀{as : List A} -> as ≼ as
    -- id-≼ {as = []} = done
    -- id-≼ {as = x ∷ as} = take id-≼

    id-≼' : ∀{as : List A} -> as ≼' as
    id-≼' {as = []} = []
    id-≼' {as = a ∷ as} = a ∷ id-≼

    _◆-≼'_ : ∀{as bs cs : List A} -> as ≼' bs -> bs ≼' cs -> as ≼' cs
    [] ◆-≼' [] = []
    (a ∷ p) ◆-≼' (a ∷ q) = a ∷ (p ◆-≼ q)





  invisible-id : ∀ {μ ν : a ⟶ b}
              -> (α : Linear2Cell invis μ ν)
              -> μ ≡ ν
  invisible-id [] = refl-≡


  transToSublist-Single : ∀{μ ν : ⊢ModeHom ◯ ◯}
                 -> (α : SingleFace' vis μ ν)
                 -> classify-Single α ≤ ⦗ pureT ⦘
                 -> rev (transl-Mod3 μ) ≼' rev (transl-Mod3 ν)
  transToSublist-Single (singleFace (idₗ₁ ⌟[ send U ]⌞ idᵣ₁) refl-≡ refl-≡) αp = {!!}
  transToSublist-Single (singleFace (idₗ₁ ⌟[ recv U ]⌞ (_ ⨾ _)) top₁ bot) αp = ⊥-elim (≰-singleton (λ ()) αp)
  transToSublist-Single (singleFace (ϕ ⌟[ recv U ]⌞ id') top bot) αp = ⊥-elim (≰-singleton (λ ()) αp)

  transToSublist-Linear : ∀{μ ν : ⊢ModeHom ◯ ◯}
                 -> (α : Linear2Cell vis μ ν)
                 -> classify-Linear α ≤ ⦗ pureT ⦘
                 -> rev (transl-Mod3 μ) ≼' rev (transl-Mod3 ν)
  transToSublist-Linear [] αp = id-≼'
  transToSublist-Linear (α ∷ αs) αp =
    transToSublist-Single α (ι₀-∨ ⟡ αp)
    ◆-≼'
    transToSublist-Linear αs (ι₁-∨ {a = classify-Single α} ⟡ αp)

  transToSublist : ∀{μ ν : ⊢ModeHom ◯ ◯}
                 -> (α : ⊢ModeTrans μ ν)
                 -> classify α ≤ ⦗ pureT ⦘
                 -> rev (transl-Mod3 μ) ≼' rev (transl-Mod3 ν)
  transToSublist [ incl α-invis ∣ incl α-vis ] with
    invisible-id (linearize α-invis)
  ... | refl-≡ = transToSublist-Linear (linearize α-vis)


  transToSublist₁ : ∀{μ ν : ⊢ModeHom ◯ ◯}
                 -> (α : ⊢ModeTrans μ ν)
                 -> classify α ≤ ⦗ pureT ⦘
                 -> rev (transl-Mod3 μ) ≼' rev' (transl-Mod3 ν)
  transToSublist₁ {μ = μ} {ν = ν} α αp =
    transp-≡ (cong-≡ (λ ξ -> rev (transl-Mod3 μ) ≼' ξ) (rev≡rev' (transl-Mod3 ν))) (transToSublist α αp)

-}
