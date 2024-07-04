
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorProc.Properties3 where

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
open import KamiTheory.Data.UniqueSortedList.NonEmpty
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding (Mode)
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category

open import KamiCore.Language.ChorMTT.Definition
open import KamiCore.Language.ChorMTT.Properties
open import KamiCore.Language.ChorProc.Definition
open import KamiCore.Language.ChorProc.Properties
open import KamiCore.Language.ChorProc.Properties2



module Chor𝔓roc/Properties3 (This : Chor𝔓roc 𝑗) where
  open Chor𝔓roc/Definition This
  open [Chor𝔓roc/Definition::Param]
  open [Chor𝔓roc/Definition::Type]
  open [Chor𝔓roc/Definition::Ctx]
  open [Chor𝔓roc/Definition::Term]
  open Chor𝔓roc/Properties This
  open Chor𝔓roc/Properties2 This

  open Chor𝔐TT/Definition Super
  open [Chor𝔐TT/Definition::Type] renaming (⊢Type to Chor𝔐TT⊢Type)
  open [Chor𝔐TT/Definition::Ctx] renaming (⊢Ctx to Chor𝔐TT⊢Ctx)
  open [Chor𝔐TT/Definition::Term] renaming (_⊢_ to _Chor𝔐TT⊢_)
  open Chor𝔐TT/Properties Super

  lift-π-single : ∀{X A p ps q} -> π X ∣ p , ps ↦ A Type -> π ◻ X ＠ q ∣ q , (p ∷ ps) ↦ A Type
  lift-π-single X = proj-＠ refl-≤ (proj-◻ X)

  lift-π-impl : ∀{X A p ps r} -> π X ∣ r , [] ↦ A Type -> π F2-Type (p ∷ ps) X ∣ p , ps <> (r ∷ []) ↦ A Type
  lift-π-impl {ps = []} Xp = proj-＠ refl-≤ (proj-◻ Xp)
  lift-π-impl {ps = x ∷ ps} Xp = lift-π-single (lift-π-impl Xp)

  lift-π : ∀{X A ps qs r} -> ps ≼' qs -> π X ∣ r , [] ↦ A Type -> π F2-Type ps X ∣ fst (postpend qs r) , drop 1 (ps <> (r ∷ [])) ↦ A Type
  lift-π {qs = []} [] Xp = Xp
  lift-π {qs = x ∷ qs} (_∷_ .x x₁) Xp = lift-π-impl Xp

  lift-π-direct : ∀{X B ps r} -> (π X ∣ r , [] ↦ B Type) -> π F2-Type ps X ∣ fst (postpend ps r) , snd (postpend ps r) ↦ B Type
  lift-π-direct {X} {B} {ps} {r} p =
    let P = lift-π id-≼' p
    in transp-≡ (cong-≡ (λ ξ -> π F2-Type ps X ∣ fst (postpend ps r) , ξ ↦ B Type) (drop-post ps)) P


  mkVar : ∀{Δ X A r ps qs} -> ps ≼' qs -> π X ∣ r , [] ↦ A Type -> Δ , F2-Type ps X ⊢Var A GlobalFiber[ cons (postpend qs r) ]
  mkVar {r = r} {ps} {qs} [] Xp = zero done Xp -- (lift-π {ps = ps} {qs = qs} {r = r} P Xp)
  mkVar {r = r} {ps} {qs} (_∷_ a {bs = bs} Ps) Xp = zero (add-element {zs = (r ∷ [])} Ps ◆-≼≡ drop-post (a ∷ bs)) (lift-π {ps = ps} {qs = qs} {r = r} (a ∷ Ps) Xp)

  mkVar-▲ : ∀{Δ A B U V r ps qs} -> (ps <> (U ∷ [])) ≼' (qs <> (V ∷ [])) -> π A ＠ V ∣ r , [] ↦ B Type -> Δ , F2-Type ps (A ＠ U) ⊢Var B GlobalFiber[ cons (postpend qs r) ]
  mkVar-▲ {ps = []} {qs = []} (_ ∷ x) P = zero done P
  mkVar-▲ {ps = []} {qs = x ∷ qs} (.x ∷ x₁) P with P
  ... | proj-＠ x₂ done = zero []≼ ( (proj-＠ refl-≤ done))
  ... | proj-＠-≠ x₂ = none
  mkVar-▲ {U = U} {V} {r = r} {ps = x ∷ ps} {qs = .x ∷ qs} (.x ∷ x₁) P with split-≼ ps qs x₁
  ... | no (Q , refl-≡) = zero (add-element-post Q) ( (proj-＠ refl-≤ (proj-◻ (lift-π-direct {ps = ps} P))))
  ... | yes Q with P
  ... | proj-＠ x₂ done = zero ((cons-post ps _) ◆-≡≼ ((Q ◆-≼ ι₀-<> {bs = (r ∷ [])}) ◆-≼≡ sym-≡ (cons-post qs _))) ( (proj-＠ refl-≤ (proj-◻ (lift-π-direct {ps = ps} (proj-＠ refl-≤ done)))))
  ... | proj-＠-≠ x₂ = none
  mkVar-▲ {U = U} {.x} {r = r} {ps = x ∷ []} {qs = []} (.x ∷ ()) P
  mkVar-▲ {U = U} {.x} {r = r} {ps = x ∷ x₂ ∷ ps} {qs = []} (.x ∷ ()) P

  updateVar : ∀{X A B Δ p ps} -> π X ∣ p , [] ↦ B Type ->  Δ , X ⊢Var A GlobalFiber[ p ∷ ps ] -> Δ , B ＠ p ⊢Var A GlobalFiber[ p ∷ ps ]
  updateVar P (zero x x₁) = zero x (lem-12 P x₁)
  updateVar P (suc v) = suc v
  updateVar P (none) = none


