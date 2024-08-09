-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.MTT.Properties where

open import Agora.Conventions hiding (m ; n ; k ; _∣_)
open import Agora.Data.Product.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Category.Structured.Classified.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice

open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')

open import Data.Vec hiding ([_] ; map)

open import KamiCore.Language.MTT.Definition



module _ {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} where
  instance
    hasDecidableEquality:∑ : {{_ : hasDecidableEquality A}} -> {{_ : ∀{a : A} -> hasDecidableEquality (B a)}} -> hasDecidableEquality (∑ B)
    hasDecidableEquality:∑ = record { _≟_ = f }
      where
        f : (x y : ∑ B) -> isDecidable (x ≡ y)
        f (a0 , b0) (a1 , b1) with a0 ≟ a1
        ... | no x = no λ {refl-≡ → x refl-≡}
        ... | yes refl-≡ with b0 ≟ b1
        ... | no x = no λ {refl-≡ → x refl-≡}
        ... | yes refl-≡ = yes refl-≡



ofTypeSyntax : (A : 𝒰 𝑖) (a : A) -> A
ofTypeSyntax A a = a

syntax ofTypeSyntax A a = a ofType A

module 𝔐TT/Properties {𝑖 : 𝔏 ^ 6} (This : MTT 𝑖) where
  open 𝔐TT/Definition This
  open [𝔐TT/Definition::Type]
  private 𝓂 = ModeTheory This

  decide-≡-𝔐TT⊢Type : ∀{m} -> (A B : ⊢Type m) -> (¬ A ≡ B) +-𝒰 (A ≡ B)
  decide-≡-𝔐TT⊢Type ⟨ A ∣ μ₁ ⟩ ⟨ B ∣ μ₂ ⟩ with ((_ , _) , μ₁ ofType (∑ λ ((a , b) : ⟨ 𝓂 ⟩ ×-𝒰 ⟨ 𝓂 ⟩) -> a ⟶ b)) ≟ ((_ , _) , μ₂)
  ... | no x = no λ {refl-≡ → x refl-≡}
  ... | yes refl-≡ with decide-≡-𝔐TT⊢Type A B
  ... | no x = no λ {refl-≡ → x refl-≡}
  ... | yes refl-≡ = yes refl-≡
  decide-≡-𝔐TT⊢Type ⟨ A ∣ x ⟩ Unit = no λ ()
  decide-≡-𝔐TT⊢Type ⟨ A ∣ x ⟩ (Tr B) = no λ ()
  decide-≡-𝔐TT⊢Type ⟨ A ∣ x ⟩ (Either B B₁) = no λ ()
  decide-≡-𝔐TT⊢Type ⟨ A ∣ x ⟩ (Lst B) = no λ ()
  decide-≡-𝔐TT⊢Type ⟨ A ∣ x ⟩ (⟮ B ∣ x₁ ⟯⇒ B₁) = no λ ()
  decide-≡-𝔐TT⊢Type Unit ⟨ B ∣ x ⟩ = no λ ()
  decide-≡-𝔐TT⊢Type Unit Unit = yes refl-≡
  decide-≡-𝔐TT⊢Type Unit (Tr B) = no λ ()
  decide-≡-𝔐TT⊢Type Unit (Either B B₁) = no λ ()
  decide-≡-𝔐TT⊢Type Unit (Lst B) = no λ ()
  decide-≡-𝔐TT⊢Type Unit (⟮ B ∣ x ⟯⇒ B₁) = no λ ()
  decide-≡-𝔐TT⊢Type (Tr A) ⟨ B ∣ x ⟩ = no λ ()
  decide-≡-𝔐TT⊢Type (Tr A) Unit = no λ ()
  decide-≡-𝔐TT⊢Type (Tr A) (Tr B) with decide-≡-𝔐TT⊢Type A B
  ... | no x = no λ {refl-≡ → x refl-≡}
  ... | yes refl-≡ = yes refl-≡
  decide-≡-𝔐TT⊢Type (Tr A) (Either B B₁) = no λ ()
  decide-≡-𝔐TT⊢Type (Tr A) (Lst B) = no λ ()
  decide-≡-𝔐TT⊢Type (Tr A) (⟮ B ∣ x ⟯⇒ B₁) = no λ ()
  decide-≡-𝔐TT⊢Type (Either A A₁) ⟨ B ∣ x ⟩ = no λ ()
  decide-≡-𝔐TT⊢Type (Either A A₁) Unit = no λ ()
  decide-≡-𝔐TT⊢Type (Either A A₁) (Tr B) = no λ ()
  decide-≡-𝔐TT⊢Type (Either A A₁) (Either B B₁) with decide-≡-𝔐TT⊢Type A B
  ... | no x = no λ {refl-≡ → x refl-≡}
  ... | yes refl-≡ with decide-≡-𝔐TT⊢Type A₁ B₁
  ... | no x = no λ {refl-≡ → x refl-≡}
  ... | yes refl-≡ = yes refl-≡
  decide-≡-𝔐TT⊢Type (Either A A₁) (Lst B) = no λ ()
  decide-≡-𝔐TT⊢Type (Either A A₁) (⟮ B ∣ x ⟯⇒ B₁) = no λ ()
  decide-≡-𝔐TT⊢Type (Lst A) ⟨ B ∣ x ⟩ = no λ ()
  decide-≡-𝔐TT⊢Type (Lst A) Unit = no λ ()
  decide-≡-𝔐TT⊢Type (Lst A) (Tr B) = no λ ()
  decide-≡-𝔐TT⊢Type (Lst A) (Either B B₁) = no λ ()
  decide-≡-𝔐TT⊢Type (Lst A) (Lst B) with decide-≡-𝔐TT⊢Type A B
  ... | no x = no λ {refl-≡ → x refl-≡}
  ... | yes refl-≡ = yes refl-≡
  decide-≡-𝔐TT⊢Type (Lst A) (⟮ B ∣ x ⟯⇒ B₁) = no λ ()
  decide-≡-𝔐TT⊢Type (⟮ A ∣ x ⟯⇒ A₁) ⟨ B ∣ x₁ ⟩ = no λ ()
  decide-≡-𝔐TT⊢Type (⟮ A ∣ x ⟯⇒ A₁) Unit = no λ ()
  decide-≡-𝔐TT⊢Type (⟮ A ∣ x ⟯⇒ A₁) (Tr B) = no λ ()
  decide-≡-𝔐TT⊢Type (⟮ A ∣ x ⟯⇒ A₁) (Either B B₁) = no λ ()
  decide-≡-𝔐TT⊢Type (⟮ A ∣ x ⟯⇒ A₁) (Lst B) = no λ ()
  decide-≡-𝔐TT⊢Type (⟮ A ∣ μ ⟯⇒ A₁) (⟮ B ∣ μ₁ ⟯⇒ B₁) with ((_ , _) , μ ofType (∑ λ ((a , b) : ⟨ 𝓂 ⟩ ×-𝒰 ⟨ 𝓂 ⟩) -> a ⟶ b)) ≟ ((_ , _) , μ₁)
  ... | no x = no λ {refl-≡ → x refl-≡}
  ... | yes refl-≡ with decide-≡-𝔐TT⊢Type A B
  ... | no x = no λ {refl-≡ → x refl-≡}
  ... | yes refl-≡ with decide-≡-𝔐TT⊢Type A₁ B₁
  ... | no x = no λ {refl-≡ → x refl-≡}
  ... | yes refl-≡ = yes refl-≡


  instance
    hasDecidableEquality:𝔐TT⊢Type : ∀{m} -> hasDecidableEquality (⊢Type m)
    hasDecidableEquality:𝔐TT⊢Type = record { _≟_ = decide-≡-𝔐TT⊢Type }



  -----------------------------------------------
  -- Show

  module _ {{_ : ∀{m n : ⟨ 𝓂 ⟩} -> IShow (m ⟶ n)}} where
    show-Type : ∀{m} -> ⊢Type m -> String
    show-Type ⟨ X ∣ x ⟩ = "⟨ " <> show-Type X <> " ∣ " <> show x <> " ⟩"
    show-Type Unit = "Unit"
    show-Type (Tr X) = "(Tr " <> show-Type X <> ")"
    show-Type (Either X Y) = "(Either " <> show-Type X <> " " <> show-Type Y <> ")" 
    show-Type (Lst X) = "(List " <> show-Type X <> ")"
    show-Type (⟮ X ∣ μ ⟯⇒ Y) = "⟨ " <> show-Type X <> " ∣ " <> show μ <> " ⟩⇒ " <> show-Type Y

    instance
      IShow:Type : ∀{m} -> IShow (⊢Type m)
      IShow:Type = record { show = show-Type }


    withTypeEquality : ∀{m} {X : 𝒰 𝑖}
                    (A B : ⊢Type m)
                    (f : A ≡ B -> (Text +-𝒰 X))
                    ->
                    Text +-𝒰 X
    withTypeEquality A B f with A ≟ B
    ... | no x = left $ "expected types to be equal (" <> show A <> " == " <> show B <> ")"
    ... | yes x = f x



  module _ {{_ : IShow ⟨ 𝓂 ⟩}} where
    withModeEquality : {X : 𝒰 𝑖}
                    (A B : ⟨ 𝓂 ⟩)
                    (f : A ≡ B -> (Text +-𝒰 X))
                    ->
                    Text +-𝒰 X
    withModeEquality A B f with A ≟ B
    ... | no x = left $ "expected modes to be equal (" <> show A <> " == " <> show B <> ")"
    ... | yes x = f x
