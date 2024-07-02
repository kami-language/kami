
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

--
-- Purpose: Function types don't have modalites,
-- mod introduces always single modalities
--

module KamiCore.Language.MinMTT.Translation where

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


F₁ : Min𝔐TT 𝑖 -> 𝔐TT _
F₁ This = Min𝔐TT/Definition.[Min𝔐TT/Definition::Private].Super This

module _ {𝑖} where
  macro 𝔉₁ = #structureOn (F₁ {𝑖 = 𝑖})

module _ (This : Min𝔐TT 𝑖) where
  open Min𝔐TT/Definition This
  open [Min𝔐TT/Definition::Private]
  open [Min𝔐TT/Definition::Type]
  open [Min𝔐TT/Definition::Ctx]
  open [Min𝔐TT/Definition::Term]

  open 𝔐TT/Definition Super
  open [𝔐TT/Definition::Type] renaming (⊢Type to 𝔐TT⊢Type)
  open [𝔐TT/Definition::Ctx] renaming (⊢Ctx to 𝔐TT⊢Ctx)
  open [𝔐TT/Definition::Term] renaming (_⊢_ to _𝔐TT⊢_)
  open Variables/Mode

  par-𝔉₁ : Param Super -> Param This
  par-𝔉₁ x = x



  --------------------------------------------------------------------
  -- Types
  Mod-Type : ∀{a b} -> Path _⟶ₛ_ a b -> ⊢Type a -> ⊢Type b
  Mod-Type id' X = X
  Mod-Type (μ ⨾ μs) X = Mod-Type μs ⟨ X ∣ μ ⟩

  ⟪𝔉₁∣_Type⟫ : ∀{a} -> 𝔐TT⊢Type a -> ⊢Type a
  ⟪𝔉₁∣ ⟨ X ∣ μ ⟩ Type⟫ = Mod-Type (split This μ) ⟪𝔉₁∣ X Type⟫
  ⟪𝔉₁∣ Unit Type⟫ = Unit
  ⟪𝔉₁∣ Tr X Type⟫ = Tr ⟪𝔉₁∣ X Type⟫
  ⟪𝔉₁∣ Either X Y Type⟫ = Either ⟪𝔉₁∣ X Type⟫ ⟪𝔉₁∣ Y Type⟫
  ⟪𝔉₁∣ Lst X Type⟫ = Lst ⟪𝔉₁∣ X Type⟫
  ⟪𝔉₁∣ ⟮ X ∣ μ ⟯⇒ Y Type⟫ =  Mod-Type (split This μ) ⟪𝔉₁∣ X Type⟫ ⇒ ⟪𝔉₁∣ Y Type⟫

  -- End Types
  --------------------------------------------------------------------


  --------------------------------------------------------------------
  -- Contexts

  Mod-Ctx : (μs : Path _⟶ₛ_ m n) -> (Γ : ⊢Ctx {k} n) -> ⊢Ctx {k} m
  Mod-Ctx id' Γ = Γ
  Mod-Ctx (μ ⨾ μs) Γ = Mod-Ctx μs Γ ∙! fst μ

  ⟪𝔉₁∣_Ctx⟫ : {a : Param Super} -> Ctx a of Super -> Ctx a of This
  ⟪𝔉₁∣ ε Ctx⟫ = ε
  ⟪𝔉₁∣ Γ ∙⟮ X ∣ μ ⟯ Ctx⟫ = ⟪𝔉₁∣ Γ Ctx⟫ ∙⟮ ⟪𝔉₁∣ X Type⟫ ∣ μ ⟯
  ⟪𝔉₁∣ Γ ∙! μ Ctx⟫ = Mod-Ctx (split This μ) ⟪𝔉₁∣ Γ Ctx⟫

  -- End Contexts
  --------------------------------------------------------------------


  --------------------------------------------------------------------
  -- Terms
  Mod-Term : (μs : Path _⟶ₛ_ m n) -> {X : ⊢Type m}
             -> (t : Mod-Ctx μs Γ ⊢ X)
             -> Γ ⊢ Mod-Type μs X
  Mod-Term id' t = t
  Mod-Term (μ ⨾ μs) t = Mod-Term μs (mod μ t)

  -- Split-Ctx : Γ ∙! μ

  ⟪𝔉₁∣_Term⟫ : {a : Param Super} -> {Γ : Ctx a of Super} -> {X : Type a of Super}
               -> Γ ⊢ X at a of Super
               -> ⟪𝔉₁∣ Γ Ctx⟫ ⊢ ⟪𝔉₁∣ X Type⟫ at a of This
  ⟪𝔉₁∣ var x α x₁ Term⟫ = {!!}
  ⟪𝔉₁∣ mod μ t Term⟫ = {!Mod-Term (split This μ) t!}
  ⟪𝔉₁∣ letmod ν t t₁ Term⟫ = {!!}
  ⟪𝔉₁∣ trans α x t Term⟫ = {!!}
  ⟪𝔉₁∣ pure t Term⟫ = {!!}
  ⟪𝔉₁∣ seq t t₁ Term⟫ = {!!}
  ⟪𝔉₁∣ lam t Term⟫ = {!!}
  ⟪𝔉₁∣ app t t₁ Term⟫ = {!!}
  ⟪𝔉₁∣ tt Term⟫ = {!!}
  ⟪𝔉₁∣ left t Term⟫ = {!!}
  ⟪𝔉₁∣ right t Term⟫ = {!!}
  ⟪𝔉₁∣ either t t₁ t₂ Term⟫ = {!!}
  ⟪𝔉₁∣ [] Term⟫ = {!!}
  ⟪𝔉₁∣ t ∷ t₁ Term⟫ = {!!}
  ⟪𝔉₁∣ rec-Lst t t₁ t₂ Term⟫ = {!!}

  -- End Terms
  --------------------------------------------------------------------


  run-𝔉₁ : {a : Param Super}
           -> (pa : SubParam Super a)
           -> Hom-STT (Super at a) (This at a)
  run-𝔉₁ pa = record
    { ⟪_∣_Ctx⟫ = ⟪𝔉₁∣_Ctx⟫
    ; ⟪_∣_Type⟫ = ⟪𝔉₁∣_Type⟫
    ; ⟪_∣_Term⟫ = ⟪𝔉₁∣_Term⟫
    }

{-


instance
  isReduction:F₁ : isParamSTTHom (Min𝔐TT 𝑖) (𝔐TT _) F₁
  isReduction:F₁ = record
    { param = par-𝔉₁
    ; runAt = run-𝔉₁
    }


-}

