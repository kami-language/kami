
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.F.Translation8 where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category
open import Data.List using (drop)


open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')

open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Basics hiding (_⋆_)





module Translation (n : ℕ) where
-- (P : Preorder 𝑖) {{_ : hasDecidableEquality ⟨ P ⟩}} {{_ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)}} where

  P : Preorder _
  P = 𝒫ᶠⁱⁿ (𝔽 n)

  postulate instance
    hasDecidableEquality:P : hasDecidableEquality ⟨ P ⟩
    -- hasDecidableEquality:P = {!!}

  postulate instance
    isProp:≤ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)
    -- isProp:≤ = {!!}

  -- Getting the mode system
  import KamiTheory.Main.Generic.ModeSystem.2Graph.Example2 as 2GraphExample
  -- import KamiTheory.Main.Generic.ModeSystem.2Cell.Example as 2CellExample
  import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition as 2CellDefinition
  import KamiTheory.Main.Generic.ModeSystem.2Cell.Rewriting as 2CellRewriting
  import KamiTheory.Main.Generic.ModeSystem.2Cell.Linear as 2CellLinear
  open 2CellDefinition.2CellDefinition hiding (id)
  open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Example2
  open SendNarrow-ModeSystem P {{it}} {{it}}
  open 2GraphExample.SendNarrow-2Graph P
  open 2CellLinear.2CellLinear SN
  open 2CellRewriting.2CellRewriting SN
  -- open 2CellExample.SendNarrow-2Cells P {{it}} {{it}}


  -- Instantiating MTT with the 2category generated from the modesystem
  open import KamiCore.Typed.Variant.F.Definition3

  instance
    Param : MTTꟳ _
    Param = record
      { 𝓂 = Mode SN-ModeSystem
      ; isCategory:𝓂 = isCategory:byModeSystem SN-ModeSystem
      ; is2Category:𝓂 = is2Category:byModeSystem SN-ModeSystem
      }


  open Definition-MTTꟳ {{Param}}
    renaming (ModeHom to ModeHom' ; _⊢_ to _⊢'_)

  instance
    isCategoryData:ModeHom : isCategoryData (Mode SN-ModeSystem) ModeHom'
    isCategoryData:ModeHom = HomData {{isCategory:𝓂 {{Param}}}}

  instance
    isCategory:ModeHom : isCategory (Mode SN-ModeSystem)
    isCategory:ModeHom = record { Hom = ModeHom' }

  instance
    is2Category:ModeHom : is2Category ′(Mode SN-ModeSystem)′
    is2Category:ModeHom = is2Category:𝓂 {{Param}}


  -- Instantiating the target language with the preorder
  open import KamiCore.Typed.Variant.F.Model8

  ρ : isProcessSet _
  ρ = record { Proc = 𝔽 n }

  open IR {{ρ}}
    renaming (Ctx to Ctx' ; Mode to Mode')


  private variable
    a a₀ b c d : Mode SN-ModeSystem
    μ ν η ω : ModeHom' a b

  isSuffix : (x : Edge (of SN-ModeSystem .graph) a b) -> ModeHom' c b -> 𝒰 _
  isSuffix x μ = ∑ λ ν -> ν ◆' (x ⨾ id') ≡ μ

  -- split-Path-eq : ∀{}

  skipSuffixPrefix : ∀{y} -> {x : Edge (of SN-ModeSystem .graph) a₀ b} {μ : ModeHom' a b} {ω : ModeHom' c d} -> isSuffix x (ω ◆ (y ⨾ μ)) -> isSuffix x (y ⨾ μ)
  skipSuffixPrefix {ω = id'} (η , P) = η , P
  skipSuffixPrefix {ω = x ⨾ ω} (id' , P) = {!!} , {!!}
  skipSuffixPrefix {ω = x ⨾ ω} (x₁ ⨾ η , P) = {!!} , {!!}

  data isBroadcast : ∀{a b} -> {μ ν : ModeHom' a b} -> μ ⟹ ν -> 𝒰₀ where
  -- data isBroadcast {a b} : {μ ν : ModeHom' a b} -> μ ⟹ ν -> 𝒰₀ where
    -- br : ∀{U ϕ₀ ϕ₁} -> isBroadcast [ (incl []) ∣ incl (incl (ϕ₀ ⌟[ recv U ]⌞ (ϕ₁ ⌟)) ∷ []) ]
    -- br : ∀{U} -> isBroadcast [ (incl []) ∣ incl (incl (id' ⌟[ recv U ]⌞ (id' ⌟)) ∷ []) ]

  derive-subset-Single : ∀{U V} -> {μ ν : ModeHom' a ▲} -> SingleFace' vis (μ ◆' `＠` U ⨾ id') (ν ◆' `＠` V ⨾ id') -> U ≡ V
  derive-subset-Single (singleFace (idₗ₁ ⌟[ send U ]⌞ (`＠` U₁ ⨾ idᵣ₁)) top₁ bot) = {!!}

  derive-subset : ∀{U V} -> {μ ν : ModeHom' ◯ b} -> Linear2Cell vis (`＠` U ⨾ μ) (`＠` V ⨾ ν) -> U ≡ V
  derive-subset = {!!}
  -- derive-subset [] = {!!}
  -- derive-subset (_∷_ {η = id'} (singleFace (id' ⌟[ send U ]⌞ idᵣ) top ()) x₁)
  -- derive-subset (_∷_ {η = id'} (singleFace ((x ⨾ idₗ₁) ⌟[ send U ]⌞ idᵣ) top ()) x₁)
  -- derive-subset (_∷_ {η = id'} (singleFace ((x ⨾ idₗ₁) ⌟[ recv U ]⌞ idᵣ) top ()) x₁)
  -- derive-subset (2CellLinear.2CellLinear._∷_ {η = 2GraphExample.SendNarrow-2Graph.`＠` U ⨾ .(2GraphExample.SendNarrow-2Graph.`[]` ⨾ id' ◆' `＠` _ ⨾ idᵣ₁)} (2CellLinear.2CellLinear.singleFace (id' 2CellRewriting.2CellRewriting.⌟[ 2GraphExample.SendNarrow-2Graph.send .U ]⌞ (.(`＠` _) ⨾ idᵣ₁)) refl-≡ refl-≡) x₁) = {!!}
  -- derive-subset (2CellLinear.2CellLinear._∷_ {η = 2GraphExample.SendNarrow-2Graph.`＠` U ⨾ η} (2CellLinear.2CellLinear.singleFace ((x ⨾ idₗ₁) 2CellRewriting.2CellRewriting.⌟[ 2GraphExample.SendNarrow-2Graph.send U₁ ]⌞ idᵣ₁) top₁ bot) x₁) = {!!}
  -- derive-subset (2CellLinear.2CellLinear._∷_ {η = 2GraphExample.SendNarrow-2Graph.`＠` U ⨾ η} (2CellLinear.2CellLinear.singleFace (idₗ₁ 2CellRewriting.2CellRewriting.⌟[ 2GraphExample.SendNarrow-2Graph.recv U₁ ]⌞ idᵣ₁) top₁ bot) x₁) = {!!}





  --------------------------------------------------
  -- Translating MTT terms into a form where the
  -- contexts only have single restrictions form.
  data isCtx₁ : Ctx a -> 𝒰₀ where
    ε : isCtx₁ {a = a} ε
    stepVar : {Γ : Ctx b} -> isCtx₁ Γ -> {A : ⊢Type a} -> {μ : a ⟶ b} -> isCtx₁ (Γ ∙⟮ A ∣ μ ⟯)
    stepRes : {Γ : Ctx b} -> isCtx₁ Γ -> {μ : BaseModeHom-SN a b} -> isCtx₁ (Γ ∙! (μ ⨾ id))


  addRes : (μ : a ⟶ b) -> ∑ isCtx₁ {a = b} -> ∑ isCtx₁ {a = a}
  addRes id' Γ = Γ
  addRes (x ⨾ μ) Γ =
    let Γ' , Γ'p = addRes μ Γ
    in Γ' ∙! (x ⨾ id') , stepRes Γ'p

  toCtx₁ : Ctx a -> ∑ isCtx₁ {a = a}
  toCtx₁ ε = ε , ε
  toCtx₁ (Γ ∙⟮ x ∣ x₁ ⟯) =
    let Γ , Γp = toCtx₁ Γ
    in Γ ∙⟮ x ∣ x₁ ⟯ , stepVar Γp
  toCtx₁ (Γ ∙! μ) = addRes μ (toCtx₁ Γ)

  -- to₁-Var : ∀{Γ : Ctx a} {A : ⊢Type a} -> Γ ⊢ A -> fst (toCtx₁ Γ) ⊢ 

  --------------------------------------------------
  -- Translating MTT terms into a form where the
  -- contexts only have {＠j}{◻} form.



  --------------------------------------------------
  -- An MTT version which has only single 
  module _ where
    private variable
      Γ : Ctx a
      A B : ⊢Type a

    data _⊢_ : Ctx a -> ⊢Type a -> 𝒰₀ where
      var : ∀{μ : _ ⟶ b} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> (α : μ ⟹ η) -> Γ ⊢ A
      tt : Γ ⊢ Unit

      -- modalities
      mod : ∀ μ -> Γ ∙! (μ ⨾ id') ⊢ A -> Γ ⊢ ⟨ A ∣ μ ⨾ id' ⟩
      letmod : ∀(μ : BaseModeHom-SN a b) -> (ν : b ⟶ c)
            -> Γ ∙! ν ⊢ ⟨ A ∣ μ ⨾ id' ⟩
            -> Γ ∙⟮ A ∣ μ ⨾ ν ⟯ ⊢ B
            -> Γ ⊢ B

      letmod' : ∀(μ : BaseModeHom-SN a b)
            -> Γ ⊢ ⟨ A ∣ μ ⨾ id' ⟩
            -> Γ ∙⟮ A ∣ μ ⨾ id' ⟯ ⊢ B
            -> Γ ⊢ B

      -- explicit transformations
      trans : ∀ {μ ν : a ⟶ b} -> (α : μ ⟹ ν) -> isBroadcast α -> Γ ⊢ ⟨ A ∣ μ ⟩ -> Γ ⊢ Tr ⟨ A ∣ ν ⟩

      -- transformations monad
      pure : Γ ⊢ A -> Γ ⊢ Tr A
      seq : ∀{A : ⊢Type a} -> Γ ⊢ Tr A -> Γ ∙⟮ A ∣ id ⟯ ⊢ B -> Γ ⊢ Tr B

      -- functions
      lam : Γ ∙⟮ A ∣ id' ⟯ ⊢ B -> Γ ⊢ ⟮ A ∣ id' ⟯⇒ B

      -- app : Γ ⊢ ⟮ A ∣ μ ⟯⇒ B -> Γ ∙! μ ⊢ A -> Γ ⊢ B
      app : Γ ⊢ ⟮ A ∣ id' ⟯⇒ B -> Γ ⊢ A -> Γ ⊢ B

    -- shift-＠ : ∀{i} -> {A : ⊢Type a} -> (Γ ∙! (`＠` i ⨾ id')) ∙⟮ A ∣ μ ⟯ ⊢ B -> (Γ ∙⟮ A ∣ μ ◆ (`＠` i ⨾ id') ⟯ ∙! (`＠` i ⨾ id')) ⊢ B
    -- shift-＠ = {!!}

    shift-＠ : ∀{i} -> {A : ⊢Type ▲} -> (Γ ∙! (`＠` i ⨾ id')) ∙⟮ A ∣ id' ⟯ ⊢ B -> (Γ ∙⟮ ⟨ A ∣ (`＠` i ⨾ id') ⟩ ∣ id' ⟯ ∙! (`＠` i ⨾ id')) ⊢ B
    shift-＠ = {!!}

    id-annotate : ∀{Γ : Ctx a} -> Γ ∙⟮ A ∣ μ ⟯ ⊢ B -> Γ ∙⟮ ⟨ A ∣ μ ⟩ ∣ id' ⟯ ⊢ B
    id-annotate = {!!}

    split-path : ∀{μs : ModeHom' b c} -> ∀{μ} -> ∀{A : ⊢Type a} -> Γ ∙! (μ ⨾ μs) ⊢ A -> (Γ ∙! μs) ∙! (μ ⨾ id') ⊢ A
    split-path = {!!}

    add-id : Γ ⊢ A -> Γ ∙! id' ⊢ A
    add-id = {!!}

    remove-id : Γ ∙! id' ⊢ A -> Γ ⊢ A
    remove-id = {!!}

    -- _↶_ : Ctx b -> (ModeHom' a b) -> Ctx a
    -- _↶_ Γ id' = Γ
    -- _↶_ Γ (x ⨾ μ) = _↶_ Γ μ ∙! (x ⨾ id')

    _↶_ : ∀{ω : ModeHom' b c} -> CtxExt ω -> (μ : ModeHom' a b) -> CtxExt (μ ◆ ω)
    _↶_ Γ id' = Γ
    _↶_ Γ (x ⨾ μ) = _↶_ Γ μ ∙! (x ⨾ id')


    infixl 30 _↶_

    splits-path : ∀{Γ : CtxExt ω} -> ∀{μs : ModeHom' a b} -> ∀{A : ⊢Type a} -> (ε ⋆ Γ) ∙! μs ⊢ A -> ε ⋆ Γ ↶ μs ⊢ A
    splits-path {μs = id'} t = remove-id t
    splits-path {μs = x ⨾ μs} t = {!splits-path !}

    splits2-path : ∀{Γ : CtxExt ω} -> ∀{μs : ModeHom' a b} -> ∀{A : ⊢Type a} -> (ε ⋆ Γ) ∙! μs ⊢ A -> ε ⋆ Γ ↶ μs ⊢ A
    splits2-path = {!!}






  data isCtx₂ : Ctx a -> 𝒰₀ where
    ε : isCtx₂ {a = a} ε
    stepVar : {Γ : Ctx ◯} -> isCtx₂ Γ -> {A : ⊢Type a} -> {μ : a ⟶ ◯} -> isCtx₂ (Γ ∙⟮ A ∣ μ ⟯)
    -- stepRes : {Γ : Ctx a} -> isCtx₂ Γ -> isCtx₂ (Γ ∙! μ)
    stepRes : ∀(x : Edge (of SN-ModeSystem .graph) b a) -> {Γ : Ctx a} -> isCtx₂ Γ -> isCtx₂ (Γ ∙! (x ⨾ id))

    -- stepRes-◻ : {Γ : Ctx ▲} -> isCtx₂ Γ -> isCtx₂ (Γ ∙! (`[]` ⨾ id))
    -- stepRes-＠ : {Γ : Ctx ◯} -> ∀{p} -> isCtx₂ Γ -> isCtx₂ (Γ ∙! (`＠` p ⨾ id))



  isGood:splits : {ω : ModeHom' b c} {Γ : CtxExt ω} {μs : ModeHom' a b} -> isCtx₂ (ε ⋆ Γ) -> isCtx₂ (ε ⋆ Γ ↶ μs)
  isGood:splits = {!!}



  ⦋_⦌-Mode : Mode SN-ModeSystem -> Mode'
  ⦋ ▲ ⦌-Mode = ▲
  ⦋ ◯ ⦌-Mode = ◯

  F-Type : (ModeHom' a b) -> Type ⦋ a ⦌-Mode -> Type ⦋ b ⦌-Mode
  F-Type id' x = x
  F-Type (`＠` U ⨾ μ) x = F-Type μ (x ＠ U)
  F-Type (`[]` ⨾ μ) x = F-Type μ (◻ x)

  F-Type-Proof : (μ : ModeHom' a b) -> ∀{X : Type ⦋ a ⦌-Mode} -> isClosed X -> isClosed (F-Type μ X)
  F-Type-Proof μ Xp = {!!}

  F-Type-map : ∀{X} {μ : ModeHom' a b} {ν : ModeHom' b c} -> F-Type (μ ◆ ν) X ≡ F-Type ν (F-Type μ X)
  F-Type-map {μ = id'} = refl-≡
  F-Type-map {μ = `＠` U ⨾ μ} = F-Type-map {μ = μ}
  F-Type-map {μ = `[]` ⨾ μ} = F-Type-map {μ = μ}


  ⦋_⦌-Type : ⊢Type a -> Type ⦋ a ⦌-Mode
  ⦋ ⟨ X ∣ μ ⟩ ⦌-Type = F-Type μ ⦋ X ⦌-Type
  ⦋ Unit ⦌-Type = Unit
  ⦋ Tr X ⦌-Type = Tr ⦋ X ⦌-Type
  ⦋ ⟮ X ∣ μ ⟯⇒ Y ⦌-Type = F-Type μ ⦋ X ⦌-Type ⇒ ⦋ Y ⦌-Type
  ⦋ Either x x₁ ⦌-Type = {!!}
  ⦋ Lst x ⦌-Type = {!!}


  TargetCtx : Mode SN-ModeSystem -> 𝒰 _
  TargetCtx ▲ = Ctx' × ⟨ P ⟩
  TargetCtx ◯ = Ctx'

  addRestr : (μ : ModeHom' a b) -> TargetCtx b -> TargetCtx a
  addRestr id' Γ = Γ
  addRestr (`＠` U ⨾ μ) Γ = addRestr μ Γ , U
  addRestr (`[]` ⨾ μ) Γ = let Γ' , U = addRestr μ Γ in Γ' ,[ U ]

  forget : TargetCtx a -> Ctx'
  forget {a = ◯} Γ = Γ
  forget {a = ▲} Γ = fst Γ

  addRestr' : (μ : ModeHom' a b) -> TargetCtx b -> Ctx'
  addRestr' μ Γ = forget (addRestr μ Γ)

  transl-Ctx : ∀{μ : ModeHom' a ◯} -> (Γ : CtxExt μ) -> isCtx₂ (ε ⋆ Γ) -> TargetCtx a
  transl-Ctx ε Γp = ε
  transl-Ctx (Γ ∙⟮ x ∣ μ ⟯) (stepVar Γp) = transl-Ctx Γ Γp , F-Type μ ⦋ x ⦌-Type
  transl-Ctx (_∙!_ Γ μ) (stepRes _ Γp) = addRestr μ (transl-Ctx Γ Γp)

  transl-Ctx' : ∀{μ : ModeHom' a ◯} -> (Γ : CtxExt μ) -> isCtx₂ (ε ⋆ Γ) -> Ctx'
  transl-Ctx' Γ Γp = forget (transl-Ctx Γ Γp)

  transl₂-Ctx : ∀{μ : ModeHom' a b} -> (Γ : CtxExt μ) -> isCtx₂ (ε ⋆ Γ) -> TargetCtx a
  transl₂-Ctx {2GraphExample.SendNarrow-2Graph.▲} Definition-MTTꟳ.ε Γp = {!!}
  transl₂-Ctx {2GraphExample.SendNarrow-2Graph.◯} Definition-MTTꟳ.ε Γp = {!!}
  transl₂-Ctx (Γ ∙⟮ x ∣ μ ⟯) (stepVar Γp) = transl₂-Ctx Γ Γp , F-Type μ ⦋ x ⦌-Type
  transl₂-Ctx (_∙!_ Γ μ) (stepRes _ Γp) = addRestr μ (transl₂-Ctx Γ Γp)



  lemma:transl,restr : ∀{ω : ModeHom' a ◯} -> {μ : ModeHom' b a} -> {Γ : CtxExt ω} -> {Γp : isCtx₂ (ε ⋆ Γ)}
                      -> transl-Ctx (Γ ↶ μ) (isGood:splits Γp) ≡ addRestr μ (transl-Ctx Γ Γp)
  lemma:transl,restr = {!!}


    -- let Γ' , i = transl-Ctx Γ Γp
    -- in {!!}
  -- transl-Ctx (_∙!_ {◯} Γ μ) (stepRes Γp) = {!!}
  -- transl-Ctx (Γ ∙! (`[]` ⨾ id')) (stepRes-◻ Γp) = let Γ , i = transl-Ctx Γ Γp in Γ ,[ i ]
  -- transl-Ctx (Γ ∙! (`＠` i ⨾ id')) (stepRes-＠ Γp) = transl-Ctx Γ Γp , i

  -- ⦋ ε ⦌-Ctx = ε
  -- ⦋_⦌-Ctx {μ = μ} (Γ ∙⟮ x ∣ ν ⟯) = ⦋ Γ ⦌-Ctx , F-Type (ν ◆ μ) (⦋ x ⦌-Type)
  -- ⦋ Γ ∙! ω ⦌-Ctx = ⦋ Γ ⦌-Ctx
             -- -> ∑ λ δ -> ∀ p -> p ∈ ⟨ ps ⟩ -> ∀{Δ Δp} -> transl-Ctx Γ Γp ∣ p ↦ Δ , Δp Ctx -> Δ ⊢ ⦋ A ⦌-Type / δ GlobalFiber[ p ]

{-
  pre-schedule : ∀{Γ A i j δ ps} -> Γ , A ＠ i ,[ i ] ⊢ A ＠ j / δ GlobalFibered[ ps ]
  ⟨ pre-schedule ⟩ p x (IR.proj-＠ x₁ IR.done) (IR.stepRes (Γp IR., IR.proj-＠ x₂ IR.done)) = {!!} , {!!} , let B = {!!}
                                                                                                              t = var (res (zero (proj-＠ {!!} B)))
                                                                                                            in map-local-project B t -- var (IR.res (zero {!!}))
  ⟨ pre-schedule ⟩ p x (IR.proj-＠ x₁ IR.done) (IR.stepRes (Γp IR., IR.proj-＠ x₂ IR.Unit-▲)) = {!!} , {!!} , {!!}
  ⟨ pre-schedule ⟩ p x (IR.proj-＠ x₁ IR.done) (IR.stepRes (Γp IR., IR.proj-＠-≠ x₂)) = {!!} , {!!} , {!!}
  ⟨ pre-schedule ⟩ p x (IR.proj-＠ x₁ IR.Unit-▲) (IR.stepRes (Γp IR., x₂)) = {!!} , {!!} , {!!}
  -- ⟨ pre-schedule ⟩ p x (IR.proj-＠ x₁ IR.done) (IR.stepRes (Γp IR., x₂)) = {!!} , {!!} , {!!} -- var (IR.res (zero (proj-＠ refl-≤ {!!})))
  -- ⟨ pre-schedule ⟩ p x (IR.proj-＠ x₁ IR.Unit-▲) (IR.stepRes (Γp IR., x₂)) = {!!} , {!!} , var (IR.res (zero {!!}))
  ⟨ pre-schedule ⟩ p x (proj-＠-≠ x₁) Γp = {!!}
  -}

  -- schedule : ∀{Γ A i j} -> Γ , A ＠ i ⊢ ◻ (A ＠ j) / {!!} GlobalFiber[ {!!} ]
  -- schedule = {!!}

  multibox : ∀{ν : ModeHom' ◯ ▲} -> ∀{Γ i X ps} -> addRestr ν (Γ , i) ⊢ X GlobalFibered[ ps ]
             -> Γ ⊢ F-Type ν X ＠ i GlobalFibered[ ps ]
  multibox {ν = `[]` ⨾ id'} t = box-GlobalFibered t
  multibox {ν = `[]` ⨾ `＠` U ⨾ ν} t = multibox {ν = ν} (box-GlobalFibered t)

  multibox' : ∀{ν : ModeHom' ◯ ◯} -> ∀{Γ X ps} -> addRestr ν Γ ⊢ X GlobalFibered[ ps ]
             -> Γ ⊢ F-Type ν X GlobalFibered[ ps ]
  multibox' {ν = id'} t = t
  multibox' {ν = `[]` ⨾ `＠` U ⨾ ν} t = multibox' {ν = ν} (box-GlobalFibered t)

  -- transl-Var : ∀{ω : ModeHom' ◯ ◯} {Γ : CtxExt ω} {ps Γp} {A : ⊢Type ◯} -> (ε ⋆ Γ) ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> transl-Ctx Γ Γp ⊢ ⦋ A ⦌-Type GlobalFibered[ ps ]
  -- transl-Var {Γ = Γ ∙⟮ x ∣ μ ⟯} zero = {!!}
  -- transl-Var {Γ = Γ ∙⟮ x ∣ μ ⟯} (suc v) = {!!}
  -- transl-Var {Γ = Γ ∙! ω} v = {!!}

  -- transl-Mod : ModeHom' ▲ ◯ -> ((𝒫ᶠⁱⁿ (Proc ρ)) ×-𝒰 List (𝒫ᶠⁱⁿ (Proc ρ)))
  -- transl-Mod = {!!}

  -- transl-Mod : ModeHom' ◯ ◯ -> (List (𝒫ᶠⁱⁿ (Proc ρ)))
  -- transl-Mod ω = {!!}

  transl-Mod : ModeHom' ◯ ◯ -> (List (𝒫ᶠⁱⁿ (Proc ρ)))
  transl-Mod id' = []
  transl-Mod (`[]` ⨾ `＠` U ⨾ ω) = U ∷ transl-Mod ω

  transl-Mod-rec : ModeHom' ◯ ◯ -> (List (𝒫ᶠⁱⁿ (Proc ρ))) -> (List (𝒫ᶠⁱⁿ (Proc ρ)))
  transl-Mod-rec id' xs = xs
  transl-Mod-rec (`[]` ⨾ `＠` U ⨾ ω) xs = transl-Mod-rec ω (U ∷ xs)


  transl-Mod' : ModeHom' ◯ ◯ -> (List (𝒫ᶠⁱⁿ (Proc ρ)))
  transl-Mod' ω = transl-Mod-rec ω []

  -- map-restr : ∀{Γ B} -> Γ ⊢Var B GlobalFiber[ transl-Mod η ]
  --                  -> addRestr ω Γ ⊢Var B GlobalFiber[ transl-Mod (ω ◆' η) ]
  -- map-restr {ω = id'} v = v
  -- map-restr {ω = `[]` ⨾ `＠` U ⨾ ω} v = let zz = map-restr {ω = ω} v in {!!}

  -- add-restr-var : Γ ⊢Var B GlobalFiber[ ps ] -> Γ ,[ U ] ⊢Var B GlobalFiber

  cons : ∀{A : 𝒰 𝑙} -> A × List A -> List A
  cons (a , as) = a ∷ as


  postpend : ∀{A : 𝒰 𝑙} -> (List A) -> A -> A × List A
  postpend [] x = x , []
  postpend (x ∷ xs) z = x , cons (postpend xs z)

  rev' : ∀{A : 𝒰 𝑙} -> List A -> List A
  rev' [] = []
  rev' (x ∷ xs) = cons (postpend (rev' xs) x)


{-
  map-restr : ∀{Γ B ps} -> Γ ⊢Var B GlobalFiber[ (rev (transl-Mod ω)) <> ps ]
                   -> addRestr ω Γ ⊢Var B GlobalFiber[ ps ]
  map-restr {ω = id'} v = v
  map-restr  {ω = (`[]` ⨾ `＠` U ⨾ ω)} {Γ = Γ} {B} {ps} v =
    let v₀ : Γ ⊢Var B GlobalFiber[(rev (transl-Mod ω) ++-List ( U ∷ [] )) ++-List ps ]
        v₀ = v

        p₀ : (rev (transl-Mod ω) ++-List ( U ∷ [] )) ++-List ps ≡  rev (transl-Mod ω) ++-List (( U ∷ [] ) ++-List ps) 
        p₀ = {!!}

        v₁ : Γ ⊢Var B GlobalFiber[ rev (transl-Mod ω) ++-List (( U ∷ [] ) ++-List ps) ]
        v₁ = transp-≡ (cong-≡ (λ ξ -> Γ ⊢Var B GlobalFiber[ ξ ]) p₀) v₀

        v'' = map-restr {ω = ω} v₁

    in res v''

  map-restr' : ∀{Γ B p} -> Γ ⊢Var B GlobalFiber[ (rev' (p ∷ (transl-Mod ω))) ]
                   -> addRestr ω Γ ⊢Var B GlobalFiber[ p ∷ [] ]
  map-restr' = {!!}

-}


{-
  transl-Var : ∀{ω : ModeHom' a ◯} (Γ : CtxExt ω) -> ∀ Γp -> {X : ⊢Type ◯}
               -> (ε ⋆ Γ) ⊢Var⟮ X ∣ μ ⇒ η ⟯
               -- -> ∀{A p} -> ∀ (ν : ModeHom' ◯ a) -> π ⦋ X ⦌-Type ∣ p , transl-Mod (ν ◆' η) ↦ A Type
               -> ∀{A p} -> ∀ (ν : ModeHom' ◯ a) -> π F-Type μ ⦋ X ⦌-Type ∣ postpend (rev' (transl-Mod (ν ◆' η))) p ↦ A Type
               -> ∀{B} -> ϕ A ↦ B
               -> addRestr ν (transl-Ctx Γ Γp) ⊢Var B GlobalFiber[ p ∷ [] ]
  transl-Var (Γ ∙⟮ A ∣ μ ⟯) (stepVar Γp) zero ν Xp Fp = map-restr' {ω = ν} (zero Xp Fp)
  transl-Var (Γ ∙⟮ A ∣ μ ⟯) (stepVar Γp) (suc x) ν Xp Fp = {!!}
  -- transl-Var (_∙!_ {▲} Γ ω) (stepRes Γp) (suc! x) ν = {!!}
  transl-Var (_∙!_ Γ ω) (stepRes Γp) (suc! x) ν Xp Fp =
    let xx = transl-Var Γ Γp x (ν ◆' ω) Xp Fp
    in {!!}

  transl-Var' : ∀{ω : ModeHom' ◯ ◯} (Γ : CtxExt ω) -> ∀ Γp -> {X : ⊢Type ◯}
               -> (ε ⋆ Γ) ⊢Var⟮ X ∣ μ ⇒ η ⟯
               -- -> ∀{A p} -> ∀ (ν : ModeHom' ◯ a) -> π ⦋ X ⦌-Type ∣ p , transl-Mod (ν ◆' η) ↦ A Type
               -> ∀{A p} -> π F-Type μ ⦋ X ⦌-Type ∣ postpend (rev' (transl-Mod (η))) p ↦ A Type
               -> ∀{B} -> ϕ A ↦ B
               -> transl-Ctx Γ Γp ⊢Var B GlobalFiber[ p ∷ [] ]

  transl-Var' Γ Γp v Xp Xq = transl-Var Γ Γp v id' Xp Xq



  make-π : ∀ (μ : ModeHom' ◯ ◯) X p -> ∑ λ A -> π F-Type μ ⦋ X ⦌-Type ∣ postpend (rev' (transl-Mod η)) p ↦ A Type
                                       ×-𝒰 ϕ A ↦ π-Type ⦋ X ⦌-Type (p , [])
  make-π μ = {!!}

  -- make-π-id : ∀ (μ : ModeHom' ◯ ◯) X p -> ∑ λ A -> π F-Type μ ⦋ X ⦌-Type ∣ postpend (rev' (transl-Mod μ)) p ↦ A Type
  --                                      ×-𝒰 ϕ A ↦ π-Type ⦋ X ⦌-Type {!!} (p , [])
  -- make-π-id id' X p = π-Type ⦋ X ⦌-Type {!!} (p , []) , {!!}
  -- make-π-id (`[]` ⨾ `＠` U ⨾ μ) X p =
  --   let A' , Ap , Aq = make-π-id μ X p
  --   in {!!}


  skip-step : ∀ X U -> ∀{r rs} -> ϕ π-Type (◻ X ＠ U) (U , (r ∷ rs)) ↦ π-Type X (r , rs)
  skip-step X U with decide-≤ U U
  ... | no x = ⊥-elim (x refl-≤)
  ... | yes x = proj-＠

  fmap-step : ∀{X r rs Y u us} -> ϕ π-Type X (r , rs) ↦ π-Type Y (u , us)
              -> ϕ π-Type (F-Type μ X) (r , rs) ↦ π-Type (F-Type μ Y) (u , us)
  fmap-step {μ = id'} {X = X} {r} {rs} {Y} {u} {us} = {!!}
  fmap-step {μ = (`[]` ⨾ `＠` U ⨾ μ)} {X = X} {r} {rs} {Y} {u} {us} v = fmap-step {μ = μ} {!!}


  _◆-ϕ_ : ∀{A B C : Type ▲} -> ϕ A ↦ B -> ϕ B ↦ C -> ϕ A ↦ C
  _◆-ϕ_ = {!!}

{-
  make-π-id : ∀ (μ : ModeHom' ◯ ◯) X p -> ϕ π-Type (F-Type μ ⦋ X ⦌-Type) {!!} (postpend (rev' (transl-Mod μ)) p)
                                          ↦ π-Type ⦋ X ⦌-Type {!!} (p , [])
  make-π-id id' X p = id-ϕ
  make-π-id (`[]` ⨾ `＠` U ⨾ μ) X p =
    let Ap : ϕ π-Type (F-Type μ ⦋ X ⦌-Type) {!!} (postpend (rev' (transl-Mod μ)) p) ↦ π-Type ⦋ X ⦌-Type {!!} (p , [])
        Ap = make-π-id μ X p

        Bp : ϕ π-Type (◻ (F-Type μ ⦋ X ⦌-Type) ＠ U) (◻ {!!} ＠ U) (U , cons ((postpend (rev' (transl-Mod μ)) p))) ↦ π-Type (F-Type μ ⦋ X ⦌-Type) {!!} (postpend (rev' (transl-Mod μ)) p)
        Bp = skip-step (F-Type μ ⦋ X ⦌-Type) {!!} U

        Bp' : ϕ π-Type (◻ (⦋ X ⦌-Type) ＠ U) (◻ {!!} ＠ U) (U , cons ((postpend (rev' (transl-Mod μ)) p))) ↦ π-Type (⦋ X ⦌-Type) {!!} (postpend (rev' (transl-Mod μ)) p)
        Bp' = skip-step (⦋ X ⦌-Type) {!!} U

        Bp'2 : ϕ π-Type (◻ (⦋ X ⦌-Type) ＠ U) (◻ {!!} ＠ U) (((postpend (rev' (transl-Mod (`[]` ⨾ `＠` U ⨾ μ))) p))) ↦ π-Type (⦋ X ⦌-Type) {!!} (postpend (rev' (transl-Mod μ)) p)
        Bp'2 = {!!} -- skip-step (⦋ X ⦌-Type) {!!} U

        Bp'' : ϕ π-Type (F-Type μ (◻ (⦋ X ⦌-Type) ＠ U)) {!!} (U , cons ((postpend (rev' (transl-Mod μ)) p))) ↦ π-Type (F-Type μ ⦋ X ⦌-Type) {!!} (postpend (rev' (transl-Mod μ)) p)
        Bp'' = fmap-step {μ = μ} Bp'
    in  {!Bp''!} ◆-ϕ {!!}

-}



  cong₁-ϕ : ∀{a} -> ∀{A B C : Type a} -> A ≡ B -> ϕ A ↦ C -> ϕ B ↦ C
  cong₁-ϕ refl-≡ x = x

  make-π-id-ind : ∀ (μ : ModeHom' ◯ ◯) X p -> ϕ π-Type (F-Type (ν ◆ μ) ⦋ X ⦌-Type) (postpend (rev' (transl-Mod (ν ◆ μ))) p)
                                          ↦ π-Type (F-Type ν ⦋ X ⦌-Type) (postpend (rev' (transl-Mod (ν))) p)
  make-π-id-ind id' X p = id-ϕ
  make-π-id-ind {ν = ν} (`[]` ⨾ `＠` U ⨾ μ) X p =
    let Ap = make-π-id-ind {ν = ν ◆ `[]` ⨾ `＠` U ⨾ id'} μ X p

        Bp₀ : ϕ π-Type (F-Type (`[]` ⨾ `＠` U ⨾ id') (F-Type ν ⦋ X ⦌-Type)) (U , cons (postpend (rev' (transl-Mod ν)) p))
              ↦ π-Type (F-Type ν ⦋ X ⦌-Type) (postpend (rev' (transl-Mod (ν))) p)
        Bp₀ = skip-step (F-Type ν ⦋ X ⦌-Type) U

        p₀ : (F-Type (`[]` ⨾ `＠` U ⨾ id') (F-Type ν ⦋ X ⦌-Type)) ≡ (F-Type (ν ◆ `[]` ⨾ `＠` U ⨾ id') ⦋ X ⦌-Type)
        p₀ = sym-≡ (F-Type-map {X = ⦋ X ⦌-Type} {μ = ν} {ν = (`[]` ⨾ `＠` U ⨾ id')})

        p₁ : U , cons (postpend (rev' (transl-Mod ν)) p) ≡ postpend (rev' (transl-Mod (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p
        p₁ = {! !}

        Bp : ϕ π-Type (F-Type (ν ◆ `[]` ⨾ `＠` U ⨾ id') ⦋ X ⦌-Type) (postpend (rev' (transl-Mod (ν ◆ (`[]` ⨾ `＠` U ⨾ id')))) p)
            ↦ π-Type (F-Type ν ⦋ X ⦌-Type) (postpend (rev' (transl-Mod (ν))) p)
        Bp = cong₁-ϕ (cong-≡ (λ ξ -> π-Type ξ (U , cons (postpend (rev' (transl-Mod ν)) p))) p₀
                     ∙-≡ cong-≡ (λ ξ -> π-Type (F-Type (ν ◆ `[]` ⨾ `＠` U ⨾ id') ⦋ X ⦌-Type) ξ) p₁) Bp₀

    in Ap ◆-ϕ Bp

-}


{-
  make-π-under-ind : ∀ (μ ν ω : ModeHom' ◯ ◯) X p -> ∀{C}
                       -> ϕ π-Type (F-Type ν ⦋ X ⦌-Type) (postpend (rev' (transl-Mod ω)) p) ↦ C

                       -> ϕ π-Type (F-Type (ν ◆ μ) ⦋ X ⦌-Type) (postpend (rev' (transl-Mod (ω ◆ μ))) p) ↦ C

  make-π-under-ind id' ν ω X p P = P
  make-π-under-ind (`[]` ⨾ `＠` U ⨾ μ) ν ω X p PP =
    let Ap = make-π-under-ind μ (ν ◆ `[]` ⨾ `＠` U ⨾ id') (ω ◆ `[]` ⨾ `＠` U ⨾ id') X p {!!}

        -- Bp₀ : ϕ π-Type (F-Type (`[]` ⨾ `＠` U ⨾ id') (F-Type ν ⦋ X ⦌-Type)) (U , cons (postpend (rev' (transl-Mod ν)) p))
        --       ↦ π-Type (F-Type ν ⦋ X ⦌-Type) (postpend (rev' (transl-Mod (ν))) p)
        -- Bp₀ = skip-step (F-Type ν ⦋ X ⦌-Type) U

        -- p₀ : (F-Type (`[]` ⨾ `＠` U ⨾ id') (F-Type ν ⦋ X ⦌-Type)) ≡ (F-Type (ν ◆ `[]` ⨾ `＠` U ⨾ id') ⦋ X ⦌-Type)
        -- p₀ = sym-≡ (F-Type-map {X = ⦋ X ⦌-Type} {μ = ν} {ν = (`[]` ⨾ `＠` U ⨾ id')})

        -- p₁ : U , cons (postpend (rev' (transl-Mod ν)) p) ≡ postpend (rev' (transl-Mod (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p
        -- p₁ = {! !}

        -- Bp : ϕ π-Type (F-Type (ν ◆ `[]` ⨾ `＠` U ⨾ id') ⦋ X ⦌-Type) (postpend (rev' (transl-Mod (ν ◆ (`[]` ⨾ `＠` U ⨾ id')))) p)
        --     ↦ π-Type (F-Type ν ⦋ X ⦌-Type) (postpend (rev' (transl-Mod (ν))) p)
        -- Bp = cong₁-ϕ (cong-≡ (λ ξ -> π-Type ξ (U , cons (postpend (rev' (transl-Mod ν)) p))) p₀
        --              ∙-≡ cong-≡ (λ ξ -> π-Type (F-Type (ν ◆ `[]` ⨾ `＠` U ⨾ id') ⦋ X ⦌-Type) ξ) p₁) Bp₀

    in Ap ◆-ϕ {!!}

-}

  local-var-impossible : ∀{a b c A} {Γ : Ctx a} -> (Γp : isCtx₂ Γ) -> {μ : ModeHom' b ▲} {η : ModeHom' c ▲} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> 𝟘-𝒰
  local-var-impossible (stepRes _ Γp) (suc! v) = local-var-impossible Γp v
  local-var-impossible (stepVar Γp) (suc v) = local-var-impossible Γp v



{-
  make-π-id : ∀ (μ : ModeHom' ◯ ◯) X p -> ϕ π-Type (F-Type (μ) ⦋ X ⦌-Type) (postpend (rev' (transl-Mod μ)) p)
                                          ↦ π-Type (⦋ X ⦌-Type) (p , [])
  make-π-id μ X p = make-π-id-ind {ν = id} μ X p

  make-π-broadcast : ∀ X U p -> ϕ π-Type (◻ ⦋ X ⦌-Type ＠ U) (p , []) ↦ π-Type (⦋ X ⦌-Type) (p , [])
  make-π-broadcast = {!!}

  make-π-prepare : ∀ A U V p -> ϕ π-Type (◻ ⦋ A ⦌-Type ＠ U) (U , (V ∷ p ∷ [])) ↦ π-Type (⦋ A ⦌-Type) (p , [])
  make-π-prepare A U V p with decide-≤ U U
  ... | no x = {!!}
  ... | yes x = proj-◻ ◆-ϕ proj-＠

  make-π-prepare' : ∀ X p (U V : 𝒫ᶠⁱⁿ (Proc ρ)) -> ϕ π-Type (F-Type (id' ◆ (`[]` ⨾ `＠` U ⨾ id')) ⦋ X ⦌-Type) (postpend (rev' (transl-Mod ((`[]` ⨾ `＠` V ⨾ `[]` ⨾ id') ◆ (`＠` U ⨾ id')))) p)
                                                   ↦ π-Type (⦋ X ⦌-Type) (p , [])
  make-π-prepare' X p U V = make-π-prepare X U V p

-}


{-
-}

    -- transl-Var' : ∀{ω : ModeHom' a ◯} (Γ : CtxExt ω) -> ∀ Γp -> {X : ⊢Type ◯}
    --             -> (ε ⋆ Γ) ⊢Var⟮ X ∣ μ ⇒ η ⟯
    --             -> ∀{p Δ B}
    --             -> π ⦋ X ⦌-Type ∣ p , [] ↦ B Type
    --             -> (transl-Ctx' Γ Γp) ∣ p ∷ [] ↦ Δ Ctx
    --             -> Δ ⊢Var B GlobalFiber[ p ∷ [] ]
    -- transl-Var' {a = ▲} (Γ ∙! ω) (stepRes Γp) (suc! v) Xp Γpp = let Z = transl-Var' Γ Γp v Xp {!!} in {!!} 
    -- transl-Var' {a = ◯} Γ Γp v Xp Γpp = transl-Var Γ Γp v Xp Γpp


  transl-Mod3 : ModeHom' ◯ a -> (List (𝒫ᶠⁱⁿ (Proc ρ)))
  transl-Mod3 id' = []
  transl-Mod3 (`[]` ⨾ id') = []
  transl-Mod3 (`[]` ⨾ `＠` U ⨾ ω) = U ∷ transl-Mod3 ω

  comp-transl-Mod3 : ∀{μ : ModeHom' ◯ ◯} {ν : ModeHom' ◯ a} -> transl-Mod3 (μ ◆' ν) ≡ transl-Mod3 μ <> transl-Mod3 ν
  comp-transl-Mod3 {μ = id'} = refl-≡
  comp-transl-Mod3 {μ = (`[]` ⨾ `＠` U ⨾ μ)} = cong-≡ (λ ξ -> U ∷ ξ) (comp-transl-Mod3 {μ = μ})

  -- {-# REWRITE comp-transl-Mod3 #-}

  addResProj : ∀{Γ Δ} {ω : ModeHom' ◯ a} -> ∀{ps} -> addRestr' ω Γ ∣ ps ↦ Δ Ctx
                -> forget Γ ∣ ps <> transl-Mod3 ω  ↦ Δ Ctx
  addResProj = {!!}


  -- transl-Var : ∀{ω : ModeHom' a ◯} (Γ : CtxExt ω) -> ∀ Γp -> {X : ⊢Type b}
  --             -> (ε ⋆ Γ) ⊢Var⟮ X ∣ μ ⇒ η ⟯
  --             -- -> ∀{A p} -> ∀ (ν : ModeHom' ◯ a) -> π ⦋ X ⦌-Type ∣ p , transl-Mod (ν ◆' η) ↦ A Type
  --             -- -> ∀{A p} -> ∀ (ν : ModeHom' ◯ a) -> π F-Type μ ⦋ X ⦌-Type ∣ postpend (rev' (transl-Mod (ν ◆' η))) p ↦ A Type
  --             -- -> ∀{B} -> ϕ A ↦ B
  --             -> ∀{p ps Δ B}
  --             -> π F-Type μ ⦋ X ⦌-Type ∣ p , ps ↦ B Type
  --             -> (transl-Ctx' Γ Γp) ∣ p ∷ ps ↦ Δ Ctx
  --             -> Δ ⊢Var B GlobalFiber[ p ∷ ps ]

  -- β-addRestr : addRestr ν (Γ , X) ≡ 

  -- transl-Var : ∀{ω : ModeHom' a ◯} (Γ : CtxExt ω) -> ∀ Γp -> {X : ⊢Type b}
  --             -> (ε ⋆ Γ) ⊢Var⟮ X ∣ μ ⇒ η ⟯
  --             -> rev (transl-Mod3 μ) ≼' rev' (transl-Mod3 (ν ◆' η))
  --             -- -> ∀{A p} -> ∀ (ν : ModeHom' ◯ a) -> π ⦋ X ⦌-Type ∣ p , transl-Mod (ν ◆' η) ↦ A Type
  --             -- -> ∀{A p} -> ∀ (ν : ModeHom' ◯ a) -> π F-Type μ ⦋ X ⦌-Type ∣ postpend (rev' (transl-Mod (ν ◆' η))) p ↦ A Type
  --             -- -> ∀{B} -> ϕ A ↦ B
  --             -> ∀{p Δ B}
  --             -- -> π F-Type μ ⦋ X ⦌-Type ∣ postpend (rev' (transl-Mod (ν ◆' η))) p ↦ B Type
  --             -- -> π F-Type μ ⦋ X ⦌-Type ∣ postpend (rev' (transl-Mod (ν ◆' η))) p ↦ B Type
  --             -> transl-Ctx' Γ Γp ∣ cons (postpend (rev' (transl-Mod3 ν)) p) ↦ Δ Ctx
  --             -> Δ ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 ν)) p) ]


  F2-Type : (List (𝒫ᶠⁱⁿ (Proc ρ))) -> Type ◯ -> Type ◯
  F2-Type [] X = X
  F2-Type (x ∷ xs) X = ◻ (F2-Type xs X) ＠ x


  F2-comp : ∀{X } -> ∀ xs ys -> F2-Type (xs <> ys) X ≡ F2-Type xs (F2-Type ys X)
  F2-comp [] ys = refl-≡
  F2-comp (x ∷ xs) ys = cong-≡ (λ X -> ◻ X ＠ x) (F2-comp xs ys)

  F-prop : ∀{X} -> F-Type μ X ≡ F2-Type (rev (transl-Mod3 μ)) X
  F-prop {μ = id'} = refl-≡
  F-prop {μ = `[]` ⨾ `＠` U ⨾ μ} {X = X} =
    let Z = F-prop {μ = μ} {X = (◻ X ＠ U)}
    in Z ∙-≡ sym-≡ (F2-comp (rev (transl-Mod3 μ)) _ )

  lift-π-single : ∀{X A p ps q} -> π X ∣ p , ps ↦ A Type -> π ◻ X ＠ q ∣ q , (p ∷ ps) ↦ A Type
  lift-π-single X = proj-＠ refl-≤ (IR.proj-◻ X)

  lift-π-impl : ∀{X A p ps r} -> π X ∣ r , [] ↦ A Type -> π F2-Type (p ∷ ps) X ∣ p , ps <> (r ∷ []) ↦ A Type
  lift-π-impl {ps = []} Xp = proj-＠ refl-≤ (IR.proj-◻ Xp)
  lift-π-impl {ps = x ∷ ps} Xp = lift-π-single (lift-π-impl Xp)

  lift-π : ∀{X A ps qs r} -> ps ≼' qs -> π X ∣ r , [] ↦ A Type -> π F2-Type ps X ∣ fst (postpend qs r) , drop 1 (ps <> (r ∷ [])) ↦ A Type
  lift-π {qs = []} [] Xp = Xp
  lift-π {qs = x ∷ qs} (_∷_ .x x₁) Xp = lift-π-impl Xp

  lift-π-direct : ∀{X B ps r} -> (π X ∣ r , [] ↦ B Type) -> π F2-Type ps X ∣ fst (postpend ps r) , snd (postpend ps r) ↦ B Type
  lift-π-direct = {!!}

  mkVar : ∀{Δ X A r ps qs} -> ps ≼' qs -> π X ∣ r , [] ↦ A Type -> Δ , F2-Type ps X ⊢Var A GlobalFiber[ cons (postpend qs r) ]
  mkVar {r = r} {ps} {qs} [] Xp = zero done Xp -- (lift-π {ps = ps} {qs = qs} {r = r} P Xp)
  mkVar {r = r} {ps} {qs} (a ∷ Ps) Xp = zero {!P!} (lift-π {ps = ps} {qs = qs} {r = r} (a ∷ Ps) Xp)

  mkVar-▲ : ∀{Δ A B U V r ps qs} -> (ps <> (U ∷ [])) ≼' (qs <> (V ∷ [])) -> π A ＠ V ∣ r , [] ↦ B Type -> Δ , F2-Type ps (A ＠ U) ⊢Var B GlobalFiber[ cons (postpend qs r) ]
  mkVar-▲ {ps = []} {qs = []} (_ ∷ x) P = zero done P
  mkVar-▲ {ps = []} {qs = x ∷ qs} (.x ∷ x₁) P with P
  ... | IR.proj-＠ x₂ IR.done = zero done ( (proj-＠ refl-≤ done))
  ... | IR.proj-＠-≠ x₂ = none
  mkVar-▲ {U = U} {V} {r = r} {ps = x ∷ ps} {qs = .x ∷ qs} (.x ∷ x₁) P with split-≼ ps qs x₁
  ... | no (Q , refl-≡) = zero {!!} ( (proj-＠ refl-≤ (proj-◻ (lift-π-direct {ps = ps} P))))
  ... | yes Q with P
  ... | IR.proj-＠ x₂ IR.done = zero {!!} ( (proj-＠ refl-≤ (proj-◻ (lift-π-direct {ps = ps} (proj-＠ refl-≤ done)))))
  ... | IR.proj-＠-≠ x₂ = none
  mkVar-▲ {U = U} {.x} {r = r} {ps = x ∷ []} {qs = []} (.x ∷ ()) P
  mkVar-▲ {U = U} {.x} {r = r} {ps = x ∷ x₂ ∷ ps} {qs = []} (.x ∷ ()) P



  updateVar : ∀{X A B Δ p ps} -> π X ∣ p , [] ↦ B Type ->  Δ , X ⊢Var A GlobalFiber[ p ∷ ps ] -> Δ , B ＠ p ⊢Var A GlobalFiber[ p ∷ ps ]
  updateVar P (IR.zero x x₁) = zero x (lem-12 P x₁)
  updateVar P (IR.suc v) = suc v
  updateVar P (none) = none







  -- transl-Var : ∀{ω : ModeHom' a ◯} (Γ : CtxExt ω) -> ∀ Γp -> {X : ⊢Type b}
  --             -> (ε ⋆ Γ) ⊢Var⟮ X ∣ μ ⇒ η ⟯
  --             -> rev (transl-Mod3 μ) ≼' rev' (transl-Mod3 (ν ◆' η))
  --             -> ∀{p Δ B}
  --             -> transl-Ctx' Γ Γp ∣ cons (postpend (rev' (transl-Mod3 ν)) p) ↦ Δ Ctx
  --             -> Δ ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 ν)) p) ]

  transl-Var-▲ : ∀{ω : ModeHom' ◯ ◯} (Γ : CtxExt ω) -> ∀ Γp -> {A : ⊢Type ▲} -> ∀{U V}
              -> (ε ⋆ Γ) ⊢Var⟮ A ∣ (`＠` U ⨾ μ) ⇒ (η) ⟯
              -> rev (transl-Mod3 (`[]` ⨾ `＠` U ⨾ μ)) ≼' rev' (transl-Mod3 (`[]` ⨾ `＠` V ⨾ (ν ◆' η)))
              -> ∀{p Δ B}
              -> transl-Ctx' Γ Γp ∣ cons (postpend (rev' (transl-Mod3 (ν))) p) ↦ Δ Ctx
              -> π ⦋ A ⦌-Type ＠ V ∣ p , [] ↦ B Type
              -> Δ ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 (ν))) p) ]
  transl-Var-▲ {ν = ν} (Γ ∙⟮ x ∣ (`＠` U ⨾ μ) ⟯) (stepVar Γp) {A = A} {U} {V} zero μ≼ν {p = p} {Δ = Δ , _} {B = B} (Γpp IR., x₁) Xp =
    let
        YY : (Δ , F2-Type (rev (transl-Mod3 (μ))) (⦋ x ⦌-Type ＠ U)) ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 (ν))) p) ]
        YY = mkVar-▲ {U = U} {V = V} {ps = (rev (transl-Mod3 (μ)))} {qs = (rev' (transl-Mod3 (ν)))} {!μ≼ν!} Xp
        -- mkVar {ps = (rev (transl-Mod3 μ))} {qs = (rev' (transl-Mod3 (`[]` ⨾ ν)))} μ≼ν Xp

        ZZ : (Δ , F-Type μ (⦋ x ⦌-Type ＠ U)) ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 (ν))) p) ]
        ZZ = {!!}

    in updateVar x₁ ZZ
  transl-Var-▲ {ν = ν} (Γ ∙! (`＠` U ⨾ id') ∙! .(`[]` ⨾ id')) (stepRes `[]` (stepRes x Γp)) (suc! (suc! v)) PP {p = p} {Δ = Δ ,[ _ ]} {B = B} (stepRes Γpp) Xp = {!!}
  transl-Var-▲ {ν = ν} (Γ Definition-MTTꟳ.∙⟮ x ∣ μ ⟯) (stepVar Γp) (Definition-MTTꟳ.suc v) PP (Γpp IR., x₁) Xp =
    let res = transl-Var-▲ {ν = ν} Γ Γp v PP Γpp Xp
    in suc res


    -- let Γpp' : transl-Ctx' Γ Γp ∣ cons (postpend (rev' (transl-Mod3 (ν ◆ (`[]` ⨾ `＠` U ⨾ id')))) p) ↦ Δ Ctx
    --     Γpp' = {!!}

    --     result = transl-Var-▲ {ν = ν ◆ (`[]` ⨾ `＠` U ⨾ id')} Γ Γp v PP Γpp' Xp

    --     P1 : cons (postpend (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p) ≡ U ∷ cons (postpend (rev' (transl-Mod3 ν)) p)
    --     P1 = cons (postpend (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p)
    --               ⟨ {!!} ⟩-≡
    --          cons (postpend (rev' (transl-Mod3 (ν) <> transl-Mod3 (`[]` ⨾ `＠` U ⨾ id'))) p)
    --               ⟨ {!!} ⟩-≡
    --          U ∷ cons (postpend (rev' (transl-Mod3 ν)) p) ∎-≡

    --     result' : Δ ⊢Var B GlobalFiber[ U ∷ cons (postpend (rev' (transl-Mod3 ν)) p) ]
    --     result' = transp-≡ (cong-≡ (λ ξ -> Δ ⊢Var B GlobalFiber[ ξ ]) {!!}) result

    -- in res result'




  transl-Var-◯ : ∀{ω : ModeHom' ◯ ◯} (Γ : CtxExt ω) -> ∀ Γp -> {X : ⊢Type ◯}
              -> (ε ⋆ Γ) ⊢Var⟮ X ∣ μ ⇒ η ⟯
              -> rev (transl-Mod3 μ) ≼' rev' (transl-Mod3 (ν ◆' η))
              -> ∀{p Δ B}
              -> transl-Ctx' Γ Γp ∣ cons (postpend (rev' (transl-Mod3 ν)) p) ↦ Δ Ctx
              -> π ⦋ X ⦌-Type ∣ p , [] ↦ B Type
              -> Δ ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 ν)) p) ]

  transl-Var-◯ {ν = ν} (Γ ∙⟮ x ∣ μ ⟯) (stepVar Γp) zero μ≼ν {p = p} {Δ = Δ , _} {B = B} (Γpp IR., x₁) Xp =
    let
        YY : (Δ , F2-Type (rev (transl-Mod3 μ)) ⦋ x ⦌-Type) ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 ν)) p) ]
        YY = mkVar {ps = (rev (transl-Mod3 μ))} {qs = (rev' (transl-Mod3 ν))} μ≼ν Xp

        ZZ : (Δ , F-Type μ ⦋ x ⦌-Type) ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 ν)) p) ]
        ZZ = {!!}

    in updateVar x₁ ZZ
  transl-Var-◯ {ν = ν} (Γ Definition-MTTꟳ.∙⟮ x ∣ μ ⟯) (stepVar Γp) (Definition-MTTꟳ.suc v) PP (Γpp IR., x₁) Xp =
    let res = transl-Var-◯ {ν = ν} Γ Γp v PP Γpp Xp
    in suc res
  transl-Var-◯ {ν = ν} (Γ ∙! (`＠` U ⨾ id') ∙! .(`[]` ⨾ id')) (stepRes `[]` (stepRes x Γp)) (suc! (suc! v)) PP {p = p} {Δ = Δ ,[ _ ]} {B = B} (stepRes Γpp) Xp =
    let Γpp' : transl-Ctx' Γ Γp ∣ cons (postpend (rev' (transl-Mod3 (ν ◆ (`[]` ⨾ `＠` U ⨾ id')))) p) ↦ Δ Ctx
        Γpp' = {!!}

        result = transl-Var-◯ {ν = ν ◆ (`[]` ⨾ `＠` U ⨾ id')} Γ Γp v PP Γpp' Xp

        P1 : cons (postpend (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p) ≡ U ∷ cons (postpend (rev' (transl-Mod3 ν)) p)
        P1 = cons (postpend (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p)
                  ⟨ {!!} ⟩-≡
             cons (postpend (rev' (transl-Mod3 (ν) <> transl-Mod3 (`[]` ⨾ `＠` U ⨾ id'))) p)
                  ⟨ {!!} ⟩-≡
             U ∷ cons (postpend (rev' (transl-Mod3 ν)) p) ∎-≡

        result' : Δ ⊢Var B GlobalFiber[ U ∷ cons (postpend (rev' (transl-Mod3 ν)) p) ]
        result' = transp-≡ (cong-≡ (λ ξ -> Δ ⊢Var B GlobalFiber[ ξ ]) {!!}) result

    in res result'






  mutual
    {-# TERMINATING #-} -- NOTE: Agda does not see that the letmod case terminates
    transl-Term-▲ : ∀{ps i} -> ∀{μ : ModeHom' ◯ ◯} -> (Γ : CtxExt μ) -> (Γp : isCtx₂ (ε ⋆ Γ))
              -> ∀{A} -> ε ⋆ Γ ∙! (`＠` i ⨾ id') ⊢ A
              -> transl-Ctx Γ Γp  ⊢ (⦋ A ⦌-Type ＠ i) GlobalFibered[ ps ]
    transl-Term-▲ Γ Γp (var {b = ▲} (suc! x) [ incl α₀ ∣ incl α₁ ]) = ⊥-elim (local-var-impossible Γp x)
    transl-Term-▲ {i = i} Γ Γp (var {b = ◯} {μ = `＠` j ⨾ μ} (suc! x) [ incl α₀ ∣ incl α₁ ]) =
      let α₀' = linearize α₀
          α₁' = linearize α₁

          P : i ≤ j
          P = {!!}

      -- in {!!}
      in IR.incl (λ p x₁ Xp Γp₁ → (let XX = (transl-Var-▲ {ν = id'} Γ Γp x {!!} Γp₁ Xp) in var XX)) -- (extend-π {μ = {!μ!}} Xp)
    transl-Term-▲ Γ Γp tt = {!!}
    transl-Term-▲ Γ Γp (mod `[]` t) = {!!}
      -- let δ' , ts' = transl-Term-◯ _ (stepRes-◻ (stepRes-＠ Γp)) t
      -- in _ , box-GlobalFibered ts'
    transl-Term-▲ Γ Γp (letmod' `[]` t s) =
      let t' = transl-Term-▲ _ Γp t
          s' = transl-Term-▲ _ (stepVar Γp) (shift-＠ (id-annotate s))
      in letin-GlobalFibered t' s'
    transl-Term-▲ Γ Γp (letmod (`＠` U) ν t s) =
      let t' = transl-Term-◯ _ (isGood:splits (stepRes _ Γp)) (splits-path t)
          t'' = cong-GlobalFibered (lemma:transl,restr {μ = ν}) t'
          s' = transl-Term-▲ _ (stepVar Γp) (shift-＠ (id-annotate s))
      in letin-GlobalFibered (multibox t'') s'
    transl-Term-▲ Γ Γp (letmod `[]` id' t s) = {!!}
    transl-Term-▲ Γ Γp (letmod `[]` (`＠` U ⨾ ν) t s) =
      -- let t' = split-path t

      --     t'' = transl-Term-▲ _ (stepRes (stepRes Γp)) t'
      --     s' = transl-Term-▲ _ (stepVar Γp) (shift-＠ (id-annotate s))

      -- in letin-GlobalFibered (multibox t'') s'
      let -- t' = split-path t

          t'' = transl-Term-▲ _ ((isGood:splits {μs = ν} (stepRes _ Γp))) (splits-path t) -- (isGood:splits {μs = (`＠` U ⨾ ν)} (stepRes _ Γp))
          t''' = cong-GlobalFibered ((lemma:transl,restr {μ = ν})) t''
          s' = transl-Term-▲ _ (stepVar Γp) (shift-＠ (id-annotate s))

      in letin-GlobalFibered (multibox t''') s'
    transl-Term-▲ Γ Γp (trans x xP t) = {!!}
    transl-Term-▲ Γ Γp (pure t) = {!!}
    transl-Term-▲ Γ Γp (seq t t₁) = {!!}
    transl-Term-▲ Γ Γp (lam t) =
      let t' = shift-＠ t
          rest' = transl-Term-▲ _ (stepVar Γp) t'
      in commute-＠-Exp _ (lam-GlobalFibered rest')
    transl-Term-▲ Γ Γp (app t t₁) = {!!}


    transl-Term-◯ : ∀{ps} -> ∀{μ : ModeHom' ◯ ◯} -> (Γ : CtxExt μ) -> (Γp : isCtx₂ (ε ⋆ Γ))
              -> ∀{A} -> ε ⋆ Γ ⊢ A
              -> transl-Ctx Γ Γp  ⊢ ⦋ A ⦌-Type GlobalFibered[ ps ]
    transl-Term-◯ Γ Γp (var {b = ▲} x [ incl α₀ ∣ incl α₁ ]) = ⊥-elim (local-var-impossible Γp x)
    transl-Term-◯ Γ Γp (var {b = ◯} {μ = μ} x [ incl α₀ ∣ incl α₁ ]) =
      let α₀' = linearize α₀
          α₁' = linearize α₁
          -- xx = transl-Var' Γ Γp x {!!} {!!}
      in IR.incl (λ p x₁ Xp Γp₁ → var (transl-Var-◯ {ν = id'} Γ Γp x {!!} Γp₁ Xp))
    transl-Term-◯ Γ Γp tt = {!!}
    transl-Term-◯ Γ Γp (mod (`＠` U) t) =
      let t' = transl-Term-▲ _ Γp t
      in t'
    transl-Term-◯ Γ Γp (letmod (`＠` U) ν t s) =
      let t' = transl-Term-◯ _ (isGood:splits Γp) (splits-path t)
          t'' = cong-GlobalFibered (lemma:transl,restr {μ = ν}) t'
          s' = transl-Term-◯ _ (stepVar Γp) s
      in letin-GlobalFibered (multibox' t'') s'
    transl-Term-◯ Γ Γp (letmod `[]` (`＠` i ⨾ ν) t s) =
      let -- t' = split-path t

          t'' = transl-Term-▲ _ (isGood:splits Γp) (splits-path t)
          t''' = cong-GlobalFibered (lemma:transl,restr {μ = ν}) t''

          s' = transl-Term-◯ _ (stepVar Γp) s
      in letin-GlobalFibered (multibox' t''') s'

    transl-Term-◯ Γ Γp (letmod' μ t t₁) = {!μ!}
    -- transl-Term-◯ Γ Γp (trans .([ incl [] ∣ incl (incl (id' ⌟[ recv _ ]⌞ id' ⌟) ∷ []) ]) br t) =
    --   let t' = transl-Term-◯ _ Γp t
    --   in broadcast-GlobalFibered t'
    transl-Term-◯ Γ Γp (pure t) = {!!}
    transl-Term-◯ Γ Γp (seq t t₁) = {!!}
    transl-Term-◯ Γ Γp (lam t) =
      let t' = transl-Term-◯ _ (stepVar Γp) t
      in lam-GlobalFibered t'
    transl-Term-◯ Γ Γp (app t s) =
      let t' = transl-Term-◯ _ Γp t
          s' = transl-Term-◯ _ Γp s
      in app-GlobalFibered t' s'


{-
-}
