
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


open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')

open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Basics hiding (_⋆_)

module _ {A B : 𝒰 𝑖} where
  transp : A ≡ B -> A -> B
  transp refl-≡ a = a

  -- cong-≡ 



module Translation (n : ℕ) where
-- (P : Preorder 𝑖) {{_ : hasDecidableEquality ⟨ P ⟩}} {{_ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)}} where

  P : Preorder _
  P = 𝒫ᶠⁱⁿ (𝔽 n)

  instance
    hasDecidableEquality:P : hasDecidableEquality ⟨ P ⟩
    hasDecidableEquality:P = {!!}

  instance
    isProp:≤ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)
    isProp:≤ = {!!}

  -- Getting the mode system
  import KamiTheory.Main.Generic.ModeSystem.2Graph.Example as 2GraphExample
  import KamiTheory.Main.Generic.ModeSystem.2Cell.Example as 2CellExample
  import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition as 2CellDefinition
  import KamiTheory.Main.Generic.ModeSystem.2Cell.Linear as 2CellLinear
  open 2CellDefinition.2CellDefinition hiding (id)
  open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Example
  open SendReceiveNarrow-ModeSystem P {{it}} {{it}}
  open 2GraphExample.SendReceiveNarrow-2Graph P
  open 2CellLinear.2CellLinear SRN
  -- open 2CellExample.SendReceiveNarrow-2Cells P {{it}} {{it}}


  -- Instantiating MTT with the 2category generated from the modesystem
  open import KamiCore.Typed.Variant.F.Definition3

  instance
    Param : MTTꟳ _
    Param = record
      { 𝓂 = Mode SRN-ModeSystem
      ; isCategory:𝓂 = isCategory:byModeSystem SRN-ModeSystem
      ; is2Category:𝓂 = is2Category:byModeSystem SRN-ModeSystem
      }


  open Definition-MTTꟳ {{Param}}
    renaming (ModeHom to ModeHom' ; _⊢_ to _⊢'_)

  instance
    isCategoryData:ModeHom : isCategoryData (Mode SRN-ModeSystem) ModeHom'
    isCategoryData:ModeHom = HomData {{isCategory:𝓂 {{Param}}}}

  instance
    isCategory:ModeHom : isCategory (Mode SRN-ModeSystem)
    isCategory:ModeHom = record { Hom = ModeHom' }

  instance
    is2Category:ModeHom : is2Category ′(Mode SRN-ModeSystem)′
    is2Category:ModeHom = is2Category:𝓂 {{Param}}


  -- Instantiating the target language with the preorder
  open import KamiCore.Typed.Variant.F.Model9

  ρ : isProcessSet _
  ρ = record { Proc = 𝔽 n }

  open IR {{ρ}}
    renaming (Ctx to Ctx' ; Mode to Mode')


  private variable
    a b c : Mode SRN-ModeSystem
    μ ν η ω : ModeHom' a b

  data isBroadcast : ∀{a b} -> {μ ν : ModeHom' a b} -> μ ⟹ ν -> 𝒰₀ where
  -- data isBroadcast {a b} : {μ ν : ModeHom' a b} -> μ ⟹ ν -> 𝒰₀ where
    -- br : ∀{U ϕ₀ ϕ₁} -> isBroadcast [ (incl []) ∣ incl (incl (ϕ₀ ⌟[ recv U ]⌞ (ϕ₁ ⌟)) ∷ []) ]
    br : ∀{U} -> isBroadcast [ (incl []) ∣ incl (incl (id' ⌟[ recv U ]⌞ (id' ⌟)) ∷ []) ]



  --------------------------------------------------
  -- Translating MTT terms into a form where the
  -- contexts only have single restrictions form.
  data isCtx₁ : Ctx a -> 𝒰₀ where
    ε : isCtx₁ {a = a} ε
    stepVar : {Γ : Ctx b} -> isCtx₁ Γ -> {A : ⊢Type a} -> {μ : a ⟶ b} -> isCtx₁ (Γ ∙⟮ A ∣ μ ⟯)
    stepRes : {Γ : Ctx b} -> isCtx₁ Γ -> {μ : BaseModeHom-SRN a b} -> isCtx₁ (Γ ∙! (μ ⨾ id))


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
      letmod : ∀(μ : BaseModeHom-SRN a b) -> (ν : b ⟶ c)
            -> Γ ∙! ν ⊢ ⟨ A ∣ μ ⨾ id' ⟩
            -> Γ ∙⟮ A ∣ μ ⨾ ν ⟯ ⊢ B
            -> Γ ⊢ B

      letmod' : ∀(μ : BaseModeHom-SRN a b)
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

    split-path : ∀{μs : ModeHom' b c} -> ∀{μ} -> ∀{A : ⊢Type a} -> Γ ∙! (μ ⨾ μs) ⊢ A -> (Γ ∙! μs) ∙! (μ ⨾ id') ⊢ A
    split-path = {!!}

    id-annotate : ∀{Γ : Ctx a} -> Γ ∙⟮ A ∣ μ ⟯ ⊢ B -> Γ ∙⟮ ⟨ A ∣ μ ⟩ ∣ id' ⟯ ⊢ B
    id-annotate = {!!}



  data isCtx₂ : Ctx a -> 𝒰₀ where
    ε : isCtx₂ {a = a} ε
    stepVar : {Γ : Ctx ◯} -> isCtx₂ Γ -> {A : ⊢Type a} -> {μ : a ⟶ ◯} -> isCtx₂ (Γ ∙⟮ A ∣ μ ⟯)
    stepRes : {Γ : Ctx a} -> isCtx₂ Γ -> isCtx₂ (Γ ∙! μ)
    -- stepRes-◻ : {Γ : Ctx ▲} -> isCtx₂ Γ -> isCtx₂ (Γ ∙! (`[]` ⨾ id))
    -- stepRes-＠ : {Γ : Ctx ◯} -> ∀{p} -> isCtx₂ Γ -> isCtx₂ (Γ ∙! (`＠` p ⨾ id))







  ⦋_⦌-Mode : Mode SRN-ModeSystem -> Mode'
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


  TargetCtx : Mode SRN-ModeSystem -> 𝒰 _
  TargetCtx ▲ = Ctx' × ⟨ P ⟩
  TargetCtx ◯ = Ctx'

  addRestr : (μ : ModeHom' a b) -> TargetCtx b -> TargetCtx a
  addRestr id' Γ = Γ
  addRestr (`＠` U ⨾ μ) Γ = addRestr μ Γ , U
  addRestr (`[]` ⨾ μ) Γ = let Γ' , U = addRestr μ Γ in Γ' ,[ U ]

  transl-Ctx : ∀{μ : ModeHom' a ◯} -> (Γ : CtxExt μ) -> isCtx₂ (ε ⋆ Γ) -> TargetCtx a
  transl-Ctx ε Γp = ε
  transl-Ctx (Γ ∙⟮ x ∣ μ ⟯) (stepVar Γp) = transl-Ctx Γ Γp , F-Type μ ⦋ x ⦌-Type
  transl-Ctx (_∙!_ Γ μ) (stepRes Γp) = addRestr μ (transl-Ctx Γ Γp)
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
        v₁ = transp (cong-≡ (λ ξ -> Γ ⊢Var B GlobalFiber[ ξ ]) p₀) v₀

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
  local-var-impossible (stepRes Γp) (suc! v) = local-var-impossible Γp v
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

  transl-Var : ∀{ω : ModeHom' ◯ ◯} (Γ : CtxExt ω) -> ∀ Γp -> {X : ⊢Type ◯}
               -> (ε ⋆ Γ) ⊢Var⟮ X ∣ μ ⇒ η ⟯
               -- -> ∀{A p} -> ∀ (ν : ModeHom' ◯ a) -> π ⦋ X ⦌-Type ∣ p , transl-Mod (ν ◆' η) ↦ A Type
               -- -> ∀{A p} -> ∀ (ν : ModeHom' ◯ a) -> π F-Type μ ⦋ X ⦌-Type ∣ postpend (rev' (transl-Mod (ν ◆' η))) p ↦ A Type
               -- -> ∀{B} -> ϕ A ↦ B
               -> ∀{p Δ B}
               -> π ⦋ X ⦌-Type ∣ p , [] ↦ B Type
               -> (transl-Ctx Γ Γp) ∣ p ∷ [] ↦ Δ Ctx
               -> Δ ⊢Var B GlobalFiber[ p ∷ [] ]
  transl-Var (Γ Definition-MTTꟳ.∙⟮ x ∣ μ ⟯) Γp Definition-MTTꟳ.zero Xp Γpp = {!!}
  transl-Var (Γ Definition-MTTꟳ.∙⟮ x ∣ μ ⟯) Γp (Definition-MTTꟳ.suc v) Xp Γpp = {!!}
  transl-Var (Γ Definition-MTTꟳ.∙! ω) Γp (Definition-MTTꟳ.suc! v) Xp Γpp = {!!}


{-

  mutual
    {-# TERMINATING #-} -- NOTE: Agda does not see that the letmod case terminates
    transl-Term-▲ : ∀{ps i} -> ∀{μ : ModeHom' ◯ ◯} -> (Γ : CtxExt μ) -> (Γp : isCtx₂ (ε ⋆ Γ))
              -> ∀{A} -> ε ⋆ Γ ∙! (`＠` i ⨾ id') ⊢ A
              -> transl-Ctx Γ Γp  ⊢ (⦋ A ⦌-Type ＠ i) GlobalFibered[ ps ]
    transl-Term-▲ Γ Γp (var x [ incl α₀ ∣ incl α₁ ]) =
      let α₀' = linearize α₀
          α₁' = linearize α₁
      -- in {!!}
      in {!!} --  IR.incl (λ p x₁ Xp Γp₁ → var (transl-Var Γ Γp x Xp Γp₁))
    transl-Term-▲ Γ Γp tt = {!!}
    transl-Term-▲ Γ Γp (mod `[]` t) = {!!}
      -- let δ' , ts' = transl-Term-◯ _ (stepRes-◻ (stepRes-＠ Γp)) t
      -- in _ , box-GlobalFibered ts'
    transl-Term-▲ Γ Γp (letmod' `[]` t s) =
      let t' = transl-Term-▲ _ Γp t
          s' = transl-Term-▲ _ (stepVar Γp) (shift-＠ (id-annotate s))
      in letin-GlobalFibered t' s'
    transl-Term-▲ Γ Γp (letmod (`＠` U) ν t s) =

      let t' = transl-Term-◯ _ (stepRes (stepRes Γp)) t
          s' = transl-Term-▲ _ (stepVar Γp) (shift-＠ (id-annotate s))
      in letin-GlobalFibered (multibox t') s'
    transl-Term-▲ Γ Γp (letmod `[]` id' t s) = {!!}
    transl-Term-▲ Γ Γp (letmod `[]` (`＠` U ⨾ ν) t s) =
      let t' = split-path t

          t'' = transl-Term-▲ _ (stepRes (stepRes Γp)) t'
          s' = transl-Term-▲ _ (stepVar Γp) (shift-＠ (id-annotate s))

      in letin-GlobalFibered (multibox t'') s'
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
    transl-Term-◯ Γ Γp (var {b = ◯} x [ incl α₀ ∣ incl α₁ ]) =
      let α₀' = linearize α₀
          α₁' = linearize α₁
          -- xx = transl-Var' Γ Γp x {!!} {!!}
      in IR.incl (λ p x₁ Xp Γp₁ → var (transl-Var Γ Γp x Xp Γp₁))
    transl-Term-◯ Γ Γp tt = {!!}
    transl-Term-◯ Γ Γp (mod (`＠` U) t) =
      let t' = transl-Term-▲ _ Γp t
      in t'
    transl-Term-◯ Γ Γp (letmod (`＠` U) ν t s) =
      let t' = transl-Term-◯ _ (stepRes Γp) t
          s' = transl-Term-◯ _ (stepVar Γp) s
      in letin-GlobalFibered (multibox' t') s'
      -- in _ , letin-GlobalFibered t' s'
    transl-Term-◯ Γ Γp (letmod `[]` (`＠` i ⨾ ν) t s) =
      let t' = split-path t

          t'' = transl-Term-▲ _ (stepRes Γp) t'

          s' = transl-Term-◯ _ (stepVar Γp) s
      in letin-GlobalFibered (multibox' t'') s'

    transl-Term-◯ Γ Γp (letmod' μ t t₁) = {!μ!}
    transl-Term-◯ Γ Γp (trans .([ incl [] ∣ incl (incl (id' ⌟[ recv _ ]⌞ id' ⌟) ∷ []) ]) br t) =
      let t' = transl-Term-◯ _ Γp t
      in broadcast-GlobalFibered t'
    transl-Term-◯ Γ Γp (pure t) = {!!}
    transl-Term-◯ Γ Γp (seq t t₁) = {!!}
    transl-Term-◯ Γ Γp (lam t) =
      let t' = transl-Term-◯ _ (stepVar Γp) t
      in lam-GlobalFibered t'
    transl-Term-◯ Γ Γp (app t s) =
      let t' = transl-Term-◯ _ Γp t
          s' = transl-Term-◯ _ Γp s
      in app-GlobalFibered t' s'



-}










