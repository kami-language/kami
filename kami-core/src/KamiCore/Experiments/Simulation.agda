-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas --rewriting --guardedness #-}

module KamiCore.Typed.Variant.F.Simulation where

open import Agora.Conventions hiding (k ; m ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Data.Nat.Properties using (+-comm)



-- We need an infinite sequence of types which all depend on each other.

record 𝕍 𝑖 : 𝒰 (𝑖 ⁺) where
  coinductive
  field H : 𝒰 𝑖
  field T : H -> 𝕍 𝑖

open 𝕍 public


mutual
  record ∞-Point (v : 𝕍 𝑖) : 𝒰 (𝑖 ⁺) where
    coinductive
    field h : H v
    field t : ∞-Open (T v h)

  record ∞-Open (v : 𝕍 𝑖) : 𝒰 (𝑖 ⁺) where
    coinductive
    field Ix : 𝒰 𝑖
    field h : Ix -> H v
    field t : ∀ i -> ∞-Point (T v (h i))


data Kind : 𝒰₀ where
  pt op : Kind

mutual
  data PointStep {𝑖} : Kind -> 𝕍 𝑖 -> 𝒰 (𝑖 ⁺) where
    [] : ∀{v} -> PointStep pt v
    _∷_ : ∀{v k} -> {I : 𝒰 𝑖} -> (h : I -> H v) -> (∀ i -> OpenStep k (T v (h i))) -> PointStep k v

  data OpenStep {𝑖} : Kind -> 𝕍 𝑖 -> 𝒰 (𝑖 ⁺) where
    [] : ∀{v} -> OpenStep op v
    _∷_ : ∀{k v} -> (h : H v) -> PointStep k (T v h) -> OpenStep k v

Point : 𝕍 𝑖 -> _
Point = OpenStep pt

Open : 𝕍 𝑖 -> _
Open = PointStep op

-- _∋_ : ∀{v} -> Open v -> Point v -> 



  -- A point is given by x ∷ [] or x ∷ U ∷ z ∷ []
  -- A Open is given by [] or U ∷ x ∷ []

record Trace (v : 𝕍 𝑖) : 𝒰 𝑖 where
  coinductive
  field h : H v
  field t : Trace (T v h)

mutual
  record Impl-∀ (v : 𝕍 𝑖) : 𝒰 𝑖 where
    constructor Ev
    coinductive
    field eval : ∀(h : H v) -> Impl-∃ (T v h)

  record Impl-∃ (v : 𝕍 𝑖) : 𝒰 𝑖 where
    constructor _,_
    coinductive
    field fst : H v
    field snd : Impl-∀ (T v fst)



empty : 𝕍 𝑖
𝕍.H empty = 𝟙
𝕍.T empty = λ x → empty

mutual
  vempty-∀ : Impl-∀ {𝑖} empty
  Impl-∀.eval vempty-∀ h = vempty-∃

  vempty-∃ : Impl-∃ {𝑖} empty
  Impl-∃.fst vempty-∃ = tt
  Impl-∃.snd vempty-∃ = vempty-∀

module Example where
  v0 : 𝕍 ℓ₀
  𝕍.H v0 = ℕ
  𝕍.H (𝕍.T v0 x) = 𝟙
  𝕍.H (𝕍.T (𝕍.T v0 x) x₁) = ℕ
  𝕍.H (𝕍.T (𝕍.T (𝕍.T v0 x) x₁) x₂) = x +-ℕ x₂ ≡ x₂ +-ℕ x
  𝕍.H (𝕍.T (𝕍.T (𝕍.T (𝕍.T v0 x) x₁) x₂) x₃) = 𝟙
  𝕍.T (𝕍.T (𝕍.T (𝕍.T (𝕍.T v0 x) x₁) x₂) x₃) x4 = empty

  i0 : Impl-∀ v0
  i0 = Ev λ a → tt , Ev λ b → +-comm a b , Ev λ h → tt , vempty-∀


  p0 : Point v0
  p0 = 1 ∷ []

  p1 : Point v0
  p1 = 1 ∷ const tt ∷ λ (i : 𝟙) -> 2 ∷ []

  -- p2 : Point v0
  -- p2 = 1 ∷ ? ∷ 2 ∷ refl-≡ ∷ tt ∷ []


{-
-- record isGenTop (X : 𝒰 𝑖) : 𝒰 𝑖 where
--   field Ix : 


-- If we have a sequence a = (a0 , a1 , a2 , a3) and b = (b0 , b1 , b2 , b3), we can combine
-- them into a ∨ b = (a0 ∨ b0 , a1 ∨ b1 , a2 ∨ b2 , ...).
--
-- We have a subrelation where a ≤ 0 forall a. And a multiplication where a * a = a
-- The point is that a * b ≤ a and a * b ≤ b.
--
-- We have a preorder with products and top element. Then we can do pointwise ∧ to compute the
-- common largest sequence.
--
-- (a0 , a1 , a2)
-- ∧
-- (a0 , ⊤ , ⊤)
--
-- (a0 ∧ a0 , a1 , a2)
--
-- For simple values we can make a meet lattice by saying:
-- A = V + 1
-- * : A -> A -> A
-- a * b = a = b ? => a else 0
-- 0 * b = 0
-- a * 0 = 0
--
-- a ≤ b if ∃ x. a * x = b
--
-- The thing is that the family F : A -> 𝕍 𝑖 has to preserve the subset structure
-- if I have (a ∧ b) ≤ a, then if I have (x : F a), I should get (x' : F (a ∧ b)).
--
-- An open set is an external choice of response.

-}
