{-# OPTIONS --cumulativity #-}
-- Because we are loading LogicalRelation.agda which has unresolved goals, we have to 
-- use the following Pragma. Delete this when you complete LogicalRelation.agda 
{-# OPTIONS --allow-unsolved-metas #-}
module Canonicity where

open import T.Syntax
open import T.Signature
open Theory Ø
open import SOAS.Common
open import SOAS.Variable
open import SOAS.Context
open import SOAS.ContextMaps.Inductive

open import Assumptions
open import OperationalSemantics
open import LogicalRelation

open import Data.Product
open import Data.Unit 
open import Data.Nat hiding (_*_)
open import Relation.Binary.PropositionalEquality

open Candidate
open LR


empty/𝕤𝕦𝕓/var : _≡_ {A = ∅ ~[ Λᴳ ]↝ ∅} (index {𝒳 = Λᴳ} •) 𝕧𝕒𝕣 
empty/𝕤𝕦𝕓/var = funext (λ c ())

empty/𝕤𝕦𝕓 : ∀ {τ} {e : P τ} → 𝕤𝕦𝕓 e (index {𝒳 = Λᴳ} •) ≡ e
empty/𝕤𝕦𝕓 {e = e} = trans (cong (𝕤𝕦𝕓 e) empty/𝕤𝕦𝕓/var) (𝕥𝕣𝕒𝕧-η≈id 𝕋ᴮ id refl)

canonicity : (e : P N) → Σ ℕ λ n → e ⇓ numeral n
canonicity e = {!   !} 

-- example
-- De Bruijn indices: 
-- x₀ is the closest bound variable 
-- x₁ is the second closes bound variable
-- warning: these are hard coded variables, but you can define your own
-- as x_i = var (old old .... old new) where there are i old's in x_i

plus : P (N ↣ N ↣ N)
plus = ƛ (ƛ (iter x₁ x₀ (su x₀)))

1+2 : P N 
1+2 = plus $ (su ze) $ (su (su ze))

-- the following should type check when you finish the proof of the ftlr
-- _ : proj₁ (canonicity 1+2) ≡ 3 
-- _ = refl