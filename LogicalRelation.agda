{-# OPTIONS --cumulativity #-}
-- Because we are loading LogicalRelation.agda in Canonicity.agda which has unresolved goals, we have to 
-- use the following Pragma. Delete this when you complete LogicalRelation.agda 
{-# OPTIONS --allow-unsolved-metas #-}
module LogicalRelation where

open import Level

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Metatheory.Syntax

open import T.Syntax hiding (_▷_)
open import T.Signature

open import Assumptions 

open import OperationalSemantics

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 


private
  variable
    Γ Δ Π : Ctx
    σ τ ρ : ΛT

open import SubLemma T.Syntax.⅀F ⅀:Str Ø (𝕋:Init Ø)
open Theory Ø

module Candidate where

  record cand (τ : ΛT) : Set1 where 
    field 
      -- underlying set of the candidate
      set : Set
      -- logical relation
      _⊩_ : P τ → set → Set 
      -- closure under reverse execution
      ← : {e e' : P τ} {a : set} → e ↦* e' → e' ⊩ a → e ⊩ a
    infix 3 _⊩_

  open cand 

  ⟦_⟧ : cand τ → Set 
  ⟦ 𝔖 ⟧ = 𝔖 . set 

  _∣_⊩_ : (𝔖 : cand τ) → P τ → ⟦ 𝔖 ⟧ → Set  
  𝔖 ∣ e ⊩ a =  𝔖 ._⊩_ e a
  
  numeral : ℕ → P N 
  numeral ℕ.zero = ze
  numeral (suc n) = su (numeral n) 

  numeral/val : (n : ℕ) → val (numeral n)
  numeral/val ℕ.zero = ze/val
  numeral/val (ℕ.suc n) = su/val (numeral/val n)

  𝔑  : cand N 
  𝔑  . set = ℕ 
  𝔑  . _⊩_ = λ e n → e ⇓ numeral n 
  𝔑  . ←  = head/exp

  _⇒_ : cand σ → cand τ → cand (σ ↣ τ)
  𝔖 ⇒ 𝔗 = {!   !}

  𝔘 : cand 𝟙 
  𝔘 = {!   !}

  𝔈 : cand 𝟘 
  𝔈 = {!   !}

  _⊞_ : cand σ → cand τ → cand (σ ⊕ τ)
  _⊞_ = {!   !}

  _⊠_ : cand σ → cand τ → cand (σ ⊗ τ)
  _⊠_ = {!   !}

  
open Candidate hiding (⟦_⟧ ; _∣_⊩_)

module LR where 

  open cand

  -- assignment of candidate to types of T
  𝓕 : (τ : ΛT) → cand τ
  𝓕 N = 𝔑
  𝓕 (σ ↣ τ) = 𝓕 σ ⇒ 𝓕 τ
  𝓕 𝟙 = 𝔘
  𝓕 (σ ⊗ τ) = 𝓕 σ ⊠ 𝓕 τ
  𝓕 𝟘 = 𝔈
  𝓕 (σ ⊕ τ) = 𝓕 σ ⊞ 𝓕 τ

  ⟦_⟧ : ΛT → Set 
  ⟦ τ ⟧ = 𝓕 τ . set 

  _∣_⊩_ : (τ : ΛT) → P τ → ⟦ τ ⟧ → Set  
  τ ∣ e ⊩ a =  (𝓕 τ) ._⊩_ e a

  _∣_←_ : (τ : ΛT) → ∀ {e e' : P τ} {a : ⟦ τ ⟧} → (τ ∣ e' ⊩ a) → e ↦* e' → (τ ∣ e ⊩ a)
  τ ∣ e'⊩a ← e↦*e' = (𝓕 τ) .← e↦*e' e'⊩a

  cand/Ctx : Ctx → Set1
  cand/Ctx ∅ = ⊤
  cand/Ctx (τ ∙ Γ) = cand τ × cand/Ctx Γ

  open import SOAS.ContextMaps.Inductive {T = ΛT}
  open import SOAS.Coalgebraic.Lift {T = ΛT} using (lift₁)
  -- semantic closing substitutions
  ⟦_⟧₁ : Ctx → Set 
  ⟦ ∅ ⟧₁ = ⊤
  ⟦ τ ∙ Γ ⟧₁ =  ⟦ τ ⟧ × ⟦ Γ ⟧₁

  open import SOAS.ContextMaps.Combinators Λᴳ using (add)

  open import Level

  private
    add/index : (e : Λᴳ τ Δ) (𝕤 : Sub Λᴳ Γ Δ) → 
      _≡_ {a = 0ℓ} {A = (τ ∙ Γ) ~[ Λᴳ ]↝ Δ}
      (index {𝒳 = Λᴳ} {Γ = τ ∙ Γ} {Δ = Δ} (e ◂ 𝕤)) 
      (add {α = τ} {Δ = Δ} {Γ = Γ} e (index 𝕤))
    add/index e 𝕤 = funext (λ τ → λ { new → refl ; (old v) → refl })

  -- you may find the following lemma useful in the proof of the ftlr for elimination forms that involve binding
  𝕤𝕦𝕓[/]'' : (𝕤 : Sub Λᴳ Γ ∅) (e : Λᴳ τ (σ ∙ Γ)) (e1 : 𝕋 σ ∅)
      → [ e1 /] (𝕤𝕦𝕓 e (lift₁ 𝕋ᴮ (index 𝕤))) ≡ 𝕤𝕦𝕓 e (index (e1 ◂ 𝕤))
  𝕤𝕦𝕓[/]'' 𝕤 e e1 = sym (trans (cong (𝕤𝕦𝕓 e) (add/index e1 𝕤)) (𝕤𝕦𝕓[/]' (index 𝕤) e e1 ))

  data _∣_▷_ : (Γ : Ctx) → Sub Λᴳ Γ ∅ → ⟦ Γ ⟧₁ → Set where 
    -- "bullet" • code: \bub
    * : ∅ ∣ • ▷ tt
    -- "bullet operator" ∙ code: \.
    _::_ : ∀ {Γ} {𝕤} {γ} {τ} {e} {a} → τ ∣ e ⊩ a → Γ ∣ 𝕤 ▷ γ → (τ ∙ Γ) ∣ (e ◂ 𝕤) ▷ (a , γ)
 
  ftlr/var : (Γ : Ctx) → (τ : ΛT) → 
         (𝓋 : ℐ τ Γ) → 
         Σ (⟦ Γ ⟧₁ → ⟦ τ ⟧) λ f → 
          (𝕤 : Sub Λᴳ Γ ∅) → (γ : ⟦ Γ ⟧₁ ) → Γ ∣ 𝕤 ▷ γ → 
            τ ∣ (𝕤𝕦𝕓 (var 𝓋) (index 𝕤)) ⊩ f γ
  ftlr/var .(_ ∙ _) τ new = proj₁ ,  
    λ {(e ◂ 𝕤) (a , γ) (prf :: 𝕤▷γ) → 
     ≡subst (λ e → τ ∣ e ⊩ a) (sym (Substitution.𝕥⟨𝕧⟩ {σ = index (e ◂ 𝕤)} {x = new})) prf
    } 
  ftlr/var (_ ∙ Γ) τ (old x) = 
    let (f , prf') = ftlr/var Γ τ x in 
      f ∘ proj₂ , 
      λ { (e ◂ 𝕤) (a , γ) (prf :: 𝕤▷γ) → prf' 𝕤 γ 𝕤▷γ }
 
  ftlr : (Γ : Ctx) → (τ : ΛT) → 
         (e : Λᴳ τ Γ) → 
         Σ (⟦ Γ ⟧₁ → ⟦ τ ⟧) λ f → 
          (𝕤 : Sub Λᴳ Γ ∅) → (γ : ⟦ Γ ⟧₁ ) → Γ ∣ 𝕤 ▷ γ → 
            τ ∣ (𝕤𝕦𝕓 e (index 𝕤)) ⊩ f γ
  ftlr Γ τ (var 𝓋) = ftlr/var Γ τ 𝓋 
  ftlr Γ (σ ↣ τ) (ƛ e) = {!   !}
  ftlr Γ τ (_$_ {α = σ} {β = ρ} e e1) = {!   !}
  ftlr Γ τ (iter e e0 e1) = {!   !}
  ftlr Γ .𝟙 triv = {!   !}
  ftlr Γ τ (fst e) = {!   !}
  ftlr Γ τ (snd e) = {!   !}
  ftlr Γ τ (abort e) = {!   !}
  ftlr Γ .(_ ⊕ _) (inl e) = {!   !}
  ftlr Γ .(_ ⊕ _) (inr e) = {!   !}
  ftlr Γ τ (case {α = σ} {β = ρ} e e₁ e₂) = {!   !}
  ftlr Γ .N ze = {!   !}
  ftlr Γ .N (su e) = {!   !}
  ftlr Γ (σ ⊗ τ) ⟨ e1 , e2 ⟩ = {!   !}