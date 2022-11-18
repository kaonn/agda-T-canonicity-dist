module OperationalSemantics where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core

open import T.Syntax hiding (_▷_)
open import T.Signature

open import Relation.Binary.Construct.Closure.ReflexiveTransitive 


private
  variable
    Γ Δ Π : Ctx
    σ τ ρ : ΛT

Λᴳ : Familyₛ
Λᴳ = Λ Ø

P : ΛT → Set 
P σ = Λᴳ σ ∅ 

open Theory Ø

data val : Λᴳ σ ∅ → Set where
  lam/val  : {b : Λᴳ τ (σ ∙ ∅)} → val (ƛ b)
  triv/val : val triv
  pair/val : {e1 : Λᴳ σ ∅} {e2 : Λᴳ τ ∅} → val ⟨ e1 , e2 ⟩
  inl/val : {τ : ΛT} {e : Λᴳ σ ∅} → val (inl {β = τ} e)
  inr/val : {σ : ΛT} {e : Λᴳ τ ∅} → val (inr {α = σ} e)
  ze/val : val ze
  su/val : {e : Λᴳ N ∅} → val e → val (su e)

data _↦_ : P σ → P σ → Set where
  ap/c : {e e' : P (σ ↣ τ) } {e2 : P σ} → e ↦ e' → e $ e2 ↦ e' $ e2
  ap/τ : {e : Λᴳ τ (σ ∙ ∅)} {e2 : P σ} → ((ƛ e) $ e2) ↦ [ e2 /] e 
  fst/c : {e e' : P (σ ⊗ τ)} → e ↦ e' → fst e ↦ fst e' 
  fst/τ : {e1 : P σ} {e2 : P τ} → fst ⟨ e1 , e2 ⟩ ↦ e1
  snd/c : {e e' : P (σ ⊗ τ)} → e ↦ e' → snd e ↦ snd e' 
  snd/τ : {e1 : P σ} {e2 : P τ} → snd ⟨ e1 , e2 ⟩ ↦ e2
  case/c : {e e' : P (σ ⊕ τ)} {e1 : Λᴳ ρ (σ ∙ ∅)} {e2 : Λᴳ ρ (τ ∙ ∅)} → e ↦ e' → case e e1 e2 ↦ case e' e1 e2
  case/inl : {e : P σ} {e1 : Λᴳ ρ (σ ∙ ∅)} {e2 : Λᴳ ρ (τ ∙ ∅)} → case (inl e) e1 e2 ↦ [ e /] e1
  case/inr : {e : P τ} {e1 : Λᴳ ρ (σ ∙ ∅)} {e2 : Λᴳ ρ (τ ∙ ∅)} → case (inr e) e1 e2 ↦ [ e /] e2
  rec/c : {e e' : P N} {e0 : P σ} {e1 : Λᴳ σ (σ ∙ ∅)} → e ↦ e' → iter e e0 e1 ↦ iter e' e0 e1 
  rec/z : {e0 : P σ} {e1 : Λᴳ σ (σ ∙ ∅)} → iter ze e0 e1 ↦ e0 
  rec/s : {e : P N} {e0 : P σ} {e1 : Λᴳ σ (σ ∙ ∅)} → val (su e) → iter (su e) e0 e1 ↦ [ iter e e0 e1 /] e1
  su/c : {e e' : P N} → e ↦ e' → su e ↦ su e' 

infix 2 _↦_

_↦*_ : P σ → P σ → Set 
e ↦* v = Star _↦_ e v

_⇓_ : P σ → P σ → Set
e ⇓ v = e ↦* v × val v

eval/val : {v : P τ} → val v → v ⇓ v 
eval/val valv = ε , valv

-- evaluation is closed under reverse execution 

head/exp : {e e' : P τ} {v : P τ} → e ↦* e' → e' ⇓ v → e ⇓ v 
head/exp ↦*/prf ⇓/prf = ( ↦*/prf ◅◅ ⇓/prf . proj₁ , ⇓/prf . proj₂ )

-- compatibility

rec/compat : ∀ {τ} {e} {e'} {e0 : P τ} {e1} → e ↦* e' → iter e e0 e1 ↦* iter e' e0 e1 
rec/compat ε = ε
rec/compat (x ◅ e↦*e') = rec/c x ◅ rec/compat e↦*e'

case/compat : ∀ {e e' : P (σ ⊕ τ)} {e1 : Λᴳ ρ (σ ∙ ∅)} {e2 : Λᴳ ρ (τ ∙ ∅)} → 
  e ↦* e' → case e e1 e2 ↦* case e' e1 e2 
case/compat ε = ε
case/compat (x ◅ e↦*e') = case/c x ◅ case/compat e↦*e'

ap/compat : {e e' : P (σ ↣ τ) } {e2 : P σ} → e ↦* e' → (e $ e2) ↦* (e' $ e2)
ap/compat ε = ε
ap/compat (x ◅ e↦*e') = ap/c x ◅ ap/compat e↦*e' 

fst/compat : {e e' : P (σ ⊗ τ)} → e ↦* e' → fst e ↦* fst e' 
fst/compat ε = ε
fst/compat (x ◅ e↦*e') = fst/c x ◅ fst/compat e↦*e' 

snd/compat : {e e' : P (σ ⊗ τ)} → e ↦* e' → snd e ↦* snd e' 
snd/compat ε = ε
snd/compat (x ◅ e↦*e') = snd/c x ◅ snd/compat e↦*e' 

su/compat : {e e' : P N} → e ↦* e' → su e ↦* su e' 
su/compat ε = ε
su/compat (x ◅ e↦*e') = su/c x ◅ su/compat e↦*e' 