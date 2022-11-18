open import SOAS.Common
open import SOAS.Families.Core
open import Categories.Object.Initial
open import SOAS.Coalgebraic.Strength
import SOAS.Metatheory.MetaAlgebra

module SubLemma {T : Set}
  (⅀F : Functor 𝔽amiliesₛ 𝔽amiliesₛ) (⅀:Str : Strength ⅀F)
  (𝔛 : Familyₛ) (open SOAS.Metatheory.MetaAlgebra ⅀F 𝔛)
  (𝕋:Init : Initial 𝕄etaAlgebras)
  where

open import SOAS.Metatheory.Substitution {T = T} ⅀F ⅀:Str 𝔛 𝕋:Init

open import SOAS.Context
open import SOAS.Variable
open import SOAS.Abstract.Hom
import SOAS.Abstract.Coalgebra as →□ ; open →□.Sorted
import SOAS.Abstract.Box as □ ; open □.Sorted

open import SOAS.Abstract.Monoid

open import SOAS.Coalgebraic.Map
open import SOAS.Coalgebraic.Monoid
open import SOAS.Coalgebraic.Lift

open import SOAS.Metatheory.Algebra ⅀F
open import SOAS.Metatheory.Semantics ⅀F ⅀:Str 𝔛 𝕋:Init
open import SOAS.Metatheory.Traversal ⅀F ⅀:Str 𝔛 𝕋:Init
open import SOAS.Metatheory.Renaming ⅀F ⅀:Str 𝔛 𝕋:Init
open import SOAS.Metatheory.Coalgebraic ⅀F ⅀:Str 𝔛 𝕋:Init

open Strength ⅀:Str

private
  variable
    Γ Δ : Ctx
    α β : T

open import SOAS.ContextMaps.Combinators

𝕤𝕦𝕓[/]' : (σ : Γ ~[ 𝕋 ]↝ ∅)(b : 𝕋 α (β ∙ Γ))(a : 𝕋 β ∅)
      → 𝕤𝕦𝕓 b (add 𝕋 a σ) ≡ [ a /] (𝕤𝕦𝕓 b (lift 𝕋ᴮ ⌈ β ⌋ σ))
𝕤𝕦𝕓[/]' {β = β} σ b a = sym (begin 
    [ a /] (𝕤𝕦𝕓 b (lift 𝕋ᴮ ⌈ β ⌋ σ)) ≡⟨ assoc ⟩  
    𝕤𝕦𝕓 b (λ v → 𝕤𝕦𝕓 (lift 𝕋ᴮ ⌈ β ⌋ σ v) (add 𝕋 a 𝕧𝕒𝕣)) ≡⟨ 
        cong (𝕤𝕦𝕓 b) (dext (λ{ new → lunit ; (old v) → 
        begin
            𝕤𝕦𝕓 (𝕣𝕖𝕟 (σ v) old) (add 𝕋 a 𝕧𝕒𝕣)
        ≡⟨ 𝕤𝕦𝕓ᶜ.f∘r ⟩
            𝕤𝕦𝕓 (σ v) (λ v → add 𝕋 a 𝕧𝕒𝕣 (old v))
        ≡⟨ cong (𝕤𝕦𝕓 (σ v)) (dext (λ y → refl)) ⟩
            𝕤𝕦𝕓 (σ v) 𝕧𝕒𝕣
        ≡⟨ runit ⟩
            σ v
        ∎ 
        })) ⟩  
    𝕤𝕦𝕓 b (add 𝕋 a σ)  
    ∎) where open ≡-Reasoning