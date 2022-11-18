open import Relation.Binary.PropositionalEquality
open import Level

-- We assume function extensionality
module Assumptions where

  private
    variable
        ℓ ℓ′ ℓ″ : Level

  postulate
    funext : ∀ {C : Set ℓ″} {A : C → Set ℓ} {B : C → Set ℓ′} {f g : {c : C} → A c → B c} (h : ∀ c x → f {c} x ≡ g {c} x) → _≡_ {A =  {c : C} → A c → B c} f g
