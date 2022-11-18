{-
This second-order equational theory was created from the following second-order syntax description:

syntax TLC | Λ

type
  N   : 0-ary
  _↣_ : 2-ary | r30
  𝟙   : 0-ary
  _⊗_ : 2-ary | l40
  𝟘   : 0-ary
  _⊕_ : 2-ary | l30

term
  app   : α ↣ β  α  ->  β | _$_ l20
  lam   : α.β  ->  α ↣ β | ƛ_ r10
  triv  : 𝟙
  pair  : α  β  ->  α ⊗ β | ⟨_,_⟩ 
  fst   : α ⊗ β  ->  α
  snd   : α ⊗ β  ->  β
  abort : 𝟘  ->  α
  inl   : α  ->  α ⊕ β
  inr   : β  ->  α ⊕ β
  case  : α ⊕ β  α.γ  β.γ  ->  γ
  ze    : N
  su    : N  ->  N
  iter  : N  α  α.α  ->  α

theory
  (ƛβ) b : α.β  a : α |> app (lam(x.b[x]), a) = b[a]
  (ƛη) f : α ↣ β      |> lam (x. app(f, x))   = f
  (𝟙η) u : 𝟙 |> u = triv
  (fβ) a : α  b : β |> fst (pair(a, b))      = a
  (sβ) a : α  b : β |> snd (pair(a, b))      = b
  (pη) p : α ⊗ β    |> pair (fst(p), snd(p)) = p
  (𝟘η) e : 𝟘  c : α |> abort(e) = c
  (lβ) a : α   f : α.γ  g : β.γ |> case (inl(a), x.f[x], y.g[y])      = f[a]
  (rβ) b : β   f : α.γ  g : β.γ |> case (inr(b), x.f[x], y.g[y])      = g[b]
  (cη) s : α ⊕ β  c : (α ⊕ β).γ |> case (s, x.c[inl(x)], y.c[inr(y)]) = c[s]
  (zeβ) z : α   s : (α).α        |> iter (ze,     z, r. s[r]) = z
  (suβ) z : α   s : (α).α  n : N |> iter (su (n), z, r. s[r]) = s[iter (n, z, r. s[r]), n]
  (ift) t f : α |> if (true,  t, f) = t
  (iff) t f : α |> if (false, t, f) = f
-}

module T.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import T.Signature
open import T.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution Λ:Syn
open import SOAS.Metatheory.SecondOrder.Equality Λ:Syn

private
  variable
    α β γ τ : ΛT
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ Λ) α Γ → (𝔐 ▷ Λ) α Γ → Set where
  ƛβ  : ⁅ α ⊩ β ⁆ ⁅ α ⁆̣           ▹ ∅ ⊢                    (ƛ 𝔞⟨ x₀ ⟩) $ 𝔟 ≋ₐ 𝔞⟨ 𝔟 ⟩
  ƛη  : ⁅ α ↣ β ⁆̣                 ▹ ∅ ⊢                         ƛ (𝔞 $ x₀) ≋ₐ 𝔞
  𝟙η  : ⁅ 𝟙 ⁆̣                     ▹ ∅ ⊢                                  𝔞 ≋ₐ triv
  fβ  : ⁅ α ⁆ ⁅ β ⁆̣               ▹ ∅ ⊢                    fst (⟨ 𝔞 , 𝔟 ⟩) ≋ₐ 𝔞
  sβ  : ⁅ α ⁆ ⁅ β ⁆̣               ▹ ∅ ⊢                    snd (⟨ 𝔞 , 𝔟 ⟩) ≋ₐ 𝔟
  pη  : ⁅ α ⊗ β ⁆̣                 ▹ ∅ ⊢              ⟨ (fst 𝔞) , (snd 𝔞) ⟩ ≋ₐ 𝔞
  𝟘η  : ⁅ 𝟘 ⁆ ⁅ α ⁆̣               ▹ ∅ ⊢                            abort 𝔞 ≋ₐ 𝔟
  lβ  : ⁅ α ⁆ ⁅ α ⊩ γ ⁆ ⁅ β ⊩ γ ⁆̣ ▹ ∅ ⊢   case (inl 𝔞) (𝔟⟨ x₀ ⟩) (𝔠⟨ x₀ ⟩) ≋ₐ 𝔟⟨ 𝔞 ⟩
  rβ  : ⁅ β ⁆ ⁅ α ⊩ γ ⁆ ⁅ β ⊩ γ ⁆̣ ▹ ∅ ⊢   case (inr 𝔞) (𝔟⟨ x₀ ⟩) (𝔠⟨ x₀ ⟩) ≋ₐ 𝔠⟨ 𝔞 ⟩
  cη  : ⁅ α ⊕ β ⁆ ⁅ (α ⊕ β) ⊩ γ ⁆̣ ▹ ∅ ⊢ case 𝔞 (𝔟⟨ inl x₀ ⟩) (𝔟⟨ inr x₀ ⟩) ≋ₐ 𝔟⟨ 𝔞 ⟩
  zeβ : ⁅ α ⁆ ⁅ α ⊩ α ⁆̣           ▹ ∅ ⊢                iter ze 𝔞 (𝔟⟨ x₀ ⟩) ≋ₐ 𝔞
  suβ : ⁅ α ⁆ ⁅ α ⊩ α ⁆ ⁅ N ⁆̣     ▹ ∅ ⊢            iter (su 𝔠) 𝔞 (𝔟⟨ x₀ ⟩) ≋ₐ 𝔟⟨ (iter 𝔠 𝔞 (𝔟⟨ x₀ ⟩)) ⟩

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning

-- Derived equations
ift : ⁅ α ⁆ ⁅ α ⁆̣ ▹ ∅ ⊢ if true 𝔞 𝔟 ≋ 𝔞
ift = ax lβ with《 triv ◃ 𝔞 ◃ 𝔟 》
iff : ⁅ α ⁆ ⁅ α ⁆̣ ▹ ∅ ⊢ if false 𝔞 𝔟 ≋ 𝔟
iff = ax rβ with《 triv ◃ 𝔞 ◃ 𝔟 》

-- Double beta reduction
ƛβ² : ⁅ β · α ⊩ γ ⁆ ⁅ α ⁆ ⁅ β ⁆̣ ▹ ∅ ⊢ (ƛ (ƛ 𝔞⟨ x₀ ◂ x₁ ⟩)) $ 𝔟 $ 𝔠 ≋ 𝔞⟨ 𝔠 ◂ 𝔟 ⟩
ƛβ² = begin
      (ƛ (ƛ 𝔞⟨ x₀ ◂ x₁ ⟩)) $ 𝔟 $ 𝔠
  ≋⟨ cong[ ax ƛβ with《 (ƛ 𝔞⟨ x₀ ◂ x₁ ⟩) ◃ 𝔟 》 ]inside ◌ᵈ $ 𝔠 ⟩
      (ƛ 𝔞⟨ x₀ ◂ 𝔟 ⟩) $ 𝔠
  ≋⟨ ax ƛβ with《 (𝔞⟨ x₀ ◂ 𝔟 ⟩) ◃ 𝔠 》 ⟩
      𝔞⟨ 𝔠 ◂ 𝔟 ⟩
  ∎