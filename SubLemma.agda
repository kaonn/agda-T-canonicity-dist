open import SOAS.Common
open import SOAS.Families.Core
open import Categories.Object.Initial
open import SOAS.Coalgebraic.Strength
import SOAS.Metatheory.MetaAlgebra

module SubLemma {T : Set}
  (โF : Functor ๐ฝamiliesโ ๐ฝamiliesโ) (โ:Str : Strength โF)
  (๐ : Familyโ) (open SOAS.Metatheory.MetaAlgebra โF ๐)
  (๐:Init : Initial ๐etaAlgebras)
  where

open import SOAS.Metatheory.Substitution {T = T} โF โ:Str ๐ ๐:Init

open import SOAS.Context
open import SOAS.Variable
open import SOAS.Abstract.Hom
import SOAS.Abstract.Coalgebra as โโก ; open โโก.Sorted
import SOAS.Abstract.Box as โก ; open โก.Sorted

open import SOAS.Abstract.Monoid

open import SOAS.Coalgebraic.Map
open import SOAS.Coalgebraic.Monoid
open import SOAS.Coalgebraic.Lift

open import SOAS.Metatheory.Algebra โF
open import SOAS.Metatheory.Semantics โF โ:Str ๐ ๐:Init
open import SOAS.Metatheory.Traversal โF โ:Str ๐ ๐:Init
open import SOAS.Metatheory.Renaming โF โ:Str ๐ ๐:Init
open import SOAS.Metatheory.Coalgebraic โF โ:Str ๐ ๐:Init

open Strength โ:Str

private
  variable
    ฮ ฮ : Ctx
    ฮฑ ฮฒ : T

open import SOAS.ContextMaps.Combinators

๐ค๐ฆ๐[/]' : (ฯ : ฮ ~[ ๐ ]โ โ)(b : ๐ ฮฑ (ฮฒ โ ฮ))(a : ๐ ฮฒ โ)
      โ ๐ค๐ฆ๐ b (add ๐ a ฯ) โก [ a /] (๐ค๐ฆ๐ b (lift ๐แดฎ โ ฮฒ โ ฯ))
๐ค๐ฆ๐[/]' {ฮฒ = ฮฒ} ฯ b a = sym (begin 
    [ a /] (๐ค๐ฆ๐ b (lift ๐แดฎ โ ฮฒ โ ฯ)) โกโจ assoc โฉ  
    ๐ค๐ฆ๐ b (ฮป v โ ๐ค๐ฆ๐ (lift ๐แดฎ โ ฮฒ โ ฯ v) (add ๐ a ๐ง๐๐ฃ)) โกโจ 
        cong (๐ค๐ฆ๐ b) (dext (ฮป{ new โ lunit ; (old v) โ 
        begin
            ๐ค๐ฆ๐ (๐ฃ๐๐ (ฯ v) old) (add ๐ a ๐ง๐๐ฃ)
        โกโจ ๐ค๐ฆ๐แถ.fโr โฉ
            ๐ค๐ฆ๐ (ฯ v) (ฮป v โ add ๐ a ๐ง๐๐ฃ (old v))
        โกโจ cong (๐ค๐ฆ๐ (ฯ v)) (dext (ฮป y โ refl)) โฉ
            ๐ค๐ฆ๐ (ฯ v) ๐ง๐๐ฃ
        โกโจ runit โฉ
            ฯ v
        โ 
        })) โฉ  
    ๐ค๐ฆ๐ b (add ๐ a ฯ)  
    โ) where open โก-Reasoning