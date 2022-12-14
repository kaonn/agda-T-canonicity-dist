{-# OPTIONS --cumulativity #-}
-- Because we are loading LogicalRelation.agda which has unresolved goals, we have to 
-- use the following Pragma. Delete this when you complete LogicalRelation.agda 
{-# OPTIONS --allow-unsolved-metas #-}
module Canonicity where

open import T.Syntax
open import T.Signature
open Theory Ã
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


empty/ð¤ð¦ð/var : _â¡_ {A = â ~[ Îá´³ ]â â} (index {ð³ = Îá´³} â¢) ð§ðð£ 
empty/ð¤ð¦ð/var = funext (Î» c ())

empty/ð¤ð¦ð : â {Ï} {e : P Ï} â ð¤ð¦ð e (index {ð³ = Îá´³} â¢) â¡ e
empty/ð¤ð¦ð {e = e} = trans (cong (ð¤ð¦ð e) empty/ð¤ð¦ð/var) (ð¥ð£ðð§-Î·âid ðá´® id refl)

canonicity : (e : P N) â Î£ â Î» n â e â numeral n
canonicity e = {!   !} 

-- example
-- De Bruijn indices: 
-- xâ is the closest bound variable 
-- xâ is the second closes bound variable
-- warning: these are hard coded variables, but you can define your own
-- as x_i = var (old old .... old new) where there are i old's in x_i

plus : P (N â£ N â£ N)
plus = Æ (Æ (iter xâ xâ (su xâ)))

1+2 : P N 
1+2 = plus $ (su ze) $ (su (su ze))

-- the following should type check when you finish the proof of the ftlr
-- _ : projâ (canonicity 1+2) â¡ 3 
-- _ = refl