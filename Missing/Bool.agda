{-# OPTIONS --safe --cubical #-}
module Missing.Bool where
open import Cubical.Data.Bool public
open import Cubical.Data.Unit
open import Cubical.Data.Empty

infixr 6 _∧_
infixr 5 _∨_ _xor_
infix  0 if_then_else_

------------------------------------------------------------------------
-- The boolean type

open import Agda.Builtin.Bool public

------------------------------------------------------------------------
-- Some operations

-- A function mapping true to an inhabited type and false to an empty
-- type.

T : Bool → Set
T true  = Unit
T false = ⊥

if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false

_∨_ : Bool → Bool → Bool
true  ∨ b = true
false ∨ b = b

_xor_ : Bool → Bool → Bool
true  xor b = not b
false xor b = b
