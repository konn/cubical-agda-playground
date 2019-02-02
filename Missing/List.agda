{-# OPTIONS --safe --cubical #-}
module Missing.List where
open import Agda.Builtin.List public
  using (List; []; _∷_)
open import Cubical.Data.Bool
open import Cubical.Data.Prod
open import Agda.Builtin.Sigma
open import Cubical.Data.Nat
open import Missing.Function
open import Missing.EqReasoning
open import Cubical.Core.Everything
open import Missing.Bool

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

module _ {a} {A : Set a} where

  infixr 5 _++_

  _++_ : List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

------------------------------------------------------------------------
-- Operations for reducing lists

foldr : ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

foldl : ∀ {a b} {A : Set a} {B : Set b} → (A → B → A) → A → List B → A
foldl c n []       = n
foldl c n (x ∷ xs) = foldl c (c n x) xs

concat : ∀ {a} {A : Set a} → List (List A) → List A
concat = foldr _++_ []

concatMap : ∀ {a b} {A : Set a} {B : Set b} →
            (A → List B) → List A → List B
concatMap f = concat ∘ map f

null : ∀ {a} {A : Set a} → List A → Bool
null []       = true
null (x ∷ xs) = false

sum : List ℕ → ℕ
sum = foldr _+_ 0

product : List ℕ → ℕ
product = foldr _*_ 1

length : ∀ {a} {A : Set a} → List A → ℕ
length = foldr (const suc) 0

------------------------------------------------------------------------
-- Operations for constructing lists

[_] : ∀ {a} {A : Set a} → A → List A
[ x ] = x ∷ []

replicate : ∀ {a} {A : Set a} → ℕ → A → List A
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

inits : ∀ {a} {A : Set a} → List A → List (List A)
inits []       = [] ∷ []
inits (x ∷ xs) = [] ∷ map (x ∷_) (inits xs)

tails : ∀ {a} {A : Set a} → List A → List (List A)
tails []       = [] ∷ []
tails (x ∷ xs) = (x ∷ xs) ∷ tails xs

-- Scans

scanr : ∀ {a b} {A : Set a} {B : Set b} →
        (A → B → B) → B → List A → List B
scanr f e []       = e ∷ []
scanr f e (x ∷ xs) with scanr f e xs
... | []     = []                -- dead branch
... | y ∷ ys = f x y ∷ y ∷ ys

scanl : ∀ {a b} {A : Set a} {B : Set b} →
        (A → B → A) → A → List B → List A
scanl f e []       = e ∷ []
scanl f e (x ∷ xs) = e ∷ scanl f (f e x) xs

module _ {a} {A : Set a} where

-- Tabulation

  applyUpTo : (ℕ → A) → ℕ → List A
  applyUpTo f zero    = []
  applyUpTo f (suc n) = f zero ∷ applyUpTo (f ∘ suc) n

  applyDownFrom : (ℕ → A) → ℕ → List A
  applyDownFrom f zero = []
  applyDownFrom f (suc n) = f n ∷ applyDownFrom f n

-- Numerical

upTo : ℕ → List ℕ
upTo = applyUpTo id

downFrom : ℕ → List ℕ
downFrom = applyDownFrom id

------------------------------------------------------------------------
-- Operations for deconstructing lists

-- Note that although these combinators can be useful for programming, when
-- proving it is often a better idea to manually destruct a list argument:
-- each branch of the pattern-matching will have a refined type.

take : ∀ {a} {A : Set a} → ℕ → List A → List A
take zero    xs       = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ∀ {a} {A : Set a} → ℕ → List A → List A
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n xs

splitAt : ∀ {a} {A : Set a} → ℕ → List A → (List A × List A)
splitAt zero    xs       = ([] , xs)
splitAt (suc n) []       = ([] , [])
splitAt (suc n) (x ∷ xs) with splitAt n xs
... | (ys , zs) = (x ∷ ys , zs)

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Operations for reversing lists

module _ {a} {A : Set a} where

  reverseAcc : List A → List A → List A
  reverseAcc = foldl (flip _∷_)

  reverse : List A → List A
  reverse = reverseAcc []

-- Snoc.

infixl 5 _∷ʳ_

_∷ʳ_ : ∀ {a} {A : Set a} → List A → A → List A
xs ∷ʳ x = xs ++ [ x ]

-- Backwards initialisation

infixl 5 _∷ʳ'_

data InitLast {a} {A : Set a} : List A → Set a where
  []    : InitLast []
  _∷ʳ'_ : (xs : List A) (x : A) → InitLast (xs ∷ʳ x)

initLast : ∀ {a} {A : Set a} → (xs : List A) → InitLast xs
initLast []               = []
initLast (x ∷ xs)         with initLast xs
initLast (x ∷ .[])        | []       = [] ∷ʳ' x
initLast (x ∷ .(ys ∷ʳ y)) | ys ∷ʳ' y = (x ∷ ys) ∷ʳ' y
