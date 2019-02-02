{-# OPTIONS --safe --cubical #-}
module Missing.List.Properties where
open import Missing.List
open import Missing.Function
open import Missing.EqReasoning
open import Cubical.Core.Everything
import Missing.FunctionProperties as FP

module _ {a} {A : Set a} where
  open FP {A = List A}
  ++-assoc : Associative _++_
  ++-assoc []       ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

  ++-identityˡ : LeftIdentity [] _++_
  ++-identityˡ xs = refl

  ++-identityʳ : RightIdentity [] _++_
  ++-identityʳ []       = refl
  ++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

  ++-identity : Identity [] _++_
  ++-identity = ++-identityˡ , ++-identityʳ

  unfold-reverse : ∀ (x : A) xs → reverse (x ∷ xs) ≡ reverse xs ∷ʳ x
  unfold-reverse x xs = helper [ x ] xs
    where
    helper : (xs ys : List A) → foldl (flip _∷_) xs ys ≡ reverse ys ++ xs
    helper xs []       = refl
    helper xs (y ∷ ys) =
      foldl (flip _∷_) (y ∷ xs) ys  ≡⟨ helper (y ∷ xs) ys ⟩
      reverse ys ++ y ∷ xs          ≡⟨ sym (++-assoc (reverse ys) _ _) ⟩
      (reverse ys ∷ʳ y) ++ xs       ≡⟨ sym $ cong (_++ xs) (unfold-reverse y ys) ⟩
      reverse (y ∷ ys) ++ xs        ∎


  reverse-++-commute : (xs ys : List A) →
                       reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
  reverse-++-commute []       ys = sym (++-identityʳ _)
  reverse-++-commute (x ∷ xs) ys =
    reverse (x ∷ xs ++ ys)               ≡⟨ unfold-reverse x (xs ++ ys) ⟩
    reverse (xs ++ ys) ++ [ x ]          ≡⟨ cong (_++ [ x ]) (reverse-++-commute xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]  ≡⟨ ++-assoc (reverse ys) _ _ ⟩
    reverse ys ++ (reverse xs ++ [ x ])  ≡⟨ sym $ cong (reverse ys ++_) (unfold-reverse x xs) ⟩
    reverse ys ++ reverse (x ∷ xs)       ∎

  reverse-involutive : Involutive reverse
  reverse-involutive [] = refl
  reverse-involutive (x ∷ xs) =
    reverse (reverse (x ∷ xs))   ≡⟨ cong reverse $ unfold-reverse x xs ⟩
    reverse (reverse xs ∷ʳ x)    ≡⟨ reverse-++-commute (reverse xs) ([ x ]) ⟩
    x ∷ reverse (reverse (xs))   ≡⟨ cong (x ∷_) $ reverse-involutive xs ⟩
    x ∷ xs                       ∎


  module _ {b} {B : Set b} where
    map-++-commute : ∀ (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
    map-++-commute f []       ys = refl
    map-++-commute f (x ∷ xs) ys =
        map f (x ∷ xs ++ ys)
      ≡⟨⟩
        f x ∷ map f (xs ++ ys)
      ≡⟨ cong (f x ∷_) (map-++-commute f xs ys) ⟩
        f x ∷ (map f xs ++ map f ys)
      ≡⟨⟩
        (f x ∷ map f xs) ++ map f ys
      ≡⟨⟩
        map f (x ∷ xs) ++ map f ys
      ∎

