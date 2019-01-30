{-# OPTIONS --cubical --safe #-}
module Deq where
import Level renaming (suc to sucL)
open import Cubical.Core.Everything
open import Cubical.Core.Id using (pathId)
import Cubical.Core.Id as Id
open import Cubical.Core.HoTT-UF using (transport)
open import Data.List
      using   (List)
import Data.List as L
import Data.List.Properties as L
import Agda.Builtin.Equality as BE
import Relation.Binary.PropositionalEquality as BE
open import Function
open import Algebra.FunctionProperties

data Deq {𝓁} (A : Set 𝓁) : Set 𝓁 where
  mkQ    : List A → List A → Deq A

  rotate : (a : A) (l r : List A) → mkQ (l L.∷ʳ a) r ≡ mkQ l (r L.∷ʳ a)
pattern [] = mkQ L.[] L.[]

infixr 2 _≡⟨⟩_
_≡⟨⟩_ : ∀{𝓁} {A : Set 𝓁} (x : A) {y : A} → x ≡ y → x ≡ y
_ ≡⟨⟩ e = e

module _ {𝓁} {A : Set 𝓁} where
  infixr 5 _∷_
  _∷_ : A → Deq A → Deq A
  x ∷ mkQ l r = mkQ (x L.∷ l) r
  x ∷ rotate a l r i = rotate a (x L.∷ l) r i

  infixl 5 _∷ʳ_
  _∷ʳ_ : Deq A → A → Deq A
  mkQ l r        ∷ʳ x = mkQ l (x L.∷ r)
  rotate a l r i ∷ʳ x = rotate a l (x L.∷ r) i

  reverse : Deq A → Deq A
  reverse (mkQ l r) = mkQ r l
  reverse (rotate a l r i) = rotate a r l (~ i)

  toId : ∀{ℓ′} {B : Set ℓ′} {a b : B} → a BE.≡ b → a Id.≡ b
  toId BE.refl = Id.refl

  toPath : ∀{ℓ′} {B : Set ℓ′} {a b : B} → a BE.≡ b → a ≡ b
  toPath BE.refl = refl

  map : ∀ {𝓁′} {B : Set 𝓁′} → (A → B) → Deq A → Deq B
  map f (mkQ l r) = mkQ (L.map f l) (L.map f r)
  map  {_} {B} f (rotate a l r i) = 
    let pf =  mkQ (L.map f (l L.∷ʳ a)) (L.map f r)
            ≡⟨ cong
                (λ xs → mkQ xs $ L.map f r) $
                toPath $ L.map-++-commute f l L.[ a ]
             ⟩ 
              mkQ (L.map f l L.∷ʳ f a) (L.map f r)
            ≡⟨ rotate (f a) (L.map f l) (L.map f r) ⟩
              mkQ (L.map f l) (L.map f r  L.∷ʳ f a)
            ≡⟨ cong
                (λ ys → mkQ (L.map f l) ys) $
                sym $ toPath $ L.map-++-commute f r L.[ a ]
              ⟩
              mkQ (L.map f l) (L.map f (r L.∷ʳ a))
            ∎
    in pf i

  module _ where
    aux-app-rev : ∀ (a : A) (l r : List A)
                → l L.++ L.reverse (r L.∷ʳ a) ≡ (l L.∷ʳ a) L.++ L.reverse r
    aux-app-rev a l r = 
        l L.++ L.reverse (r L.∷ʳ a)
      ≡⟨ cong (l L.++_) $ toPath $ L.reverse-++-commute r _ ⟩
        l L.++ (L.[ a ] L.++ L.reverse r)
      ≡⟨ sym $ toPath $ L.++-assoc l _ _ ⟩
        (l L.∷ʳ a) L.++ L.reverse r
      ∎

    aux-que-app-rev : ∀ (l m r : List A) → mkQ (l L.++ m) r ≡ mkQ l (r L.++ L.reverse m)
    aux-que-app-rev l L.[] r =
        mkQ (l L.++ L.[]) r
      ≡⟨ cong (λ x → mkQ x r) (toPath $ L.++-identityʳ l) ⟩
        mkQ l r
      ≡⟨ cong (mkQ l) (sym $ toPath $ L.++-identityʳ r) ⟩
        mkQ l (r L.++ L.[])
      ≡⟨⟩
        mkQ l (r L.++ L.reverse L.[])
      ∎
    aux-que-app-rev l (x L.∷ xs) r =
        mkQ (l L.++ (x L.∷ xs)) r
      ≡⟨⟩
        mkQ (l L.++ (L.[ x ] L.++ xs)) r
      ≡⟨ cong (λ l → mkQ l r) $ sym $ toPath $
          L.++-assoc l L.[ x ] xs
       ⟩
        mkQ ((l L.∷ʳ x) L.++ xs) r
      ≡⟨ aux-que-app-rev (l L.∷ʳ x) xs r ⟩
        mkQ (l L.∷ʳ x) (r L.++ L.reverse xs)
      ≡⟨ rotate x l (r L.++ L.reverse xs) ⟩
        mkQ l ((r L.++ L.reverse xs) L.∷ʳ x)
      ≡⟨ cong (mkQ l) $ toPath $
          L.++-assoc r (L.reverse xs) L.[ x ]
       ⟩
        mkQ l (r L.++ (L.reverse xs L.∷ʳ x))
      ≡⟨ cong (λ zs → mkQ l (r L.++ zs)) $ sym $ toPath $
          L.unfold-reverse x xs
       ⟩
        mkQ l (r L.++ L.reverse (x L.∷ xs))
      ∎

  infixr 5 _++_
  _++_ : Deq A → Deq A → Deq A
  mkQ l₀ r₀        ++ mkQ l₁ r₁      = mkQ (l₀ L.++ L.reverse r₀) (r₁ L.++ L.reverse l₁)
  mkQ l₀ r₀        ++ rotate a l₁ r₁ i =
    mkQ (l₀ L.++ L.reverse r₀) (aux-app-rev a r₁ l₁ i)
  rotate a l₀ r₀ i ++ mkQ l₁ r₁ =
    mkQ (aux-app-rev a  l₀ r₀ (~ i)) (r₁ L.++ L.reverse l₁)
  rotate a₀ l₀ r₀ i ++ rotate a₁ l₁ r₁ j =
    mkQ (aux-app-rev a₀ l₀ r₀ (~ i)) (aux-app-rev a₁ r₁ l₁ j)

  module Properties where
    ++-identityʳ : RightIdentity {A = Deq A} _≡_ [] _++_
    ++-identityʳ (mkQ l r) =
        mkQ l r ++ []
      ≡⟨⟩
        mkQ (l L.++ L.reverse r) (L.[] L.++ L.reverse L.[])
      ≡⟨⟩
        mkQ (l L.++ L.reverse r) L.[]
      ≡⟨ aux-que-app-rev l (L.reverse r) L.[] ⟩
        mkQ l (L.[] L.++ L.reverse (L.reverse r))
      ≡⟨⟩
        mkQ l (L.reverse (L.reverse r))
      ≡⟨ cong (mkQ l) $ toPath $ L.reverse-involutive r ⟩
        mkQ l r
      ∎
    ++-identityʳ (rotate a l r i) = ?
    
    ++-identityˡ : LeftIdentity {A = Deq A} _≡_ [] _++_
    ++-identityˡ (mkQ l r) =
        [] ++ mkQ l r
      ≡⟨⟩
        mkQ L.[] (r L.++ L.reverse l)
      ≡⟨ sym $ aux-que-app-rev L.[] l r ⟩
        mkQ l r
      ∎

    ++-assoc : Associative {A = Deq A} _≡_ _++_
    ++-assoc (mkQ l₁ r₁) (mkQ l₂ r₂) (mkQ l₃ r₃) = 
        (mkQ l₁ r₁ ++ mkQ l₂ r₂) ++ mkQ l₃ r₃
      ≡⟨⟩
        mkQ (l₁ L.++ L.reverse r₁) (r₂ L.++ L.reverse l₂) ++ mkQ l₃ r₃
      ≡⟨⟩
        mkQ ((l₁ L.++ L.reverse r₁) L.++ L.reverse (r₂ L.++ L.reverse l₂)) (r₃ L.++ L.reverse l₃)
      ≡⟨ cong (λ targ → mkQ ((l₁ L.++ L.reverse r₁) L.++ targ) (r₃ L.++ L.reverse l₃)) $
            L.reverse (r₂ L.++ L.reverse l₂)
          ≡⟨ toPath $ L.reverse-++-commute r₂ _ ⟩
            L.reverse (L.reverse l₂) L.++ L.reverse r₂
          ≡⟨ cong (L._++ L.reverse r₂) $ toPath $
              L.reverse-involutive l₂
           ⟩
            l₂ L.++ L.reverse r₂
          ∎
       ⟩
        mkQ ((l₁ L.++ L.reverse r₁) L.++ (l₂ L.++ L.reverse r₂)) (r₃ L.++ L.reverse l₃)
      ≡⟨ aux-que-app-rev (l₁ L.++ L.reverse r₁) _ (r₃ L.++ L.reverse l₃) ⟩
        mkQ (l₁ L.++ L.reverse r₁) ((r₃ L.++ L.reverse l₃) L.++ L.reverse (l₂ L.++ L.reverse r₂))
      ≡⟨⟩
        mkQ l₁ r₁ ++ mkQ (l₂ L.++ L.reverse r₂) (r₃ L.++ L.reverse l₃)
      ≡⟨⟩
        mkQ l₁ r₁ ++ (mkQ l₂ r₂ ++ mkQ l₃ r₃)
      ∎
    
     