{-# OPTIONS --cubical #-}
module Deq where
open import Cubical.Data.Prod
open import Cubical.Data.List
  renaming
    ( _++_ to _++L_ ; [] to []L ; [_] to [_]L
    ; rev to revL
    ; ++-unit-r to ++L-unit-r
    ; ++-assoc to ++L-assoc
    )
open import Cubical.Foundations.Prelude
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.SetQuotients
  renaming ( [_] to ⟦_⟧)
open import Cubical.Structures.Monoid

module _ where
  private
    variable
      𝓁 : Level
      A : Type 𝓁
      R : A → A → Type 𝓁

  recQ : {B : Type 𝓁}
        (Bset : isSet B)
        (f : A → B)
        (feq : (a b : A) (r : R a b) → f a ≡ f b)
      → A / R → B
  recQ Bset f feq ⟦ a ⟧ = f a
  recQ Bset f feq (eq/ a b r i) = feq a b r i
  recQ Bset f feq (squash/ x y p q i j) = Bset (g x) (g y) (cong g p) (cong g q) i j
    where
    g = recQ Bset f feq

  rec2 : {B : Type 𝓁} (Bset : isSet B)
       (f : A → A → B) (feql : (a b c : A) (r : R a b) → f a c ≡ f b c)
                       (feqr : (a b c : A) (r : R b c) → f a b ≡ f a c)
    → A / R → A / R → B
  rec2 Bset f feql feqr = recQ (isSetΠ (λ _ → Bset))
                            (λ a → recQ Bset (f a) (feqr a))
                            (λ a b r → funExt (elimProp (λ _ → Bset _ _)
                                              (λ c → feql a b c r)))

private
  variable
    𝓁 : Level
    A : Set 𝓁

data rotate-right (A : Type 𝓁) : (List A × List A) → (List A × List A) → Type 𝓁 where
  rot-right : (a : A) → (lh rh : List A) → rotate-right A (lh ∷ʳ a , rh) (lh , rh ∷ʳ a)

Queue : Type 𝓁 → Type 𝓁
Queue A = (List A × List A) / rotate-right A

mkQ : List A → List A → Queue A
mkQ l r = ⟦ l , r ⟧

[] : Queue A
[] = mkQ []L []L

Queue-is-Set : isSet (Queue A)
Queue-is-Set l r = squash/ l r

_◁_ : A → Queue A → Queue A
_◁_ x = recQ Queue-is-Set (λ { (lh , rh) → mkQ (x ∷ lh) rh }) 
  λ{ .((lh ∷ʳ a) , rh) .(lh , (rh ∷ʳ a)) (rot-right a lh rh) →
      mkQ (x ∷ (lh ∷ʳ a)) rh
    ≡⟨ eq/ _ _ (rot-right a (x ∷ lh) rh)  ⟩
      mkQ (x ∷ lh) (rh ∷ʳ a)
    ∎
    }

_▷_ : Queue A → A → Queue A
xs ▷ x = recQ Queue-is-Set (λ{ (lh , rh) → mkQ lh (x ∷ rh) }) 
      (λ { .((lh ∷ʳ a) , rh) .(lh , (rh ∷ʳ a)) (rot-right a lh rh) → 
            mkQ (lh ∷ʳ a) (x ∷ rh)
          ≡⟨ eq/ _ _ (rot-right a lh (x ∷ rh)) ⟩
            mkQ lh (x ∷ (rh ∷ʳ a))
          ∎
          }
      )
      xs

_++_ : Queue A → Queue A → Queue A 
_++_ = rec2 Queue-is-Set 
    (λ { (lh , mh) (mh′ , rh) → mkQ (lh ++L revL mh) (rh ++L revL mh′) } )
    (λ { (.(ls ∷ʳ a) , mls) (ls , .(mls ∷ʳ a)) (mrs′ , rs) (rot-right a .ls .mls) →
          cong (λ l → mkQ l (rs ++L revL mrs′))
          (   (ls ∷ʳ a) ++L revL mls
            ≡⟨ refl ⟩
              (ls ++L [ a ]L) ++L revL mls
            ≡⟨ ++L-assoc ls ([ a ]L) (revL mls) ⟩
              ls ++L ([ a ]L ++L revL mls)
            ≡⟨ refl ⟩
              ls ++L (a ∷ revL mls)
            ≡⟨ cong (ls ++L_) (sym (rev-++ mls [ a ]L)) ⟩
              ls ++L revL (mls ∷ʳ a)
            ∎
          )
      }
    )
    (λ { (ls , mls) (.(mrs ∷ʳ a) , rs) (mrs , .(rs ∷ʳ a)) (rot-right a .mrs .rs) →
          cong (mkQ (ls ++L revL mls))
          (   rs ++L revL (mrs ∷ʳ a) 
            ≡⟨ cong (rs ++L_) (rev-++ mrs [ a ]L) ⟩
              rs ++L (a ∷ revL mrs) 
            ≡⟨ sym (++L-assoc rs (a ∷ []L) (revL mrs)) ⟩ 
              (rs ∷ʳ a) ++L revL mrs
            ∎
          )
      }
    )

infixr 5 _++_ _◁_
infixl 5 _▷_

++-rot-rev-r : ∀ {xs ys zs : List A} → mkQ zs (ys ++L revL xs) ≡ mkQ (zs ++L xs) ys
++-rot-rev-r {xs = []L} {ys} {zs} = cong₂ mkQ (sym (++L-unit-r zs)) (++L-unit-r ys)
++-rot-rev-r {xs = x ∷ xs} {ys} {zs} =
    mkQ zs (ys ++L revL (x ∷ xs))
  ≡⟨ cong (λ ws → mkQ zs (ys ++L ws)) (rev-++ (x ∷ []L) xs) ⟩
    mkQ zs (ys ++L (revL xs ++L [ x ]L))
  ≡⟨ cong (mkQ zs) (sym (++L-assoc ys (revL xs) [ x ]L)) ⟩
    mkQ zs ((ys ++L revL xs) ∷ʳ x )
  ≡⟨ sym (eq/ _ _ (rot-right x zs (ys ++L revL xs))) ⟩
    mkQ (zs ∷ʳ x) (ys ++L revL xs)
  ≡⟨ ++-rot-rev-r ⟩
    mkQ ((zs ∷ʳ x) ++L xs) ys
  ≡⟨ cong (λ ws → mkQ ws ys) (++L-assoc zs (x ∷ []L) xs) ⟩
    mkQ (zs ++L x ∷ xs) ys
  ∎

++-rot-rev-l : ∀ {xs ys zs : List A} → mkQ (xs ++L revL ys) zs ≡ mkQ xs (zs ++L ys)
++-rot-rev-l {xs = xs} {[]L} {zs} = cong₂ mkQ (++L-unit-r xs) (sym (++L-unit-r zs))
++-rot-rev-l {xs = xs} {x ∷ ys} {zs} = 
    mkQ (xs ++L revL (x ∷ ys)) zs
  ≡⟨ cong (λ ws → mkQ (xs ++L ws) zs) (rev-++ (x ∷ []L) ys) ⟩
    mkQ (xs ++L (revL ys ∷ʳ x)) zs
  ≡⟨ cong (λ ws → mkQ ws zs) (sym (++L-assoc xs (revL ys) (x ∷ []L))) ⟩
    mkQ ((xs ++L revL ys) ∷ʳ x) zs
  ≡⟨ eq/ _ _ (rot-right x (xs ++L revL ys) zs) ⟩
    mkQ (xs ++L revL ys) (zs ∷ʳ x)
  ≡⟨ ++-rot-rev-l ⟩
    mkQ xs ((zs ∷ʳ x) ++L ys)
  ≡⟨ cong (mkQ xs) (++L-assoc zs (x ∷ []L) ys) ⟩
    mkQ xs (zs ++L x ∷ ys)
  ∎

++-unit-l : ∀ (x : Queue A) → [] ++ x ≡ x
++-unit-l = elimProp (λ x →  Queue-is-Set ([] ++ x) x) λ { 
    (lh , rh) → 
        [] ++ mkQ lh rh
      ≡⟨ refl ⟩
        mkQ []L (rh ++L revL lh)
      ≡⟨ ++-rot-rev-r ⟩ 
        mkQ lh rh
      ∎
  }

++-unit-r : ∀ (x : Queue A) → x ++ [] ≡ x
++-unit-r = elimProp (λ x →  Queue-is-Set (x ++ []) x) λ { 
    (lh , rh) → 
        mkQ lh rh ++ []
      ≡⟨ refl ⟩
        mkQ (lh ++L revL rh) []L
      ≡⟨ ++-rot-rev-l ⟩ 
        mkQ lh rh
      ∎
  }

++-assoc-aux : (ls₁ rs₁ ls₂ rs₂ ls₃ rs₃ : List A) → 
  mkQ ls₁ rs₁ ++ mkQ ls₂ rs₂ ++ mkQ ls₃ rs₃ ≡
    (mkQ ls₁ rs₁ ++ mkQ ls₂ rs₂) ++ mkQ ls₃ rs₃
++-assoc-aux ls₁ rs₁ ls₂ rs₂ ls₃ rs₃ =
    mkQ ls₁ rs₁ ++ (mkQ ls₂ rs₂ ++ mkQ ls₃ rs₃)
  ≡⟨ refl ⟩
    mkQ ls₁ rs₁ ++ (mkQ (ls₂ ++L revL rs₂) (rs₃ ++L revL ls₃))
  ≡⟨ refl ⟩
    mkQ (ls₁ ++L revL rs₁) ((rs₃ ++L revL ls₃) ++L revL (ls₂ ++L revL rs₂) )
  ≡⟨ ++-rot-rev-r ⟩
    mkQ ((ls₁ ++L revL rs₁) ++L (ls₂ ++L revL rs₂)) (rs₃ ++L revL ls₃)
  ≡⟨ cong (λ ws → mkQ ((ls₁ ++L revL rs₁) ++L ws) _) 
    (   ls₂ ++L revL rs₂
      ≡⟨ cong (_++L revL rs₂) (sym (rev-rev ls₂)) ⟩
        revL (revL ls₂) ++L revL rs₂
      ≡⟨ sym (rev-++ rs₂ (revL ls₂)) ⟩
        revL (rs₂ ++L revL ls₂) ∎
    )
  ⟩
    mkQ ((ls₁ ++L revL rs₁) ++L revL (rs₂ ++L revL ls₂)) (rs₃ ++L revL ls₃)
  ≡⟨ refl ⟩
    (mkQ (ls₁ ++L revL rs₁) (rs₂ ++L revL ls₂)) ++ mkQ ls₃ rs₃
  ≡⟨ refl ⟩
    (mkQ ls₁ rs₁ ++ mkQ ls₂ rs₂) ++ mkQ ls₃ rs₃
  ∎

++-assoc : (xs ys zs : Queue A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++-assoc = elimProp (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → Queue-is-Set _ _))) 
  λ { (ls₁ , rs₁) →  
    elimProp (λ _ → isPropΠ λ _ → Queue-is-Set _ _) 
      λ {(ls₂ , rs₂) → elimProp (λ _ → Queue-is-Set _ _) 
          (λ { (ls₃ , rs₃) → ++-assoc-aux ls₁ rs₁ ls₂ rs₂ ls₃ rs₃ }) }
  }

Queue-monoid-str : monoid-structure (Queue A)
Queue-monoid-str = ([] , _++_) , (Queue-is-Set , (++-assoc , (++-unit-r , ++-unit-l)))
