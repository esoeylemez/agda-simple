-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Data.Nat.Core where

open import Agda.Builtin.Nat public
  renaming (Nat to ℕ)
  using (suc; zero)
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Classes
open import Core


instance
  ℕ-Number : Number ℕ
  ℕ-Number =
    record {
      Constraint = λ _ → ⊤;
      fromNat = λ n → n
    }

  ℕ-Plus : Plus ℕ
  ℕ-Plus = record { _+_ = _+ℕ_ }

  ℕ-Times : Times ℕ
  ℕ-Times = record { _*_ = _*ℕ_ }

  ℕ,≡ : Equiv ℕ
  ℕ,≡ = PropEq ℕ

  module ℕ,≡ = Equiv ℕ,≡


data _≤_ : ℕ → ℕ → Set where
  instance 0≤s : ∀ {y} → 0 ≤ y
  instance s≤s : ∀ {x y} → x ≤ y → suc x ≤ suc y

infix 4 _≤_

ℕ,≤ : TotalOrder ℕ
ℕ,≤ =
  record {
    partialOrder = record {
      Eq = PropEq ℕ;
      _≤_ = _≤_;
      antisym = antisym;
      refl' = refl';
      trans = trans
    };
    total = total
  }

  where
  antisym : {x y : ℕ} → x ≤ y → y ≤ x → x ≡ y
  antisym 0≤s 0≤s = ≡-refl
  antisym (s≤s p) (s≤s q) = cong suc (antisym p q)

  refl' : {x y : ℕ} → x ≡ y → x ≤ y
  refl' {zero} ≡-refl = 0≤s
  refl' {suc x} ≡-refl = s≤s (refl' ≡-refl)

  trans : {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  trans 0≤s q = 0≤s
  trans (s≤s p) (s≤s q) = s≤s (trans p q)

  total : (x y : ℕ) → Either (x ≤ y) (y ≤ x)
  total zero y = Left 0≤s
  total (suc x) zero = Right 0≤s
  total (suc x) (suc y) with total x y
  total (suc x) (suc y) | Left p = Left (s≤s p)
  total (suc x) (suc y) | Right p = Right (s≤s p)

module ℕ,≤ = TotalOrder ℕ,≤

_≤?_ : ∀ x y → Decision (x ≤ y)
zero ≤? y = yes 0≤s
suc x ≤? zero = no (λ ())
suc x ≤? suc y with x ≤? y
suc x ≤? suc y | yes p = yes (s≤s p)
suc x ≤? suc y | no np = no (λ { (s≤s p) → np p })


_multiple-of_ : ℕ → ℕ → Set
x multiple-of y = ∃ (λ k → k * y ≡ x)


module Props where
  open Equiv (PropEq ℕ)

  private
    _!+!_ : ∀ {x1 x2 y1 y2 : ℕ} → x1 ≡ x2 → y1 ≡ y2 → x1 + y1 ≡ x2 + y2
    _!+!_ = cong2 _+_
    R = λ x → refl {x = x}

    infixl 6 _!+!_

  +-assoc : ∀ x y z → (x + y) + z ≈ x + (y + z)
  +-assoc zero y z = refl
  +-assoc (suc x) y z = cong suc (+-assoc x y z)

  +-left-id : ∀ x → 0 + x ≈ x
  +-left-id _ = refl

  +-right-id : ∀ x → x + 0 ≈ x
  +-right-id zero = refl
  +-right-id (suc x) = cong suc (+-right-id x)

  +-comm : ∀ x y → x + y ≈ y + x
  +-comm zero y = sym (+-right-id y)
  +-comm (suc x) y =
    begin
      suc x + y ≈[ cong suc (+-comm x y) ]
      suc y + x ≈[ sym (one-comm y x) ]
      y + suc x
    qed

    where
    one-comm : ∀ x y → x + suc y ≈ suc x + y
    one-comm zero _ = refl
    one-comm (suc x) y = cong suc (one-comm x y)

  +-suc-assoc : ∀ x y → x + suc y ≈ suc (x + y)
  +-suc-assoc x y =
    begin
      x + suc y   ≈[ sym (+-assoc x 1 y) ]
      (x + 1) + y ≈[ +-comm x 1 !+! R y ]
      suc (x + y)
    qed

  *-+-left-dist : ∀ x a b → x * (a + b) ≈ x * a + x * b
  *-+-left-dist zero a b = refl
  *-+-left-dist (suc x) a b =
    begin
      a + b + x * (a + b)       ≈[ R (a + b) !+! *-+-left-dist x a b ]
      a + b + (x * a + x * b)   ≈[ +-assoc a b _ ]
      a + (b + (x * a + x * b)) ≈[
      cong (a +_) $
        b + (x * a + x * b) ≈[ sym (+-assoc b (x * a) (x * b)) ]
        b + x * a + x * b   ≈[ +-comm b _ !+! R (x * b) ]
        x * a + b + x * b   ≈[ +-assoc (x * a) _ _ ]
        x * a + (b + x * b)
      qed ]
      a + (x * a + (b + x * b)) ≈[ sym (+-assoc a _ _) ]
      a + x * a + (b + x * b)
    qed

  *-+-right-dist : ∀ a b x → (a + b) * x ≈ a * x + b * x
  *-+-right-dist zero b x = refl
  *-+-right-dist (suc a) b x =
    begin
      x + (a + b) * x     ≈[ R x !+! *-+-right-dist a b x ]
      x + (a * x + b * x) ≈[ sym (+-assoc x (a * x) (b * x)) ]
      (x + a * x) + b * x
    qed

  *-assoc : ∀ x y z → (x * y) * z ≈ x * (y * z)
  *-assoc zero y z = refl
  *-assoc (suc x) y z =
    begin
      (y + x * y) * z     ≈[ *-+-right-dist y (x * y) z ]
      y * z + (x * y) * z ≈[ R (y * z) !+! *-assoc x y z ]
      y * z + x * (y * z)
    qed

  *-left-id : ∀ x → 1 * x ≈ x
  *-left-id = +-right-id

  *-right-id : ∀ x → x * 1 ≈ x
  *-right-id zero = refl
  *-right-id (suc x) = cong suc (*-right-id x)

  *-right-zero : ∀ x → x * 0 ≈ 0
  *-right-zero zero = refl
  *-right-zero (suc x) = *-right-zero x

  *-comm : ∀ x y → x * y ≈ y * x
  *-comm zero y = sym (*-right-zero y)
  *-comm (suc x) zero = *-comm x zero
  *-comm (suc x) (suc y) =
    cong suc $
    begin
      y + x * suc y       ≈[ R y !+! (*-+-left-dist x 1 y) ]
      y + (x * 1 + x * y) ≈[ R y !+! (*-right-id x !+! R (x * y)) ]
      y + (x + x * y)     ≈[ sym (+-assoc y x (x * y)) ]
      y + x + x * y       ≈[ +-comm y x !+! *-comm x y ]
      x + y + y * x       ≈[ +-assoc x y (y * x) ]
      x + (y + y * x)     ≈[ R x !+! (sym (*-right-id y) !+! R (y * x)) ]
      x + (y * 1 + y * x) ≈[ R x !+! sym (*-+-left-dist y 1 x) ]
      x + y * suc x
    qed

  suc-inj : ∀ {x y} → suc x ≈ suc y → x ≈ y
  suc-inj ≡-refl = refl

  sum-mult : ∀ {x1 x2 y} → x1 multiple-of y → x2 multiple-of y → (x1 + x2) multiple-of y
  sum-mult {x1} {x2} {y} (k1 , p1) (k2 , p2) =
    k1 + k2
    because:
      (k1 + k2) * y   ≈[ *-+-right-dist k1 k2 y ]
      k1 * y + k2 * y ≈[ p1 !+! p2 ]
      x1 + x2
    qed
