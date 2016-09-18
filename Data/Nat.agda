-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Data.Nat where

-- open import Algebra.Monoid
open import Core
open import Data.Nat.Core


-- + : MonoidOver ≡
-- + =
--   record {
--     semigroupOver = record {
--       _⋄_ = _+_;
--       ⋄-cong = cong2 _+_;
--       assoc = Props.+-assoc
--     };
--     id = 0;
--     left-id = λ _ → refl;
--     right-id = Props.+-right-id
--   }

--   where
--   open Equiv (PropEq ℕ)

-- module + = MonoidOver +


-- * : MonoidOver ≡
-- * =
--   record {
--     semigroupOver = record {
--       _⋄_ = _*_;
--       ⋄-cong = cong2 _*_;
--       assoc = Props.*-assoc
--     };
--     id = 1;
--     left-id = Props.+-right-id;
--     right-id = Props.*-right-id
--   }

-- module * = MonoidOver *
