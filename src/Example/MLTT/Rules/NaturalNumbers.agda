module Example.MLTT.Rules.NaturalNumbers where


-- ========= Natural numbers ==========

-- Type former
--
--   -------------
--    ⊢ Nat Type

-- Introduction rule
--
--   ----------------------------------
--    x : Nat + Unit ⊢ nat-intro : Nat

-- Elimination rule
--
--    x : Nat ⊢ A Type  ⊢ f₀ : A(nat-intro(inr(unit)))  x : Nat, a : A(x) ⊢ f : A(nat-intro(inl(x)))
--   -----------------------------------------------------------------------------------------------
--                                 x : Nat ⊢ nat-elim : A
