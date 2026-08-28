module Example.MLTT.Rules.SumType where

-- ======== Sum type ==========

-- Type former
--
--    ⊢ A Type  ⊢ B Type
--   --------------------
--       ⊢ A + B Type

-- Introduction rules
--
--    ⊢ A Type  ⊢ B Type
--   ---------------------
--    x : A ⊢ inl : A + B

--    ⊢ A Type  ⊢ B Type
--   ---------------------
--    x : B ⊢ inr : A + B

-- Elimination rule
--
--    ⊢ A Type  ⊢ B Type  x : A + B ⊢ C Type
--       x : A ⊢ f : C  y : B ⊢ g : C
--   -----------------------------------------
--         x : A + B ⊢ sum-elim : C
