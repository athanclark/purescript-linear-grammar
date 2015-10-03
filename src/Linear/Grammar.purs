module Linear.Grammar
  ( -- * User-facing API
    multLin
  -- * Linear Expressions
  , addLin
  -- * Linear Inequalities
  , (.==.)
  , (.<=.)
  , (.=>.)
  , makeLinExpr
  -- * Standard Form
  , standardForm
  , hasNoDups
  , module X
  ) where

import Prelude

import Linear.Grammar.Types
import qualified Linear.Grammar.Types as X

import Data.Rational
import Data.Tuple
import Data.Monoid
import Data.Foldable
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map


-- | Pushes @ECoeff@ down the tree, leaving @EAdd@ at the top level.
-- After using this funciton, all @ECoeff@ constructors @LinAst@ parameter will
-- be @EVar@.
multLin :: LinAst -> LinAst
multLin (EVar n) = EVar n
multLin (ELit x) = ELit x
multLin (ECoeff e x) = case multLin e of
  (ELit y)      -> ELit (y * x)
  (EVar n)      -> ECoeff (EVar n) x
  (ECoeff e' y) -> ECoeff e' (y * x)
  (EAdd e1 e2)  -> EAdd (multLin $ ECoeff e1 x) (multLin $ ECoeff e2 x)
multLin (EAdd e1 e2) = EAdd (multLin e1) (multLin e2)

-- | Turns @LinAst@ to @LinExpr@ - should be done /after/ @multLin@.
addLin :: LinAst -> LinExpr
addLin = go (LinExpr (LinVarMap Map.empty) $ 0 % 1)
  where
    go :: LinExpr -> LinAst -> LinExpr
    go (LinExpr (LinVarMap vs) c) (EVar n) =
      LinExpr (LinVarMap $ maybe (Map.insert (VarMain n) (1 % 1) vs)
                                 (\coeff -> Map.insert (VarMain n) (coeff + (1 % 1)) vs) $
                                 Map.lookup (VarMain n) vs) c
    go (LinExpr vs c) (ELit x) = LinExpr vs (c + x)
    go (LinExpr (LinVarMap vs) c) (ECoeff (EVar n) x) =
      LinExpr (LinVarMap $ maybe (Map.insert (VarMain n) x vs)
                                 (\coeff -> Map.insert (VarMain n) (coeff + x) vs) $
                                 Map.lookup (VarMain n) vs) c
    go le (EAdd e1 e2) = mergeLinExpr (go le e1) (go le e2)


(.==.) :: LinAst -> LinAst -> IneqExpr
(.==.) x y = EquExpr (makeLinExpr x) (makeLinExpr y)

infixl 7 .==.

(.<=.) :: LinAst -> LinAst -> IneqExpr
(.<=.) x y = LteExpr (makeLinExpr x) (makeLinExpr y)

infixl 7 .<=.

(.=>.) :: LinAst -> LinAst -> IneqExpr
(.=>.) = flip (.<=.)

infixl 7 .=>.

makeLinExpr :: LinAst -> LinExpr
makeLinExpr = addLin <<< multLin

-- | Turns a user-level AST to a structurally standard from inequality.
standardForm :: IneqExpr -> IneqStdForm Rational
standardForm = go <<< standardize
  where
    go (EquExpr (LinExpr xs xc) (LinExpr ys yc)) | xs == mempty && yc == 0 % 1 = EquStd $ Equ ys xc
                                                 | ys == mempty && xc == 0 % 1 = EquStd $ Equ xs yc
    go (LteExpr (LinExpr xs xc) (LinExpr ys yc)) | xs == mempty && yc == 0 % 1 = GteStd $ Gte ys xc -- Ax >= M
                                                 | ys == mempty && xc == 0 % 1 = LteStd $ Lte xs yc -- Ax <= M

    -- Standardizes user-level inequalities - to be used before @standardForm@.
    standardize :: IneqExpr -> IneqExpr
    standardize (EquExpr (LinExpr xs xc) (LinExpr ys yc))
      | xs == mempty = EquExpr (LinExpr mempty (xc - yc)) (LinExpr ys $ 0 % 1)
      | ys == mempty = EquExpr (LinExpr xs $ 0 % 1) (LinExpr mempty (yc - xc))
      | otherwise =
          let ys' = mapCoeffVals ((-1 % 1) *) ys
          in EquExpr (LinExpr (ys' <> xs) $ 0 % 1) (LinExpr mempty (yc - xc))
    standardize (LteExpr (LinExpr xs xc) (LinExpr ys yc))
      | xs == mempty = LteExpr (LinExpr mempty (xc - yc)) (LinExpr ys $ 0 % 1)
      | ys == mempty = LteExpr (LinExpr xs $ 0 % 1) (LinExpr mempty (yc - xc))
      | otherwise =
          let ys' = mapCoeffVals ((-1 % 1) *) ys
          in LteExpr (LinExpr (ys' <> xs) $ 0 % 1) (LinExpr mempty (yc - xc))


hasNoDups :: forall a. (Ord a) => Array a -> Boolean
hasNoDups = snd <<< foldl go (Tuple Set.empty true)
  where
    go (Tuple s false) _ = (Tuple s false)
    go (Tuple s true) x  = let s' = Set.insert x s
                           in if Set.size s' > Set.size s
                              then (Tuple s' true)
                              else (Tuple s false)
