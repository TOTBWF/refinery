{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}

module TH where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)

import Control.Applicative hiding (many)

import GHC.Generics hiding
  ( SourceUnpackedness
  , SourceStrictness
  , Fixity)

import Control.Monad.Trans
import Control.Monad.Except

import Data.List (find)
import Data.Foldable (fold)
import Data.Traversable

import Data.Proxy

import Refinery.MetaSubst
import Refinery.Proof
import Refinery.Telescope (Telescope(..), (@>))
import qualified Refinery.Telescope as Tl
import Refinery.Tactic (tactic, subgoal, solve, many)
import qualified Refinery.Tactic as T

pattern t1 :-> t2 = AppT (AppT ArrowT t1) t2

tuple :: Type -> Maybe [Type]
tuple = go []
  where
    go :: [Type] -> Type -> Maybe [Type]
    go ts (AppT (TupleT i) t) =
      let ts' = t:ts
      in (if length ts' == i then Just ts' else Nothing)
    go ts (AppT t1 t2) = go (t2:ts) t1
    go _ _ = Nothing

pattern Tuple ts <- (tuple -> Just ts)

type instance MetaVar Exp = Name

instance Evidence Exp where
  hole = UnboundVarE

instance MetaSubst Exp Lit
instance MetaSubst Exp Type
instance MetaSubst Exp TyVarBndr
instance MetaSubst Exp TyLit
instance MetaSubst Exp Pat
instance MetaSubst Exp Match
instance MetaSubst Exp Body
instance MetaSubst Exp Guard
instance MetaSubst Exp Stmt
instance MetaSubst Exp Dec
instance MetaSubst Exp PatSynDir
instance MetaSubst Exp PatSynArgs
instance MetaSubst Exp Role
instance MetaSubst Exp TypeFamilyHead
instance MetaSubst Exp InjectivityAnn
instance MetaSubst Exp FamilyResultSig
instance MetaSubst Exp Pragma
instance MetaSubst Exp AnnTarget
instance MetaSubst Exp RuleBndr
instance MetaSubst Exp Phases
instance MetaSubst Exp TySynEqn
instance MetaSubst Exp RuleMatch
instance MetaSubst Exp Inline
instance MetaSubst Exp Fixity
instance MetaSubst Exp FixityDirection
instance MetaSubst Exp Foreign
instance MetaSubst Exp Safety
instance MetaSubst Exp Callconv
instance MetaSubst Exp Overlap
instance MetaSubst Exp FunDep
instance MetaSubst Exp DerivClause
instance MetaSubst Exp DerivStrategy
instance MetaSubst Exp Clause
instance MetaSubst Exp Con
instance MetaSubst Exp Bang
instance MetaSubst Exp SourceUnpackedness
instance MetaSubst Exp SourceStrictness
instance MetaSubst Exp Range
 
instance MetaSubst Exp Name where
  metaSubst _ _ = id
  metaSubsts _ = id

instance MetaSubst Exp Exp where

  isMetaVar (UnboundVarE n) = Just $ SubstMeta n
  isMetaVar _ = Nothing

data Judgement = Judgement
  { hypotheses :: [(Name, Type)]
  , hidden :: [(Name, Type)]
  , goalType :: Type
  }
  deriving (Show, Generic)

emptyCtx :: Type -> Judgement
emptyCtx t = Judgement { hypotheses = [], hidden = [], goalType = t }

extend :: Name -> Type -> Judgement -> Judgement
extend x t j@Judgement{..} = j{ hidden = (x,t):hidden }

withGoal :: Type -> Judgement -> Judgement
withGoal t j@Judgement{..} = j{ goalType = t }

instance MetaSubst Exp Judgement

instance MonadName Name Q where
  fresh = newName "?"

instance MonadError [Char] Q where
  throwError = fail
  catchError m h = recover (h "Error") m

instance Alternative Q where
  empty = fail "Unspecified Error"
  q1 <|> q2 = recover q2 q1

instance MonadPlus Q 

data RefineError
  = Error String

type Tactic = T.Tactic Exp Judgement Q

-- | Brings a name into scope
with :: (Name -> Tactic) -> Tactic
with f = T.Tactic $ \j@Judgement{..} ->
  case hidden of
    ((x,t):hs) -> (solve $ f x) j{ hidden = hs, hypotheses = (x,t):hypotheses }
    [] -> throwError $ "No variables to bring into scope!" ++ show j

-- | Uses an in-scope name to solve a goal
use :: Name -> Tactic
use x = tactic $ \j@Judgement{..} ->
  case find ((== x) . fst) hypotheses of
    Just (_,t) ->
      if t == goalType
      then return (VarE x)
      else throwError $ "Expected type " ++ show goalType ++ " but " ++ show x ++ " has type " ++ show t
    Nothing -> throwError $ "Undefined variable " ++ show x

-- | Introduction tactic, operates of pairs, forall, and functions 
intro :: Tactic
intro = tactic $ \j@Judgement{..} -> case goalType of
  t1 :-> t2 -> do
    x <- lift $ newName "x"
    mx <- subgoal $ withGoal t2 $ extend x t1 j
    return $ LamE [VarP x] (UnboundVarE mx)
  ForallT _ _ t -> do
    x <- subgoal $ withGoal t j
    return $ hole x
  Tuple ts -> do
    mxs <- traverse (\t -> fmap hole $ subgoal $ withGoal t j) ts
    return $ TupE mxs
  t -> throwError $ "Intro Mismatch Error: " ++ show t

-- | Searches the hypotheses for any type that may match the goal
assumption :: Tactic
assumption = tactic $ \j@Judgement{..} ->
  case find ((== goalType) . snd) (hypotheses ++ hidden) of
    Just (x, _) -> return $ VarE x
    Nothing -> throwError $ "No variables of type " ++ show goalType

refine :: Tactic -> Q Type -> Q Exp
refine t goal = do
  g <- goal
  (ProofState goals ext) <- solve t $ emptyCtx g
  case goals of
    Empty -> return ext
    js -> throwError $ "Unsolved Goals:\n" ++ (fold $ (\j -> show j ++ "\n") <$> js)

