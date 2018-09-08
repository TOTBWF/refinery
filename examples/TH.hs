{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}

module TH where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)

import Control.Applicative hiding (many)

import GHC.Generics (Generic)

import Control.Monad.Trans
import Control.Monad.Except

import Data.List (find)
import Data.Foldable (fold)

import Refinery.MetaSubst
import Refinery.Proof
import Refinery.Telescope (Telescope(..), (@>))
import qualified Refinery.Telescope as Tl
import Refinery.Tactic (tactic, subgoal, solve, many)
import qualified Refinery.Tactic as T

pattern t1 :-> t2 = AppT (AppT ArrowT t1) t2

type instance MetaVar Exp = Name

instance Extract Exp where
  hole = UnboundVarE

instance MetaSubst Exp Lit Q
instance MetaSubst Exp Type Q
instance MetaSubst Exp TyVarBndr Q
instance MetaSubst Exp TyLit Q
instance MetaSubst Exp Pat Q
instance MetaSubst Exp Match Q
instance MetaSubst Exp Body Q
instance MetaSubst Exp Guard Q
instance MetaSubst Exp Stmt Q
instance MetaSubst Exp Dec Q
instance MetaSubst Exp PatSynDir Q
instance MetaSubst Exp PatSynArgs Q
instance MetaSubst Exp Role Q
instance MetaSubst Exp TypeFamilyHead Q
instance MetaSubst Exp InjectivityAnn Q
instance MetaSubst Exp FamilyResultSig Q
instance MetaSubst Exp Pragma Q
instance MetaSubst Exp AnnTarget Q
instance MetaSubst Exp RuleBndr Q
instance MetaSubst Exp Phases Q
instance MetaSubst Exp TySynEqn Q
instance MetaSubst Exp RuleMatch Q
instance MetaSubst Exp Inline Q
instance MetaSubst Exp Fixity Q
instance MetaSubst Exp FixityDirection Q
instance MetaSubst Exp Foreign Q
instance MetaSubst Exp Safety Q
instance MetaSubst Exp Callconv Q
instance MetaSubst Exp Overlap Q
instance MetaSubst Exp FunDep Q
instance MetaSubst Exp DerivClause Q
instance MetaSubst Exp DerivStrategy Q
instance MetaSubst Exp Clause Q
instance MetaSubst Exp Con Q
instance MetaSubst Exp Bang Q
instance MetaSubst Exp SourceUnpackedness Q
instance MetaSubst Exp SourceStrictness Q
instance MetaSubst Exp Range Q
 
instance MetaSubst Exp Name Q where
  metaSubst _ _ = id
  metaSubsts _ = id

instance MetaSubst Exp Exp Q where

  isMetaVar (UnboundVarE n) = Just $ SubstMeta n
  isMetaVar _ = Nothing

data Judgement = [(Name, Type)] :|- Type
  deriving (Show, Generic)

instance MetaSubst Exp Judgement Q

instance MonadName Name Q where
  fresh = newName "?"

instance MonadError [Char] Q where
  throwError = fail
  catchError m h = recover (h "Error") m

instance Alternative Q where
  empty = fail ""
  q1 <|> q2 = recover q2 q1

instance MonadPlus Q 

data RefineError
  = Error String

type Tactic = T.Tactic Exp Judgement Q

intro :: Tactic
intro = tactic $ \(ctx :|- g) -> case g of
  t1 :-> t2 -> do
    x <- lift $ newName "x"
    mx <- subgoal (((x,t1):ctx) :|- t2)
    return $ LamE [VarP x] (UnboundVarE mx)
  ForallT _ _ t -> do
    mx <- subgoal (ctx :|- t)
    return (UnboundVarE mx)
  t -> throwError $ "Intro Mismatch Error: " ++ show t

assumption :: Tactic
assumption = tactic $ \(ctx :|- g) -> do
  case find ((== g) . snd) ctx of
    Just (x,_) -> return (VarE x)
    Nothing -> throwError ("No variables of type: " ++ show g)

refine :: Tactic -> Q Type -> Q Exp
refine t goal = do
  g <- goal
  (ProofState goals ext) <- solve t ([] :|- g)
  case goals of
    Empty -> return ext
    js -> fail $ "Unsolved Goals:\n" ++ (fold $ (\j -> show j ++ "\n") <$> js)

