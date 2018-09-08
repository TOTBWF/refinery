{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
module STLC where

import GHC.Generics
import Data.Typeable
import Data.List (find)

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad.Except


import Unbound.Generics.LocallyNameless

import Refinery.Hole
import Refinery.Telescope (Telescope, (@>))
import qualified Refinery.Telescope as Tl
import qualified Refinery.Tactic as T
import Refinery.Extract

type Var = Name Term

data Term
    = Var Var
    | Hole (Ignore (MetaVar Term))
    | Lam (Bind Var Term)
    | App Term Term
    deriving (Show, Typeable, Generic)

instance Alpha Term
instance Subst Term Term where
    isvar (Var x) = Just $ SubstName x

lam :: Var -> Term -> Term
lam x t = Lam (bind x t)

metaSubst' :: (LFresh m) => MetaVar Term -> Term -> Term -> m Term
metaSubst' x e = \case
  Hole (unignore -> x') | x == x' -> return e
  Lam bnd -> lunbind bnd $ \(x',b) -> lam x' <$> metaSubst' x e b
  App f a -> App <$> metaSubst' x e f <*> metaSubst' x e a
  t -> return t

metaSubsts' :: (LFresh m) => [(MetaVar Term, Term)] -> Term -> m Term
metaSubsts' xs = \case
  Hole (unignore -> x') -> case find (\(x,e) -> x == x') xs of
    Just (_, e) -> return e
    Nothing -> return $ Hole $ ignore x'
  Lam bnd -> lunbind bnd $ \(x',b) -> lam x' <$> metaSubsts' xs b
  App f a -> App <$> metaSubsts' xs f <*> metaSubsts' xs a
  t -> return t


instance MetaSubst Term Term where
  metaSubst x e t = runLFreshM $ metaSubst' x e t
  metaSubsts xs t = runLFreshM $ metaSubsts' xs t

type TVar = Name Type

data Type
  = TVar TVar
  | Type :-> Type
  deriving (Show, Typeable, Generic)

instance Alpha Type
instance Subst Type Type where
  isvar (TVar a) = Just $ SubstName a
  isvar _ = Nothing

data Judgement = J (Map Var Type) Type 
  deriving (Show)

type Tactic = T.Tactic Term Judgement (FreshMT (Except ()))

intro :: Tactic
intro = T.tactic $ \case
  J ctx (t1 :-> t2) -> do
    x <- fresh $ s2n "x"
    mx <- T.subgoal (J (Map.insert x t1 ctx) t2)
    return $ lam x (Hole $ ignore mx)

assumption :: Tactic
assumption = T.tactic $ \(J ctx t) -> 
  case Map.keys $ Map.filter (aeq t) ctx of
    (x:_) -> return $ Var x
    [] -> throwError ()

goal :: Type
goal = let a = s2n "a" in (TVar a) :-> (TVar a)

tac = intro <> assumption
