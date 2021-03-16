# Refinery

[![Hackage](http://img.shields.io/hackage/v/refinery.svg)]


`refinery` provides a series of language-independent building blocks for creating automated, type directed program synthesis tools.
It is currently used to power the automatic code synthesis tool [Wingman For Haskell](https://haskellwingman.dev/).

## Introduction
If you are already familiar with the idea of tactics, feel free to skip ahead to the [Usage](#Usage) section.

What exactly do we do when we sit down and write a program? Sure, we may have lofty ideas about
what it may do in the end, but I'm talking about the actual process of writing a program.
For instance, take the following (rather silly) example:
```haskell
pairing :: (a -> b) -> (a -> c) -> a -> (b,c)
pairing = _
```

The first thing we might do is look at the type, see that we are writing a function, and introduce the arguments.
```haskell
pairing :: (a -> b) -> (a -> c) -> a -> (b,c)
pairing f g a = _
```

Then, we see that we are trying to make a pair type, so we will introduce a pair constructor.
```haskell
pairing :: (a -> b) -> (a -> c) -> a -> (b,c)
pairing f g a = (_, _)
```
Then, we will see that we need to produce a `b` and a `c`, and we have two functions in scope that do that, so may as well
try them!
```haskell
pairing :: (a -> b) -> (a -> c) -> a -> (b,c)
pairing f g a = (f _, g _)
```
Now, we need an `a`, and we have one in scope, so let's use that!
```haskell
pairing :: (a -> b) -> (a -> c) -> a -> (b,c)
pairing f g a = (f a, g a)
```

Now, this entire process of writing this function was entirely mechanical. We just looked at the type of the hole,
looked at what we had in scope, and applied some simple edits to get some more holes, and repeated. This feels
like we could automate this!

Now, a "tactic" is exactly this. We can think of it morally as something like the following type: `(Type -> [Type], [Expr -> Expr])`.
In short, they break the hole down into a bunch of smaller holes, and combine expressions that fit into those holes into one big expression!
This library provides the means for creating simple tactics for _any_ language you can cook up, as well as "tactic combinators", which have
a similar flavor to parser combinators. Parser combinators let us compose small atomic parsers together to form larger ones, and Tactic
combinators let us compose together small tactics to create sophisticated tools for automatic program synthesis.

## Usage
Let's walk through the usage of this library with a small example. The full source code of this example can be found in `tests/Spec/STLC.hs`.

First, let's import the main module, along with some MTL stuff:
```
import Data.List

import Control.Monad.Identity
import Control.Monad.State

import Refinery.Tactic
```


Now let's define a teeny tiny simply typed lambda calculus:
```haskell
-- Expressions in simply typed lambda calculus, along with holes
data Term
  = Var String
  | Hole
  | Lam String Term
  | Pair Term Term
  deriving (Show, Eq)

-- Types in our version of simply typed lambda calculus
data Type
  = TVar String
  | Type :-> Type
  | TPair Type Type
  deriving (Show, Eq)
```

Now, we are going to need to define the idea of a "type in a context", commonly referred to as a "Judgement".
```haskell
newtype Judgement = [(String, Type)] :- Type
  deriving (Show)
```

Now, a bit of boilerplate is required to tell `refinery` how to generate holes.
Most of the time, you will need to have a fresh source of variables for your holes, or you
may need to run effects when you generate them. However, in the name of simplicity, let's just use
`Identity`
```haskell
instance MonadExtract Term String Identity where
    hole = pure Hole
    unsolvableHole _ = pure Hole
```

Now for our first tactic:
```haskell
type T a = TacticT Judgement Term String Int Identity a

-- Tactic for solving holes of type (a,b)
pair :: T ()
pair = rule $ \goal ->
    case goal of
      (hys :- TPair a b) -> Pair <$> subgoal (hys :- a) <*> subgoal (hys :- b)
      _                  -> unsolvable "goal mismatch: Pair"
```

Now, there is a _lot_ going on here, so let's take it apart piece by piece:
To start, let's look at `TacticT`. The first type parameter is the "goal" type.
We can think of this as the thing that we are trying to "solve". For us, this
is `Judgement`, as we are going to need to know exactly what is in scope at a given point.

The next type parameter is what the tactic is going to synthesize, commonly referred to as the
"extract".

The next three type parameters are decidedly less exciting. They represent the type of errors, the
type of the state, and the base monad. We need to have a way of generating unique names, so let's
just use `Int` as our state to accomplish this.

<!-- FIXME: Better explanation -->
That final type parameter is the type that the tactic during the course of execution. We will discuss this further in the future,
so if you are confused, feel free to ignore this type parameter for now.

Next, we call `rule` to create a "basic" tactic, that lets us inspect the current goal, and create a bunch of subgoals via `subgoal`.
As we are trying to tell `refinery` how to synthesize pairs, we case on the type of the hole. If it is a pair type, we create two
new goals, one for each component of the tuple type, and then combine the solutions to those subgoals together with a pair constructor.
If the type does not match, then we throw an error via `unsolvable`.


Now, finally, we need a way of solving goals of the form `a -> b`.
```
lam :: T ()
lam = rule $ \case
    (hys :- (a :-> b)) -> do
        name <- gets show
        modify (+ 1)
        body <- subgoal $ ((name, a) : hys) :- b
        pure $ Lam name body
    _                  -> unsolvable "goal mismatch: Lam"
```
This is where the state comes in. We look up the current state, show it for use as a name,
and then increment it so that our names are unique. We then create a subgoal for `b`,
and add our new fresh name into scope, specifying that it has type `a`.
We then get the result of the subgoal and put it in a `Lam` constructor along with our fresh name.

Finally, let's define a tactic for solving a goal by using something in scope.
```haskell
assumption :: T ()
assumption = rule $ \ (hys :- a) ->
  case find (\(_, ty) -> ty == a) hys of
    Just (x, _) -> pure $ Var x
    Nothing     -> unsolvable "goal mismatch: Assumption"
```

Now, for something really exciting. Let's write a tactic that can synthesize expressions for this language. Now that we have our building blocks, this
is very easy!
```haskell
auto :: T ()
auto = do
    many_ lam
    (pair >> auto) <|> assumption
```
Before explaining how exactly this _works_, let's look at what it does!
```haskell
λ> solutions auto ([] :- (TVar "a" :-> TVar "b" :-> (TPair (TVar "a") (TVar "b")))) 0
> [Lam "0" (Lam "1" (Pair (Var "0") (Var "1")))]
```

As we can see, it generated the right thing! Let's now step through _how_ exactly it did this.
To start, `many_` is a "tactic combinator". It takes a tactic as it's first argument, and
will run it repeatedly until it fails. This will result in a single subgoal that looks something like
```haskell
[("0", TVar "a"), ("1", TVar "b")] :- (TPair (TVar "a") (TVar "b"))
```

Now, for the magic. The bind for `TacticT` will run the second tactic on _every_ subgoal created by the first.
With this crucial piece of information, we can begin to see how `auto` works. Once `many_ lam` is executed,
we execute both `pair >> auto` and `assumption` against the subgoal generated, and collect all of the
solutions found by both branches together. `pair` will generate 2 subgoals, and then `>> auto` will apply
`auto` recursively to _both_ of those subgoals.

## References
`refinery` is based roughly on [Algebraic Foundations of Proof Refinement](https://arxiv.org/abs/1703.05215)
