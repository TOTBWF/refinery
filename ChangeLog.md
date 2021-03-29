# Changelog for refinery

* 0.4.0.0
  - How failure is handled has been refined somewhat. Previously, if a
    tactic failed, then the extraction process was terminated, and
    `proofs` would return a `Left` describing the error. This design
    worked, but led to some suboptimal error reporting. To fix this,
    the `Failure` constructor from `ProofStateT` has been changed from
    ```
    | Failure err
    ```
    to
    ```
    | Failure err (ext' -> ProofStateT ext' ext err s m goal)
    ```

    This allows us the option to continue the extraction process even
    in the face of failure. This option is exercised in `partialProofs`
    and `runPartialTacticT`.

  - A bunch of helpful combinators have been added for extract
    manipulation inside of tactics.
  - `proofs` no longer returns a tuple, but rather a record type
    ```
    data Proof s meta goal ext = Proof { pf_extract :: ext, pf_state :: s, pf_unsolvedGoals :: [(meta, goal)] }
    ```
  - Added `handler`, and removed the `MonadError` instance for `TacticT`.
    Now, instead of recovering from errors (which was fraught with subtle issues),
	we allow the user to annotate errors instead.
  - Added some useful tactic combinators:
    - tweak
	- peek
	- poke
	- inspect
	- some_
  - Swapped the order of arguments to `mapExtract` to line up with `Profunctor`
  - Reworked `MonadExtract` to support named holes.
  - Added `reify` and `resume` combinators, which are used for inspecting the current proof state during tactic execution.
* 0.3.0.0
  - Reworked the core types of the library, which fixed a lot of the weird behavior
  that users were experiencing.
* 0.2.0.0
  - Added Alternative/MonadPlus instances to ProofStateT, TacticT, RuleT
* 0.1.0.0
  - Initial Release of the library
