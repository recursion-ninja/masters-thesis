# Model Justification {#sec:justification}

The verification results of a model have no bearing on TreeKEM unless the model is a faithful and equivalent translation of the protocol.
To verify the TreeKEM protocol, the CGKA security game is used.
Proof that the TreeKEM protocol is a CKGA protocol, as well as proof that results of the CGKA security game for any CGKA protocol are valid for FS and PCS, have already been produced [@alwen2020security].
Justifying the equivelence of this works modeling of the CGKA security game is pivitol to the sounds ness of verifying FS and PCS for TreeKEM.


## CGKA game adaptations {#sec:game-adaptations}

Many novel techniques were used when translating the abstractly defined CGKA securty game to a rigorous and model suitible for explicit state model checking.
The CGKA security game is originally defined as a massively concurrent, infinite game.
An infinite game does not have a definite end (CITE).
This is not always problematic for explicit state model checking, but regretably it is with regards to CGKA securty game.

Within the CGKA game the attacker makes a series of queries to the available oracles.
Queries to oracles drive the CGKA protocl's state over time, however, when playing the game as originaly defined there are no guaranteed limits on total attacker queries to all oracles.
Furthermore, while the attacker decides exactly which order to qury which oracles, all group members of the CGKA protocol concurrently broadcast an unlimited number of messages, both informational and control.
A direct modeling of the CGKA game with a $(T, C, N)$-attacker would require $N+1$ concurrent processes, accounting for the attacker and the maximum possible group members, along with $N$ infinite queues of messages to be received by pariticpants, and crutially monotonically increasing epoch and message counters representing the total ordering enforced by the delivery service.
A single state in the state-space would constitute the unique combiation of all actor processes' internal states, all message queue states, and the global protocol state.
Unfortunately, because of the monotonically increasing counters, there can be no finite representation of the infinite game.

To construct a finite model of an inifite game, the states of the model must not have depend on any monotonically increasing temporal information.
Temporal information converges to a limit in finitely many steps or converges to a to a finite cyles in finitely many steps can all be finitiely modeled.
If a model's state depends on non-converging temporal information, it necessitates that the state-vector length and search-space are infinite.
This follows from the following three facts.

 1. Each state in the state-space must have a unique state-vector encoding. 
 2. The model's state and the equivelent state-vector's encoding must include monotonically increasing temporal information.
 3. In an infinite game, there is no finite encoding of monotonically increasing temporal information.

While explicit state model checking is sophisticated, it ultimate reduces to an exhaustive search which uses a myriad of techniques to cleverly reduce the search space.
There does not exist an general technique for reducing an infinite search space to a finite one, as this would yeild a solution to the halting problem.
Considerable thought was given towards identifying a specific infinite-to-finite reduction for the CGKA security game, but the author is unable to present such a technique in this work.
Instead, different technques are presented to "truncate" an equivelent finite "prefix" of the CGKA security game.


### Exhaustiveness

Verification through explicit state model checking relies on exhaustiveness as it's proof method.
However, the definition of the CGKA security game had no notion of considering every possible interleaving of actions when created.
Instead, tt was defined in a manner which made existential proofs easy to describe and reason about.
Proofs and counterexamples from previous works [@alwen2019double], [@alwen2020security] take the form of scrutinizing the existence of a sequence of queries made by the attacker.
This existential focus permits liency for redundancy within the CGKA security game definition.
Conversely, modeling the CGKA security game such that it is ameniable to explicit state model checking demands absolute parsimony within definition.
Considering the CGKA games definition through the lens an exhuastive state-space search, both conviently and surprisingly, leads to many possible game simplifications.
Because all states are considered, equivelent or superfluous sequences can be reasoned about, identified, and collapsed.


### Elided Group Members


### Indempotency


### Decidability


## Oracles {#sec:game-oracles}

### Corrupt

### Hoard

### Reveal

### Insert

### Remove

### Update

### Deliver


## Security {#sec:ltl-security}

### PCS as LTL

### FS as LTL