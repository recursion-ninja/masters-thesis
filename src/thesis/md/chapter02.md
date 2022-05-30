# Verification Methodology {#sec:methodology}

The presence or absence of attacks on cryptographic protocols which violate one or more of the security guarantees are exceedingly difficult for humans to catch before widespread adoption [@clark1997survey].
Often attacks are discovered years, if not decades, after a protocol has been in active use.
Late discovery of these attacks after widespread adoption of the protocol requires rapid effort to fix the protocol and encourage all systems using the protocol to update to the revised version.
Often this updating process itself takes years of migration work or the migration never occurs.
This is especially problematic for embedded systems which cannot be easily retrieved and modified.
For these reasons, it is of paramount importance to identify all possible attacks on TreeKEM as early as possible, so they can be corrected before widespread adoption of the MLS standard.

Formal verification takes many forms, with many techniques and tools at our disposal, and choosing the correct verification tool is of utter importance.
In the past, Burrows–Abadi–Needham (BAN) [@burrows1989logic] logic was the tool of choice for verifying cryptographic protocols.
Unfortunately, protocols verified by BAN logic were later found to have undiscovered attacks [@10.5555/188307.188350].
BAN was subsequently critiqued for not being able to fully verify crucial aspects of cryptographic protocols.
Because of such concerns, results and conclusions from verification techniques using BAN logic stating that no attacks exist can be a false-positive.
The kind false-positive verification of security that BAN logic provided could cause the very lapses in post-adoption security that the verification had attempted to preempt.
BAN logic has since fallen out of favor and instead been replaced by model checking techniques [@marrero1997model], which have been able to produce attacks on cryptographic protocols which BAN techniques incorrectly verified as secure.

This work presents the verification of the TreeKEM protocol's FS and PCS security guarantees.
To verify these security guarantees, the CGKA security game will be used as an abstraction of the TreeKEM protocol.
The CGKA security game will be modeled as an explicit finite state transition machine, representing all possible TreeKEM execution states.
The security guarantees will be encoded as Liner Temporal Logic statements.
Then explicit state model checking techniques will be applied to verify that the LTL encodings of FS and PCS are maintained in every possible state of the CGKA security game.

There is one last important detail the verification.
Recall that what differentiates SM from SGM is that SGM involves two or more parties.
There is no theoretical limit to the number of parties the TreeKEM protocol supports.
However, we also stated that model checking represents all possible states of protocol as a finite diagram of transitions.
Here we have a potential problem, where TreeKEM allows an unbounded number of participants, producing an infinite number of possible states, while our model checker requires a finite number of states.
The IETF states that MLS in practice should support approximately 50,000 participants [@Omara2020], which is a finite, yet this very large number is problematic for the chosen methodology explicit state model checking.
This work parametrizes the model in terms of $T$ and $N$ from the definition of *Non-adaptive* $(T, C, N, \textbf{\texttt{P}}, \epsilon)$ *CGKA Security*and limits the scope of verification to within the selected parameters.
In practice, this means the results presented for a specified $T_{max}$ and $N_{max}$ only provide verification of security against $(T, C, N)$-attackers for all $T \in [1, T_{max}]$, $C \in [1, T]$ and $N \in [2, N_{max}]$.


## Explicit state model checking

Model checking exists as the preferred alternative to BAN logic techniques for verifying cryptographic protocols [@kacprzak2006comparing] [@lomuscio2007verification] [@van2004symbolic].
Model checking represents all possible states of protocol as a finite graph of transitions [@clarke1981design].
The model checker then asserts that one or more properties holds for the protocol by traversing through all combinations of transitions through the diagram.
If a property holds, the model checker will assert that there is no possible set of transitions through states that exist in the protocol which violate the specified property.
If the property does not hold, the model checker will produce a counter-example sequence of transitions through possible states showing how the specified property can be violated.
This method of verifying cryptographic protocols is very attractive as the verification result is either an exhaustive proof of security guarantees or a novel cryptographic attack which can be analyzed and corrected.
This constructive proof methodology offered by explicit state model checking, the guarantee of a falsifying counterexample if and only if one exists, is of paramount important for correcting defects within the modeled protocol.

The principle drawback of explicit state model checking is the immensity of the state-space as the complexity of the model grows.
Each possible state in the model is uniquely represented and all transitions for all states are computed during verification.
Controlling memory usage to represent and traverse the searchspace without greatly sacraficing the speed of verification remains a problem with limited tractability.
For TreeKEM, the parameters $T$ and $N$ are supplied to the model.
The model is then verified by exhaustively searching all possible protocol states over $T$ epochs and with the totoal unique group members ranging from $2$ to $N$.
Incrementing the $T$ parameter while holding $N$ constant, generally, increases the statespace by $2$ orders of magnitude.
However, incrementing the $N$ parameter while holding $T$ constant, only increases the statespace by $\frac{1}{2}$ an orders of magnitude.
Due to the constraints engineering constraints presented by explicit state model checking, the verification work presented will only consider the combinatorial collection of all models parameterized by $T$ and $N$, where $T \in [1, T_{max}]$ and $N \in [2, N_{max}]$.


## Linear Temporal Logic

Correctly specifying the properties which must hold for the cryptographic protocol is one of the most important aspects of model checking techniques.
Fortunately, Linear Temporal Logic (LTL) [@4567924] is an almost perfectly tailored language for representing the security guarantees of a cryptographic protocol when used in conjunction with an explicit state model cheacker.
LTL allows a precisely definition of what must occur in specific segments of time during the the protocol's transition through possible states.
An example of LTL's expressive power is that it allows for stating that a property must always hold, eventually hold, hold until another property holds, holds in the next state, never holds, or any combination of these.
LTL possesses just enough expressive power to specify the requirements of the cryptographic protocol's security guarantees, but no more than that.
This perfect balance of expressiveness is important, because the more expressive the logical framework we choose to define our security guarantees, the less efficient the available verification techniques will be.


## Promela

Once we decided to use model checking with LTL as the formal verification methodology, we must then select the appropriate tools to use - the Protocol Meta Language (PROMELA) [@holzmann1980basic], [@holzmann1990design].
It exists as a precise and convenient specification for defining all possible states and transitions for TreeKEM. 
By specifying the protocol in PROMELA, we can allow the PROMELA "translator: to take a high-level, human readable description of TreeKEM and produce a much larger machine readable list with all the possible states and transitions in TreeKEM. 
Manually defining all these states and transitions would take an inordinate amount of time and is prone to errors. 
Producing an exhaustive and correct representation of TreeKEM's possible states and transitions is one aspect of the verification process, at which machines are exceptionally reliable, while humans are not.

The language of PROMELA is similar to the venerable C programming language.
The similarity is not accidental, as it allows for the clear translation between a (perhaps the most) popular systems programming language and the modeling language.
PROMELA supports mutable variable assignment, treating all variables as a finite and lineraly ordered collection of bits.
Assignments mutate an implicit global state.
Variables can take the form of boolean values, signed or unsigned numbers of varying bit widths, type-checked enumerations, or multi-dimensional arrays.
PROMELA also provides looping constructs and an inlining of definition, similar to an inlined function call in C, allowing for code reuse.
These familiar C-like features of PROMELA are evaluated determinisitcally and linearly within the execution of a model defined in PROMELA.
However, PROMELA also differs from C in important ways which faccilitate explicit state graph construction and exhuastive search.

PROMELA only provides non-deterministic conditional constructs.
An \texttt{if} statement is supplied with one or more logical guards containing PROMELA expression which evaluates to a boolean value and an associated (possibly empty) sequence PROMELA expressions for each guard.
The model nondeterministically selects a guard which evaluates to \texttt{true} and follows the code path of the associated sequence of expressions.
Once a the nondeterministically selected code path completes execution, execution resumes at the end of the \texttt{if} statement.
Another similar nondeterministc conditional construct is provided by PROMELA.
A \texttt{do} statement is also supplied with one or more pairs of logical guards and expression sequences.
However, once a the nondeterministically selected code path of the \texttt{do} statement completes execution, execution resumes at the beginning of the \texttt{do} statement.
Execution only resumes at the end of a \texttt{do} block when one of the nondeterministically selected code paths contains a \texttt{break} statement.
This definition of the \texttt{do} statement provides nondeterministic looping behavior.
The \texttt{if} statement permits identical behavior to C \texttt{if/else} statements if all guards are mutually exclusive.
The \texttt{do} statement permits identical behavior to a while loop with correctly constructed guards.
However, the nondeterministic nature of these conditional constructs provide much more expressive power within the model.

There exists one final nondeterministic construct provided by PROMELA.
The \texttt{select} statement takes a contiguous, inclusive range of values and nondeterministically selects a value from within the range, assigning the result to a specified variable.
This replaces the notion of a random number generator within the model.
Explicit state model checking requires that all possible states within the model be explicitly enumerated.
Randomness is replaced by a range of nondeterministic values.
During model checking all possible branches of the \texttt{if}, \texttt{do}, and \texttt{select} constructs are explored, creating a wide array of state transitions for exhaustive search.
The expressive power provided by PROMELA's \texttt{if}, \texttt{do}, and \texttt{select} statements allows for conveniently modeling randomness and alternation in verifiably sound manner.

A major difference from other C-like laguaes is PROMELA's support of concurrency.
A model may include multiple processes, with no restrictions as to when and how the processes are created or terminated.
The model of multiple processes considers the state transitions through each process being interleaved in any permissible permutation during the execution of the model.
Processes can communicate only my mutating shared global state variables or through the message passing channels, semantically FIFO queues, that are shared between two or more processes.
To further support modeling concurrency, PROMELA provides an \texttt{atomic} block for indicating that a sequence of expressions cannot be interleaved between processes.

Lastly, PROMELA supports a \texttt{d\_step} block, which allows specifying that a sequence of expressions are deterministic within the model and should be considered a single state within the generated state-space transition graph.
Unlike an \texttt{atomic} block, a \texttt{d\_step} block cannot include any nondeterministic constructs.
Judicious use of \texttt{d\_step} can greatly simplify the state-space search as well as improve the comprehensibility of any counterexamples produced by the model checker.


## Spin

Once PROMELA is used to produce all possible states and transitions of TreeKEM, we must supply that representation to a model checker which will verify LTL specifications.
Among the many options of model checkers, we will use the SPIN model checker [@godefroid1990using], [@holzmann1997model].
SPIN provides several important features for our verification goals.
The main difficulty with model checking is the size of the number of states and transitions [@burch1992symbolic].
Since model checking works by checking every possible combination of states and transitions, the size of the state-space directly impacts the feasibility.
SPIN provides some solutions to making this problem tractable, the culmination of over three decades of research and development. 
First, SPIN supports "on-the-fly" verification [rudin1987limits], which means that SPIN does not need to consider the entire set of states and transitions at the same time, but instead can work on just subsets until the whole set is verified.
Second, SPIN also uses a "partial ordering" of the states and transitions [@shannon1958note] to reduce the number of subsets it needs to verify before being certain that a property holds for the whole set of states and transitions.
Both "on-the-fly" verification and "partial order" reduction are enabled by default as they can be used in conjunction with minimal drawbacks [@valmari1993fly], [@peled1994combining], [@holzmann1995improvement], [@couvreur1999fly].
Consideration was made to use TopSpin [@DonaldsonM_AMAST2006], a PROMELA preprocessing plugin for SPIN which performs symmetry reduction as well.
Unfortunately, this theoretically viable technique is not prractically usable as the plugin has not been maintained in over a decade.
Additionally, SPIN supports numerous compile time directive which alter the state-space representation, search trajectories, and time-memory tradeoffs.
Because of these (and many more) techniques, SPIN allows efficiently working with a large state-space that the novel portions of TreeKEM produce when modeled with PROMELA.


## Directives

Spin supports many compile-time directives which allows for specifying the possible time-memory tradeoff strategies which are desirable when verifying the specific model.
Not all compile time directives are compatible with all models.
Some directives require a proof by the user that certain conditions hold within the model for the directive's usage to be sound.
Furthermore, many directives' usage are are mutualy exclusive with one or more other directives.
Still, with these restrictions in mind, the carefule selection of compile-time directives is vital to successfully grappling with the enormity of memory usage resulting from the portntially exponential state-space explosion.


### Partial Order Reduction

Partial-order reduction methods represent a well understood collection of state exploration techniques [@godefroid1990using], [@godefroid1991using], [godefroid1994partial], [@holzmann1995improvement], [@katz1992verification], [@peled1993all], [@valmari1989stubborn], [@valmari1992stubborn] whose combined usage can greatly reduce the model checking search-space.
Such techniques are applicable for verifying local and termination of concurrent models.
Furthermore, these techniques are equally applicable for verifying LTL properties, even reducing the state-space when verifying liveness and safety properties within concurrent models [@wolper1983reasoning].
The specific partial order reduction technique of "simultaneous reachability" analysis [@van1997partial] enables the verification of non-executable transitions, absence of deadlock, and buffer overflows.
The extensive research and enginnering effor put into the myriad of partial order reduction techniques have all been incorporated into verification strategies of SPIN, and are enabled by default ,requiring manual "opt-out" compilation directives in order to disable them.
SPIN ineligenty selects applicable partial order reduction techniques for the concurrency of the model, the LTL properties to be verified, and the topology of the state-space.
The verification work presented permitted the usage all the partial order reduction technique made available by SPIN.
No comparative verification(s) were made to observe the runtime difference between explicitly forbiding partial order reduction and permitting the "enabled by default" techniques available to SPIN.

The verification work refrained from from both disabling partial order reduction via the \texttt{NOREDUCE} directive as well as experiment with potential performance gains or regressions introduced by the \texttt{NIBIS} directive.
Instead this work made use of a single partial order reduction directive:

- \texttt{XUSAFE}

The \texttt{XUSAFE} directive disables validity checks of the strictly syncornizing message passing queues.
The encoded model of TreeKEM does not utilize these queues, hence any check related to them would be superfluous.
No noticeable performance gains were observed by utilizing the \texttt{XUSAFE}, but it's usage was retained regardless.


### State Vector Encoding

Each state within the model's state-space is encoded as a "state-vector."
The state vectors uniquely map to each state within the model.
Given that the main memory requirements of model checking lies in exhaustive state-space search, it is unsurprising that specifying the encodign of the state-vectors has a pronounced impact on memory usage.
There are to relevant directives used to influence the model checker's representation of state-vectors:

- \texttt{VECTORSZ=}$X$

- \texttt{MA=}$X$

- \texttt{COLLAPSE}

The \texttt{VECTORSZ} directive is used to specify the number of byte $X$ to allocate for each state-vector.
Spcifying a number of bytes which is insufficient to represent the state vector will cause the compilation of the model to fail with an approximate suggestion of the correct number of bytes to specify.
The \texttt{VECTORSZ} directive is required when the state-vector length exceeds the SPIN default of $1024$ bytes.
Likewise, the \texttt{MA} directive is used to specify the maximum number of bytes $X$ that a state vector can require.
Using the information regarding the upper bound $X$ for state-vector bytes, the model checker then encodes the model as a minimized DFA [@holzmann1999minimized].
The model checker utilizes the smaller representation of the DFA state which corresponds to the original state-vector when processing the enormous statespace.
The translation between DFA representation represents a stark time memory-tradeoff, reducing memory requirements while increasing verification run-time.
Finally, the \texttt{COLLAPSE} directive applies compression the the state-vector representation.
Note that all three directives can be used in conjunction for compounding effects, permitting the minimized DFA representation to be compressed and have the compressed values stored.
The combination produces a very significant memory reduction, however the ussage of \texttt{MA} causes an appreciable increase in verifcation run-time.
This time-memory tradeoff is necissary to make verification of higher $T_{max}$ and $N_{max}$ values tractable, even on modern computing cluster hardware.


### Multi-core Tuning

Since Version 5.0, SPIN has supported performing model checking on multicore machines [@holzmann2007design].
This support brings with it non-trivial engineering considerations, such as how to ensure partial order reduction remains sound across multiple independent prcoessors, how to exchange search state results between processors, how to share or segregate memory, and how to minimize parallelism overhead.
There are two primary directives used my SPIN for approximating the optimal multicore verification stategy at compile-time.
Both of these are used by this work while verifying TreeKEM.

- \texttt{MEMLIM=}$X$
- \texttt{NCORE=}$Y$

The \texttt{MEMLIM} directive specifies the upper limit of memory usable by the model checker to be $X$ Mebibytes for the duration it's verication.
Specifying this has the important effect of preventing the verifcation process from thrashing by utilizing more virtual memory than real memory exists on the verification machine(s).
Moreover, the \texttt{NCORE} directive informs the model checker at compile-time the maximum number of usable processors is $Y$, permitting the compiler to make informed approximations to minimize parallelism overhead and maximize multicore throughput.
The verification work's utilization of both \texttt{MEMLIM} and \texttt{NCORE} directives when utilizing a multicore computing cluster had notable impact on the overall "states per second" processing performance.


### Memory Allocation

A final memory related directive is utilized conditionally during the verification of TreeKEM.

- \texttt{SPACE}

The \texttt{SPACE} directive instructs the compiler to encode the state transition graph as well as select search algorithms with thegoal of reducing memory usage at the expense of verification time.
For large values of $T$ and $N$, the \texttt{SPACE} is utilized in conjunction \texttt{MA} directive described above, to increase the tractable values of $T_{max}$ and $N_{max}$.
During verification of TreeKEM, it is always the case that the \texttt{SPACE} directive is utilized if and only if the \texttt{MA} is also utilized.
This conditional directive usage creates an "optimization partition" bifurcating verification runs into two sets of utilized directives.
An important consequence of this partitioning relates to comparative analysis of the verificationruntime characteristics.
Such comparisons can only soundly be with other verification runs within the same set, utilizing the same directives.


### Runtime Improvement

Without any special direction SPIN includes a number of runtime checks and overhead structures to support functionality which may or may not actually be required for verification.
For each of these "safety rails" added to the verification by default, there exists a directive to remove the runtime feature.
The verification of TreeKEM does not require all runtime features and the following directives are used to remove the associated runtime increases.

- \texttt{NOBOUNDCHECK}
- \texttt{NOFAIR}

The \texttt{NOBOUNDCHECK} directive removes runtime bounds checking when indexing arrays.
While enabled, the bound checking provides extremely useful dbugging information.
Enabling bounds checking is useful while developing the model, but once confidence has been established that indexing errors do not exist in the model, such bounds checks are superfluous.
Additionally, the \texttt{NOBOUNDCHECK} performs runtime checks when syncronously accessing message queues.
The TreeKEM model does not use such message channels.
Consequently, the finalized model does not require bounds checking and the diabling directive is used during verification.

Siminlarly the \texttt{NOFAIR} removes the data structures and tracking subroutines required to reason about and verify fairness properties.
The verification of TreeKEM does not include any fairness properties.
Hence the \texttt{NOFAIR} directive is always enabled.


### Reproducable Randomness

Like many problems with arbitrary alternation or stochastic search strategies, SPIN provides the opportunity for specifying seeds to exactly reproduce the results of random selection.
The benefits of reproduciblity are difficult to understate.
Before the model is finalized, reproducibility is essential during the debugging process.
On the other hand, once the model is finalized, reproducibility is required for certianty during peer review.
Hence, directives for specify seed values are utilized throughout the verification work.

- \texttt{P\_RAND=}$X$
- \texttt{T\_RAND=}$Y$

The first randomness directive, \texttt{P\_RAND}, is utilized to specify the random seed which determines process scheduling order for multi-process models.
The second, \texttt{T\_RAND} is also utilized, and corresponding the seed value dictates the transition exploration order when traversing the state-space.
Random seed values for \texttt{P\_RAND} and \texttt{T\_RAND} were set by manipulating the known numerical constants as defined below.
The transparency of the random seed value selection exists as a "no tricks up my sleeve" technique for specifying arbitrary seed values.

\begin{equation}
\begin{split}
  X = \texttt{1618033988} = & \left| \phi * 10^9 \right|\\
  Y = \texttt{1155727349} = & \left| \frac{\pi}{e} * 10^9 \right|\\
\end{split}
\end{equation}


### Other

This directive is used, as it was suggested by SPIN, but documentation for it cannot be found.

- \texttt{SEP\_STATE}

TODO, fill in more later
