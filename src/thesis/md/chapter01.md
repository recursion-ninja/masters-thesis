# Preliminaries


Modern cryptography has made great progress in improving accessibility and usability of strong encryption.
Secure, accessible, and intuitive communication between two parties has become is ubiquitous worldwide.
Such secure bidirectional communication channels are known as Secure Messaging (SM).
Secure Messaging is supported by a variety of services including ChatSecure, CryptoCat, Cyber Dust, Cyphr, Facebook Messenger, G Data Secure Chat, Gajim, GNOME Fractal, Google Allo, Haven, Kakao Talk, Line, Element, Signal, Silence, Silent Phone, Skype, Telegram, Viber, WhatsApp, and Wickr, Wire.
The utility that these bidirectional protocols provide to the two communicating parites is undeniable.
However, generalizing the security guarantees of SM to communication with more than two parties is still an area of active research.
This generalization to multi-party communication is known as Secure Group Messaging (SGM).


## Secure Group Messaging

SGM described the *use case* of secure multi-party communication.
To be considered a SGM protocol, the following operations must exist for each participating member: create a new communication group consisting of a set of known members, send a message to all members in the group, receive a message from a member in the group, add a new member to the group, and remove an existing member from the group.
One of the novel features of SGM is the ability for members to be added and removed from the secure communication channel.
In the simpler case when two parties use SM, additional participants cannot be added.
Rather than "removing" a participant, the communication channel is simply closed when either party wishes to cease communication.
The SGM requirement of adding and removing participants to the secure communication channel poses interesting open challenges in the field of cryptography.


## Message Layer Security

Message Layer Security (MLS) [@Omara2020] is a framework for providing secure messages in groups of size two or more parties.
Originally produced in 2018 [@ietf-mls-architecture-02], MLS seeks to specify a standardization within which SGM protocols can be defined.
Consequently, implementations conforming to the specification of MLS are a subset of possible SGM implementations.
The stadardized specification of MLS is still an area of active development by The Internet Engineering Task Force (IETF).
However, the core security aspects of MLS relevant to the work presented has remained constant since the initial draft of MLS.

MLS describes the protocol environment in which protocol agents interact.
The Internet threat model of RFC3552 [@rescorla2003rfc3552] is the context within which the MLS specifies it's security guarantees.
Simply put, the Internet threat model assumes that the attacker has complete control of the network.
There are only a two caveats to consider with regard to the attacker's network control, and these are determined by two network agents with which MLS participants can interact.
MLS specifies the existence of an authentication service (AS) from which a messager can request fresh public key for a specified contact which can be immediately used within the MLS protocol.
An advantage of using the AS as described in MLS is that it allows the contact to asynchronously query the AS for the corresponding secret key at a later time, ameliorating potential protocol synchronization issues.
In addition to the AS, MLS specifies the existence of a delivery service (DS).
The DS can receive messages addressed to any contact and the DS stores the messages until the contact queries it for new messages.
Importantly, the DS will always deliver messages from all senders to a contact in the order that they were sent by the senders.
The existence of AS and a DS are required, though these do not need to be the same provider, nor do they need to be centralized.
The attacker is assumed to not be able to masquerade as the authentication service nor violate the message authentication codes within which the message ordering is encoded.

The most scruitinized aspect of the MLS specification involves the provides a set of security guarantees that participants in a conforming a protocol can expect.
The security guarantees of MLS includes many "solved problems" in the field of cryptography with respect to the Internet threat model; notably: end-to-end encryption [@padlipsky1978limitations], message confidentiality (CITE), message integrity [@voydock1983security], message authentication [@jueneman1983message], and membership authentication [@chaum1985showing].
However, MLS also specifies interesting open problems of (perfect) forward secrecy (PFS) [@gunther1989identity] and post-compromise security (PCS) [@cohn2016post] as security guarantees of the key-agreement protocol.

Both PFS and PCS have been researched with respect to bidirectional SM, producing provably secure as well as efficient constructions.
A popular example is the double-ratchet-based AXOLOTL algorithm [@perrin2014axolotl] and it's derivatives which are used by most SM protocols.
However, the requirement of PFS and PCS laid out by the MLS specificzation for a SGM protocol has introduced a novel area of research, as the double-ratchet-based algorithms do not directly map to multi-party communication.
Indeed, these MLS security guarantees have been the chief focus of research related to MLS and it's iterative development.
A trivial construction exists by utilizing a bidirectional SM protocol, and forming a fully connected graph of all SGM participants.
However, it is obvious that this trivial construction's control mesaasges scale quadratically in the size of the communication group whenever the key argeement requires an update.
Maintaining key agreement with the trivial construction is not efficient.

Considering the scope desired protocol constructions, MLS also lays out efficiency goals for implementing protocols with respect to the size of the messaging group.
Three key efficiency distinctions which MLS requires are that the number of control messages should be linear in group size, the size of control messages should be sub-linear in group size, and that group sizes up to 50,000 should be supported.
Taken in it's entirely, the framework provided by MLS is a foundational piece of achieving SGM with well understood efficiency, security guarantees, and protocol design.


## TreeKEM Protocol

The construction of scalable MSL protocols remains an area of open and active research, though the "openness" of this area closes each year.
There currently exist two proposed protocols which meet the definition of MLS with various levels of security proofs as well as efficiency with respect to group size.
The first is Asynchronous Ratcheting Tree (ART) [@cohn2018ends] described in 2018.
The second is TreeKEM [@bhargavan:hal-02425247] similarly conceived in 2018, but formally described in 2019.
The Internet Enginnering Task Force has put it's support behind the TreeKEM protocol along with many other corporate and government sponsors.
Consequently, research directed towards ART has stalled while developments for TreeKEM and it's derivatives have progressed rapidly.
As the MLS draft specification has gone through over a dozen revisions in the last half decade, the concurrent development and refinement of the TreeKEM protocol has significantly informed the direction and language of MLS.
The verifcation work presented here will ignore ART and instead focus exclusively on the TreeKEM protocol.

TreeKEM provides functionality for achieving each of the six operations to be considered a SGM protocol.
Additionally TreeKEM aims to satisfy both the efficiency goals and security guarantees of the MLS specification.
The essence of TreeKEM is a protocol to generate continuous, fresh, shared, and secret random keys for use by group members.
The TreeKEM secret key material evolves over time in such a way that all group members maintain continuous agreement of the shared secret key.
A shared secret key is used to initiate a symmetric hash ratchet which defines a stream of nonce and key pairs for symmetric encryption using an AEAD (CITE).
The stream is used until the shared secret key evolves, after which, a new stream is initiated using the evolved key.
Hash ratchet's produced by TreeKEM are analygous to double-ratchet based protocols in prior work, with the notable difference that, rather than using two ratchets for the two group members, TreeKEM uses a left balanced binary tree structure to define key agreement as a propagation from leaves of the tree to the root node, which supports an arbitrarily large number of group members instead of explicitly two members.
This novel generalization presented in TreeKEM is at the heart of constructing a protocol implementation satisfying the MLS specification.
Unsurprisingly, this same generalization is appreciably linked to proving and verifying the FS and PCS security guarantees of TreeKEM.

The TreeKEM protocol is based around a left balanced binary tree (CITE) shared by all participants.
Each leaf node in the tree contains the public key of exactly one group member, with each group member being associated with a unique leaf in the tree.
Internal nodes of the tree contain a constructed public key, such that the private key is known to each group member in the associated subtree.
The root of the tree contains a symmetric key known to all group members.
Any member may force the evolution of the shared secret key iff and only if they initiate either adding a new group member, removing an existing group member, or the key update procedure.
In each case, the shared secret key at the root node is updated in the same manner.
The initiateing member selects a random seed value $s_0$ and uses it to produce a public/secret key pair $(pk_0,sk_0)$ as well as a new seed value $s_1$.
The member then encrypts the $s_1$ with the public key of it's sister leaf node.
Iteratively, the member moves up the spine of the tree from their leaf node to the root node, using the seed value $s_n$ to generate $(pk_n,sk_n,s_n)$ and encrypting $s_n$ with the public key of the sisted node on level $n$ of the tree.
When the member has propagated the changes to the root node, the final seed value $s_r$ is determined to be the new shared secret key.
Note that each member of the group can derive the seed value required to update their copy of the shared key by decrypting the seed value $s_n$ on the node prior to where the path from said member and the initiating member intersect. 
Once each member has the requisite seed value, they each locally resume the iterative process of updating the tree and arrive at the same construction as that of the initiating member.
For a visualization of this process, refer to Figure 3 of [@alwen2020security].


## Communication Epochs 

A communication group is a set of two or more agents using multiple devices to engage in secure communication.
To initialize a group, members to connect to the AS and DS providers which transmit the requisite credentials and values used for authentication of and encryption between group members.
Subsequently, group members exchange messages with an enforced total ordering mediated by the DS and authenticated via the AS, allowing for asynchronous communication with offline members while preventing the general sequencing issues and race conditions which arise from concurrency.
Additionally, a group can add or remove members, or reset their continuously agreed upon symmetric encryption key; each of which begins a new encryption "epoch."
Advancing to a new epoch requires the creation of a new symetic key known to all group members and secret to all other parties.
Forward Secrecy and Post Compromise Secrecy for TreeKEM are delineated in said epochs.


## Forward Secrecy 

Forward Secrecy (FS) is a desirable security guarantee which offers protection in the case that a protocol's long-term secret key(s) are compromised.
The idea behind FS is that even when all of a group member's current key material is compromised, messages delivered prior to the compromise are still secret.
PFS has been used in bidirectional key agreement communication protocols, including Transport Layer Security (TLS) (CITE) protocols such as OpenSSL (CITE), as well as SM protocols such as the Signal Protocol (CITE).
While the definition of FS has been explored and made rigourously clear for bidirectional key agreement protocols, the notion of FS requires extension in the multi-directional MLS specification.
The following is the definition of FS in the multi-directional protocol context [@alwen2020security] which has been adopted by MLS.

\begin{definition}[Forward Secrecy]
If the state of any group member is leaked at some point, all previous update secrets remain hidden from the attacker.
\end{definition}

## Post-compromise Security

Post-compromise Security (PCS), within the context of bidirectional key agreement protocols, has been conflated with the definition of FS.
However, within the multi-directional MLS specification, the difference between FS and PCS has been separated to describe different security guarantee protocol when one or more of the protocol's long-term secret key(s) are compromised.
The idea behind PCS is that no matter how many compromises of key material occur among the group members previously, once no new compromises occur, the group members will eventually reestablished secrecy through continued protocol usage.
The following definition of PCS in the multi-directional protocol context [@alwen2020security] which has been adopted by MLS.

\begin{definition}[Post-compromise Security]
After every group member whose state was leaked performs an update, and that update is processed by the group, update secrets become secret again.
\end{definition}

## Continuous Group Key Agreement {#sec:CGKA}

In the two party case, a general notion of Continuous Key Agreement [@alwen2019double] has been used to provide robust security guarantees such as forward secrecy and post-compromise security.
For SGM, this general definition has been extended to Continuous \emph{Group} Key Agreement (CGKA) [@alwen2020security] which is used as lemma to derive proofs for some of MLS security guarantees.

A continuous group key-agreement scheme is defined by the following collection of algorithms:

$$ \textbf{\texttt{CGKA}} = (init, create, add, rem, upd, proc)$$

- $init : ID \to \Gamma$  
Given an $ID$, outputs initial state $\gamma$.
	
- $create : \Gamma \times \overrightarrow{ID} \to (\Gamma, W)$  
From state $\gamma$ and list of $ID$s, outputs new state $\gamma'$ and control message $w$.
	
- $add : \Gamma \times ID \to (\Gamma, W, T)$  
From state $\gamma$ and $ID$, outputs new state $\gamma'$, control message $w$ and control message $t$.
	
- $rem : \Gamma \times ID \to (\Gamma, T)$  
From state $\Gamma$ and $ID$, outputs new state $\gamma'$ and a control message $t$.
	
- $upd : \Gamma \to (\Gamma, T)$  
From state $\gamma$, outputs new state $\gamma'$ and control message $t$.
	
- $proc : \Gamma \times T \to (\Gamma, I)$  
From state $\gamma$ and control message $t$, outputs new state $\gamma'$ and update secret $I$.

The abstract collection of algorithms **\texttt{CGKA}** is used to maintain secure communications between a group of 2 or more participants.
Any group member can call any function from **\texttt{CGKA}**, producing new states $\gamma \in \Gamma$ and either none, one, or both control messages $w \in W,\; t \in T$.
There are "welcome" control messages $w \in W$ for a new member entering the group.
There are also "standard" control messages $t \in T$ for existing members in the group tinstructing them how to update the shared symmetric key and advance to the next communication epoch.
The algorithm $proc$ consumes control messages $t \in T$ and produces a secret $i \in I$. 
Each call to $proc$ corresponds to a new epoch, and the secret $i$ is the cryptographic secret update(s) required for the client with $ID$ to maintain CGKA in the new epoch.
Because the communication is defined in terms of epochs, CGKA should satisfy both Forward Secrecy and Post-compromise Security with respect to communication epochs.
The six requisite algorithms required for **\texttt{CGKA}** can be produced by the functionality of the TreeKEM protocol.
For a visualization of each **\texttt{CGKA}** algorithm defined using the functionality of TreeKEM, refer to Figure 4 of [@alwen2020security].
Using the six algorithms of **\texttt{CGKA}**, the security guarantees in for TreeKEM are formulated in terms of a security game.


## Security Games

The same work which defines CGKA also defines an oracle-based security game for CGKA.
Each oracle is defined in terms of one or more of the algorithms from the **\texttt{CGKA}** definition.
The attacker can query all of the game's oracles, and through the sequence of query's, the attacker uses the oracles to direct the execution of the CGKA protocol.
In the game the attacker is given access to various oracles to drive the execution of a CGKA protocol. 
For a visualization of each oracles' semantics, refer to Figure 1 of [@alwen2020security].
The CGKA security game defines the following oracles:

 - **init**()
 - **create-group**($\texttt{ID}_0$, $\texttt{ID}_1$, $\dots$ , $\texttt{ID}_n$)
 - **add-user**($\texttt{ID}$, $\texttt{ID}^{'}$)
 - **remove-user**($\texttt{ID}$, $\texttt{ID}^{'}$)
 - **send-update**($\texttt{ID}$)
 - **deliver**(t, $\texttt{ID}$, $\texttt{ID}^{'}$, c)
 - **no-del**($\texttt{ID}$)
 - **corr**($\texttt{ID}$)
 - **reveal**(t)
 - **chall**(t)

The first six oracles are intuitively thin wrappers for the corresponding algorithm from the **\texttt{CGKA}** definition.
Importantly, these oracles encapsulate from the attacker the stateful procudtion and consumption of group member state values $\gamma \in \Gamma$ as well as the emittion of secret key material values $i \in I$.
Control messages $w \in W$ and $t \in T$ are still broadcast across the network and assuemd to be intercepted by the attacker.
The definition of control messages within the TreeKEM protocol dictates that messages are are authenticated by the group members, which justifies the absence of an oracle permitting the attacker to change or replay intercepted control messages in the CGKA game.

The final four oracles exist to provide the attacker with means to gain undue knwoledge of secret aspects of the CGKA protocol.
The **no-del** oracle forces the specified user to *not* delete old key material when advancing to a new epoch.
The **corr** oracle "corrupts" the specified user, revealing the user's key material to the attacker. Note that if **no-del** is called before **corr** on the same user, the attacker can learn the key material from multiple epochs!
The **reveal** oracle produces the group's shared symmetric key of the specified epoch for the attacker.
The **chall** oracle allows the attacker to signal that they believe that they have succeeded in violating the CGKA protocol's security and the game should immediately cease so the attacker can provide proof of their successful attack by demonstrating *advantage*.

Note that the requisite query to the **init** oracle flips a random bit $b$ uniformly at random is which remains constant for the entirety of the game and is used for the traditional "real-or-random" challenges in security games.
If and only if $b=1$ will the real control messages be broadcast across the network for the attacker to intercept when querying **create-group**, **add-user**, **remove-user**, and **send-update** oracles.
Similarly if and only if $b=1$ will the real member states and update secrets be revealed to the attacker when querying the **corr** and **reveal** oracles.
When $b=0$, random values are instead broadcast and revealed to the attacker when querying the oracles.
The goal of the attacker is to prove advantage by discriminating the value of $b$ with probability grater than $\frac{1}{2}$.

An attacker proving *advantage* is defined by the CGKA security game as a parameterized expression involving oracles of the game.
A tuple $(T, C, N)$ paramaterizes the attacker $\mathcal{A}$, with $T \in \left[1, \infty \right]$, $C \in \left[0, T \right]$, and $N \in \left[2, \infty \right]$.
The $T$ value indicates that the protocol runs in at most $T$ epochs, during which time the attacker can make at most $C$ challenge querres, and the total unique group members of the protocol can never exceed $N$.
Furthermore there exists a predicate **\texttt{P}** (potentially always true), which indicates that a trivial attack did not occur.
The $(T, C, N)$-attacker $\mathcal{A}$ proves *advantage* by ending the game via a query to the **chall** oracle, winning the CGKA security game, if and only if the attacker:

- Correctly determines the value random bit $b$
- The predicate **\texttt{P}** evaluates to \texttt{true}.

\begin{definition}[CGKA advantage]
The advantage proved by $\mathcal{A}$ is defined as,
$$ \normalfont{\textbf{Adv}}\left\{\textbf{\texttt{CGKA}},\textbf{\texttt{P}}\right\}(\mathcal{A})  = \left|\; \textbf{Pr}\left[ \,\mathcal{A}\text{ wins}\, \right] - \frac{1}{2} \;\right| $$
\end{definition}

\begin{definition}[Non-adaptive $(T, C, N, \textbf{\texttt{P}}, \epsilon)$ CGKA Security]  
A CGKA protocol is said to be secure if and only if for all $(T, C, N)$-attackers $\mathcal{A}$,
$$ \normalfont\textbf{Adv}\left\{\textbf{\texttt{CGKA}},\textbf{\texttt{P}}\right\}(\mathcal{A}) \leq \epsilon $$
\end{definition}

The CGKA algorithms, security game, and *Non-adaptive* $(T, C, N, \textbf{\texttt{P}}, \epsilon)$ *CGKA Security* definition are integral to the verification work present.
Chapter \ref{sec:methodology} will use the security definition to parameterize and constrain the verification methodology presented.
In a similar manner, the definition and understanding of *Non-adaptive* $(T, C, N, \textbf{\texttt{P}}, \epsilon)$ *CGKA Security* will be extensively relied upon in Chapter \ref{sec:justification} when constructing the model encoding of TreeKEM.
This reliance extends to the discussions in Section \ref{sec:game-adaptations} related to utilizing explicit state model checking when modeling and verifying TreeKEM
as well as in Section \ref{sec:game-oracles} modeling the translations of the ten CGKA security game oracles explicitly for TreeKEM.
Additionally, the modeling of random $b$ and attacker advantage will be elaborated on in Section \ref{sec:game-adaptations}.
Subsequently Section \ref{sec:ltl-security} presents definitions of the predicate **\texttt{P}** for prohibiting "trivial attacks" explicitly related to TreeKEM and the CGKA game as described by [@alwen2020security].


## Concluding Abstraction

It is worth noting the relationship between the preliminary definitions explored thusfar.
SGM is a description of the high-level use case.
The MLS specification is standardization which protocols may conform to and which satisfies the SGM use case.
CGKA is a class of protocols supporting the requisite algorithms.
TreeKEM is a cryptographic protocols which conforms to the MLS specification and facilatates the CGKA algorithms.
There is a clear subsetting relationship between these abstract concepts illistrated in \ref{fig:venn-protocols}, and in future descriptions the layer of abstraction from which a definition was defined may be elided.

![Relationship of Secure Group Messaging, Message Layer Security, Continuous Group Key Agreement, and TreeKEM \label{fig:venn-protocols}](png/venn-protocols.png){height=4cm}

