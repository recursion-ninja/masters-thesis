# Preliminaries


Modern cryptography has made great progress in improving accessibility and usability of strong encryption.
Secure, accessible, and intuitive communication between two parties has become is ubiquitous worldwide.
Such secure bidirectional communication channels are known as Secure Messaging (SM).
Secure Messaging is supported by a variety of services including ChatSecure, CryptoCat, Cyber Dust, Cyphr, Facebook Messenger, G Data Secure Chat, Gajim, GNOME Fractal, Google Allo, Haven, Kakao Talk, Line, Element, Signal, Silence, Silent Phone, Skype, Telegram, Viber, WhatsApp, and Wickr, Wire.
The utility that these bidirectional protocols provide to the two communicating parites is undeniable.
However, generalizing the security guarantees of SM to communication with more than two parties is still an area of active research.
This generalization to multi-party communication is known as Secure Group Messaging (SGM).

## Secure Group Messaging

SGM described the *use case*. of secure multi-party communication.
To be considered a SGM protocol, the following operations must exist for each participating member: create a new communication group consisting of a set of known members, add a new member to the group, and remove an existing memebr from the group.
One of the novel features of SGM is the ability for members to be added and removed from the secure communication channel.
In the simpler case when two parties use SM, additional participants cannot be added.
Rather than "removing" a participant, the communication channel is simply closed when either party wishes to cease communication.
The SGM requirement of adding and removing participants to the secure communication channel poses interesting open challenges in the field of cryptography.


## Message Layer Security

Message Layer Security (MLS) [@Omara2020] is a framework for providing secure messages in groups of size two or more parties.
Originally produced in 2018 [@ietf-mls-architecture-02], MLS seeks to specify a standardization within which SGM protocols can be defined.
Consequently, implementations conforming to the specification of MLS are a subset of possible SGM implementations.
The stadardized specification of MLS is still an area of active develoment by The Internet Engineering Task Force (IETF).
However, the core security aspects of MLS relevant to the work presented has remained constant since the initial draft of MLS.

MLS describes the protocol environment in which protocol agents interact.
The Internet threat model of RFC3552 [@rescorla2003rfc3552] is the context within which the MLS specifies it's security guarantees.
Simply put, the Internet threat model assumes that the attacker has complete control of the network.
There are only a two caveats to consider with regard to the attacker's netowrk control, and these are determined by two network agents with which MLS participants can interact.
MLS specifies the existance of a key server from which a messager can request fresh public key for a specified contact which can be immediately used within the MLS protocol implementation.
An advantage of using a key server as described in MLS is that it allows the contact to asyncronously query the key server for the corresponsing secret key at a later time, ameliorating potential protocol syncronization issues.
In addition to the key server, MLS specifies the existance of a message server.
The message server can receive messages addressed to any contact and the message server stores the messages until the contact querries it for new messages.
Importantly, the message server will always deliver messages from all senders to a contact in the order that they were sent by the senders.
The attacker is assumed to not be able to masquarade as the key server nor violate the message authentication codes within which the message ordering is encoded.

The most scruitinized aspect of the MLS specification involves the provides a set of security guarantees that participants in a conforming a protocol can expect.
The security guarantees of MLS includes many "solved problems" in the field of cryptography with respect to the Internet threat model; notably: end-to-end encryption [@padlipsky1978limitations], message confidentiality (CITE), message integrity [@voydock1983security], message authentication [@jueneman1983message], and membership authentication [@chaum1985showing].
However, MLS also specifies interesting open problems of (perfect) forward secrecy (PFS) [@gunther1989identity] and post-compromise security (PCS) [@cohn2016post] as security guarantees of the key-agreement protocol.

Both PFS and PCS have been researched with respect to bidirectional SM, producing provably secure as well as efficient constructions.
A popular example is the double-ratchet-based AXOLOTL algorithm [@perrin2014axolotl] and it's derivatives which are used by most SM protocols.
However, the requirement of PFS and PCS laid out by the MLS specificzation for a SGM protocol has introduced a novel area of research, as the double-ratchet-based algorithms do not directly map to multi-party communication.
Indeed, these MLS security guarantees have been the cheif focus of reseach related to MLS and it's iterative develompent.
A trival construction exists by utilizing a bidirectional SM protocol, and forming a fully connected graph of all SGM participants.
However, it is obvious that this trivial construction's control mesaasges scale quadratically in the size of the communication group whenever the key argeement requires an update.
Maintaining key agreement with the trival construction is not efficient.

Considering the scope desired protocol constructions, MLS also lays out efficiency goals for implementing protocols with respect to the size of the messaging group.
Three key efficiency distinctions which MLS requires are that the number of control messages should be linear in group size, the size of control messages should be sub-linear in group size, and that group sizes up to 50,000 should be supported.
Taken in it's entirely, the framework provided by MLS is a foundational piece of acheiving SGM with well understood efficiency, security guarantees, and protocol design.

## TreeKEM

The construction of scalable MSL protocols remains an area of open and active research, though the "openness" of this area closes each year.
There currently exist two proposed protocols which meet the definition of MLS with various levels of security proofs as well as efficiency with respect to group size.
The first is Asynchronous Ratcheting Tree (ART) [@cohn2018ends] described in 2018.
The second is TreeKEM [@bhargavan:hal-02425247] similarly conceived in 2018, but formally described in 2019.
The Internet Enginnering Task Force has put it's support behind the TreeKEM protocol along with many other corporate and government sponsors.
Consequently, research directed towards ART has stalled while developments for TreeKEM and it's derivatives have progressed rapidly.
This work will mostly ignore ART and instead focus on the TreeKEM avenue of research.

It is worth noting the relationship between the definitions exoplore thusfar.
Secure Group Messaging (SGM) is a description of the high-level use case.
The MLS specification is standardization which protocols may conform to and which satisfies the SGM use case.
Both ART and TreeKEM are cryptographic protocols which conform to the MLS specification.
There is a clear subsetting relationship between these abstract concepts illistrated in \ref{fig:venn-protocols}, and in future descriptions the layer of abstraction from which a definition was defined may be elided.

![Relationship between Secure Group Messaging, Message Layer Security, and TreeKEM \label{fig:venn-protocols}](png/venn-protocols.png){width=40%}


## Forward Secrecy

Forward Secrecy (FS) is a desireable security guarantee which offers protection in the case that a protocol's long-term secret key(s) are compromised.
PFS has been used in bidirectional key agreement communication protocols, including Transport Layer Security (TLS) (CITE) protocols such as OpenSSL (CITE), as well as SM protocols such as the Signal Protocol (CITE).
While the definition of FS has been explored and made rigourously clear for bidirectional key agreement protocols, the notion of FS requires extension in the multi-directional MLS specification.
The notion 

> If the state of any group member is leaked at some point, all previous update secrets remain hidden from the attacker.

## Post Comprimise Security

The specific definition of the last two security guarantees within a SGM context will be expanded upon in the following sections.


### Agent Environment

A communication group is a set of two or more agents using multiple devices to engage in secure communication.
The existence of an Authentication Service (AS) and a Delivery Service (DS) are required, though these do not need to be the same provider, nor do they need to be centralized.
To initialize a group, members to connect a service provider(s) which transmits the requisite credentials and values to for authentication of and encryption between group members.

Subsequently, group members exchange messages with a total ordering and maintain continuous group key agreement.
Additionally, a group can add or remove members, or reset their encryption continuous key agreement; each of which begins a new encryption ``epoch.''
Forward Secrecy and Post Compromise Secrecy are delineated in epochs, ensuring message ciphertexts sent before the current epoch are not recoverable if the current epoch's cryptographic material is compromised by one or more group members.


## Continuous Group Key Agreement

In the two party case, a general notion of Continuous Key Agreement has been used to provide robust security guarantees such as forward secrecy and post-compromise security.
For SGM, this general definition has been extended to Continuous \emph{Group} Key Agreement (CGKA) which is often used as lemma to derive proofs for some of MLS security guarantees.
	
A naive construction of SGM exists by establishing a bidirectional SM channel between each pair of group members.
This construction, can provide the same security guarantees under some conditions to the entire group's communication.
However, we can exclude considering the robustness of the security guarantees this naive construction provides because it fails to meet the scalability requirement of MLS.
In general, the number of control messages to maintain CGKA does not increase linearly with group size.
Groups exceeding $2^8$ strain this construction in practice, while MLS targets efficiently handling groups up to roughly $2^{16}$ members.
There does not yet exists a cryptographic protocols for adding and removing participants while provably maintaining all the security guarantees of MLS that is simultaneously scalable.




### Public Key Infrastructure
	
The aforementioned authentication service is required support use as a Public Key Infrastructure (PKI) entity, assumed to have a specific set of functionality to facilitate TreeKEM.
The AS acting as PKI should support:
	
		
  - $get\_pk : ID \to (ID^\dagger, SK^\dagger, PK)$\\
		Where anyone can request a ``fresh'' public key for a user with the supplied $id$, and receive back a public key $pk \in PK$ and the PKI records $(id, sk, pk)$.	
  - $get\_sk : ID \to \text{Maybe}(SK)$\\
		A user with $ID$ can request from the PKI if there exist any keys associated with them.
		After authenticating with PKI, if there exists one or more keys associated with $id$, the PKI provides the authenticated user with the recorded secret keys $sk \in SK$.

	The existence and utilization of the PKI described above used in security proofs for TreeKEM.
	In such proofs, any user's call to $get\_pk(id)$ will also supply the attacker with $(pk, id)$.
	This is based on the assumption that the attacker can correlate network traffic and requests to group members, providing stronger and more realistic security guarantees.

	

## Security Games

## Related Work


This work will predominantly forcus on verifying PFS and PCS