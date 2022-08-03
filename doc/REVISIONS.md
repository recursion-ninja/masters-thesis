Revisions
=========


# Round 2

##  Dietrich

1.  > This requires a reference for each secure messaging program:
    >
    > "Secure Messaging is supported by a variety of services [Muj17] including ChatSecure, CryptoCat, Cyber Dust, Cyphr, Facebook Messenger, G Data Secure Chat, Gajim, GNOME Fractal, Google Allo, Haven, Kakao Talk, Line, Element, Signal, Silence, Silent Phone, Skype, Telegram, Viber, WhatsApp, and Wickr, Wire."
    >
    > For every single one of them.
	Note: Added citations
	Edit: 5f43fc9463e450185bfc5e2dc885cce3cedba323


2.  > Comparison to Broadcast Encryption, just for proper context, as discussed during the defense.
    Note: Added paragraph in Section 2.1 "Secure Group Messaging"
	Edit: 57786585b82e64dbd5f7d09f4c13a9fc44ef9007


3.  > It's still not obvious to me why AMNH computing resources were used for this project, rather than any at CUNY.
    > And what about projections for hardware resources and scalability to the original goals, as we discussed?
	> What would be needed? 
	> Where is that described, in scientific (or even engineering) terms?
    Note: Expanded Section 6.3 "Scalability Limits," added Table B.8
	Edit: a87b2d4ba5788dfc220897f83dc8a5c14fd2b8cd


##  Shankar


1.  > I remember talking about this but not the conclusion. Is there a reason why you didnt explicitly say whether the attacker can be a group member? Its OK if you had a reason, but just checking.
    Spot: Page 21
	Note: Yes, there is a reason to forbid an attacker from being a group member, but it's a bit nuanced. Essentially, the CGKA security game assumes the adversary is not a group member and uses that assumption in the way it defines the FSU property. It can be finnesed to allow the adversary to be a group member, but I'd rather keep things simple (at this point).
    Edit: None
   
2.  > Doesnt parse (to me)
    Spot: Page 24
    Edit: 0cbdcd894c2370ade72254801956fd2244fa778e

3.  > Still doesnt parse to me
    Spot: Page 29
	Note: Rephrased sentance, forming an explicit list. 
    Edit: 5e91ba2be1533cf7401ac35bd7ad390c4ac2a02e

4.  > (thats what CSP stands for)
    Spot: Page 32
    Edit: 1d52a57842a29750c27c5302d4231ff428f80323

5.  > Dont open up this can of worms (in case an external person reads it), unless its important somewhere
    Spot: Page 32
    Note: I omitted the indicated sentance.
    Edit: 737cc89793585e948f101538f6c34a75184b9566

6.  > None of these are appropriate.
    > CGH is about LTL MC using a CTL symbolic model checker.
    > BCCZ99 is the paper that introduced BMC (we talked about it), not about explicit state model checking as conventionally refered to.
    > BRS is conversion algorithms.
    > Use SPIN or Ed Clarke etal book on MC (covers all types of MCs).
    Spot: Page 32
    Note: Substituted references with Edmund Clarke's "Model Checking" book
    Edit: 


---


# Round 1

## Committee


1.  > Rephrase problem to better reflect what was achieved, and not just the current lofty goals.
    Note: Reworked Introduction, Results, and Conclusion to contextualize work acheived, not work attempted.
    Edit: `b3fb1229293ce3e0d889cb98c55ea9dace3d23ea`


2.  > Be more explicit on what you did, your contribution in the big picture, what you would do next in this regard, where you are going with this.
    Note: Moved all hypothesis verification language to conclusion
    Edit: `b3fb1229293ce3e0d889cb98c55ea9dace3d23ea`


3.  > Projections on the gap between what was done and what would be needed for the lofty goals. Where possible, include estimates of resources that would be needed.
    Note: Expanded scalability section, adding table and figure of extrapolated run-time projections
    Edit: `b3fb1229293ce3e0d889cb98c55ea9dace3d23ea`


4.  > There was a concern about why you used AMNH instead of a more public source. I see the mention in the acknowledgements, but make sure you also explicitly say that you used their cluster and what the specs are.
    Note: Added culster specifications within Verification Observations
    Edit: `b3fb1229293ce3e0d889cb98c55ea9dace3d23ea`




##  Dietrich

1.  > The bibliography needs some editing, so please make some effort to fix this. There are way too many occurrences to list here, but I'll mention a few examples/types of what is off

    a)  > There are duplicate/incomplete entries
        Note: I located and removed duplicate entries. I also retreived more BibTex information to remedy incomplete entries.
        Edit: `3aeb27c31b64f55a64e2b9f9256e032a10d54904`
    

    b)  > Conference and workshop papers should be properly cited
        Note: Added "in Proceedings of" prefix to confrence and workshop citations.
        Edit: `3aeb27c31b64f55a64e2b9f9256e032a10d54904`

    c)  > Capitalization should be honored and set properly: pki->PKI, iot->IoT and similar.
        Note: Corrected formating issue which broke capitalization
        Edit: `3aeb27c31b64f55a64e2b9f9256e032a10d54904`


2.  > New/introduced concepts should be cited/referenced at the beginning of the paragraph. For example, you introduce the idea of a 'Security Game' on page 19. Where does this terminology come from? There should be a citation right then and there. You then even spend an entire paragraph/section on Security Games without any such citations.
    Edit: `d0d1cd830458cd40553796971ddb677a876e72fe`


3.  > A better/quick summary of other modeling/analysis approaches, as in it's not just BAN Logic and then Model Checking. There should at least be short references to classic approaches beyond BAN, i.e. works by Catherine Meadows, Gavin Lowe, Bill Roscoe, and Peter YA Ryan, or even Iliano Cervesato.
    Edit: `bed960d154ef5999e8aa316904d61d0fe78527b7`

4.  > An editorial pass: too many of "it's" -> "its" instances at first glance in the main text. Spelling and grammar checks would be great, too.
    Edit: `aae5f94f0b86352914edf205463a07fcc40a105d`


5.  > Some more references you should consider
    Edit: `b3399037dcc85f60716d677fe6922f99f998d296`



##  Shankar

1.  > Some say that one should not use "novel" on themselves.
    Spot: Title Page
    Edit: `2e0d6a3e69205747e9bbca5e019693ba3034443e`
    

2.  > Generally, you often state your thought processes for doing something
    Edit: `f6f35cad8bbac5ededdf4f0dee70879b927e6f02`  
    Spot: Title Page
    

3.  > All footers are cutoff at my end (both acroread and xournal)
    Spot: Title Page
    Edit: `f538870060a894b702cc4b39070d3a2c9c7ab9fc`
    Repo: `https://github.com/recursion-ninja/hunter-thesis-class`
    

4.  > Does Hunter allow color (as in your footers)?
    Spot: Title Page
    Note: *Does not explicitly permit or prohibit colors*
    Edit: None
    

5.  > Many of these seem gratuitous
    Spot: Page 9
    Note: Intelligently pruned
    Edit: `096c439220bc68b17ce343fbd33392cb1e11f9a6`


6.  > I dont know myself but wikipedia says SM must be server based while you dont seem to imply that.
    Spot: Page 9
    Note: Added a comment about mediation services
    Edit: `6f351e635a1b1b257975c6458d77144cb3f46f56`


7.  > Do you mean attack or attack type (or vulnerablity)?
    Spot: Page 10
    Note: Standardized language; vulnerability is the most appropriate term
    Edit: `c6d77b3c5a5d24eab0a5bb53ce6e42c51864ad9b`

8.  > Is broadcast a better word?
    Spot: Page 12
    Note: Standardized language; Yes, I beleive so
    Edit: `62f46b8fc7a5570a2ebb59f2914ff14ffa645896`


9.  > Add qualifier here (currently sounds like a modification of previous sentence)
    Spot: Page 12
    Edit: `0b837157ae688823555e759b00f452730af137fc`


10. > Does IETF say these are the only 5, or the minimum 5, or something else? Later you use the word "update". Which of these ops does that refer to?
    Spot: Page 12
    Note: Added missing update requirement
    Edit: `949279cf1f599072dfb2e18179e0db453fda25ec`


11. > Do AS/DS have limits (eg, buffer size)?
    Spot: Page 13
    Note: Expanding description of AS & DS.
    Edit: `8a977bf3fb47d36d75620ce66be748fef4b72b6b`


12. > How about attacker as DS
    Spot: Page 13
    Note: Attacker's use of the `deliver` oracle is strong enough
    Edit: None
    

13. > Expand
    Spot: Page 13
    Note: This was an artifact of using abreviations within figure captions
    Edit: `678096f9a8fd3083bb03099c6a0710b226361a36`
    

14. > Earlier, you define SM to be biderectional. Assuming so, do you mean to put () around bidirectional?
    Spot: Page 13
    Note: Yeah, it was meant as a reminder. I just removed it.
    Edit: `d4b8dc93265fde741239ed58618c7f6d5a533ab2`
    

15. > I dont understand point of this paragraph. This algo is the data structure for the protocol? Or a way
to prove its correctness (I think former)? Also, is it really trivial since the graph is arbitrarily large or
infinite depending on data structure vs proof?
    Spot: Page 13
    Note: Reworked the paragraph as an introduction to protocol scalability issues
    Edit: `75ae80176add4303cb5ad51cc3709e36c36549ad`


16. > commas? or rephrase
    Spot: Page 14
    Note: Reworked the sentance
    Edit: `b1088cb3a2a9eba5f4586f4d044ab0dfd5f851bd`


17. > What happens if >50K users?
    Spot: Page 14
    Note: Commented on upper bound
    Edit: `dcc5c50a86e6b7278d78923ff05ec9b9f5adfc89`


18. > I think you want a word other than formally (in the context of your thesis)
    Spot: Page 14
    Edit: `c62603d848290bee7115f37207b80ca42dda3cc5`


19. > You listed 5 in 2.1 (are you conflating CGKA ops?)
    Spot: Page 14
    Note: Fixed above
    Edit: `8b5c331b4278384b5bba5356703ea6350415f930`


20. > This needs to be defined, perhaps earlier, since I think non-crypto people dont know this.
    Spot: Page 14
    Note: Introduced ealier in 2.2
    Edit: `0911d08e89a9658a4f00195627c998a05279d53e`


21. > expand/define
    Spot: Page 15
    Edit: `9dfade771525350565fad709c3563380cb953a57`


22. > replace "the member" with "member pk_0"
    Spot: Page 16
    Note: Done, but with v_0
    Edit: `e110740496c8940f8db2d4b7d9fae550f266ec52`


23. > Are there constraints (eg, timing) on how this update is done? Do removed cousins use their old public keys until whenever?
    Spot: Page 16
    Note: Added concurrency/timing commentary
    Edit: `95e2925923343053ae881cc95d92d4af49e1649f`


24. > Are we assuming 100% reliable (and infinitely fast?) control messages?
    Spot: Page 16
    Note: Noting concurrency, adding image
    Edit: `948ca5d75779c770b22d4bd2eb43d924296608a3`


25. > Does completing mean the entire tree has been traversed?
    Spot: Page 17
    Note: Added in #24
    Edit: `948ca5d75779c770b22d4bd2eb43d924296608a3`


26. > What if member 2 wants to add a member before getting the control message that member 1 wants to (and 1's add is still being processed)?
    Spot: Page 17
    Note: Covered in #24/#25


27. > Minor, but you never expanded FSU before here
    Spot: Page 17
    Note: Artifact of abreviation command(s)
    Edit: `02000c053b02bd2c2c4c580f166cea9a338b7cdc`


28. > Is the attacker a group member?
    Spot: Page 18
    Note: Added in future work
    Edit: `20b3c8b8e40ae8da929a5075b9b1f939ea7c2019`


29. > Whats an update (see earlier comment)
    Spot: Page 18
    Note: Changed language to "shared key" and "update instructions"
    Edit: `fc0e36e4fe3077de5e278167fb132a2b28edde00`


30. > I dont understand this sentence. Doesnt sec depend on how you use these, rather than the existence of these? How can some function signatures be a lemma?
    Spot: Page 18
    Edit: `0c0ab312d74ba45902e647793cc509609772a50c`


31. > OK but I would probably define/list \Gamma (and all sets). Some (like U/W) arent obvious til later.
    Spot: Page 18
    Edit: `865d613d6b1e8ca82f6c96a688ff6e59f87350d7`


32. > Do you mean notably or "in particular"
    Spot: Page 19
    Note: Rephrased
    Edit: `0728c3ba073d3c719068bdb622e3df3b039068c8`


33. > Are these functions required to be atomic (to ensure FSU/PCS)?
    Spot: Page 19
    Note: Kinda yes. Clarified.
    Edit: `35ef53897d8d635309a2482852d5b1ca8f59d750`


34. > After completion of proc?
    Spot: Page 19
    Note: Yes. Clarified.
    Edit: `478c192c81932393377e48681c3db65c8610a26f`


35. > Are there timing constraints to prevent (for example) every member being in a different epoch? Or some kind of join? If this is enforced by DS, I didnt see anything above that implied it conclusively.
    Spot: Page 19
    Note: Yes. Clarified.
    Edit: `4c4a4876bd0293a7f189ad76f3bbe1639e549aea`


36. > violates or can cause a violation of?
    Spot: Page 20
    Edit: `14448880827c33e81e64fdaac30c026479708bad`


37. > Rephrase entire sentence
    Spot: Page 20
    Edit: `40bc04b37c57e9286946b984c4ab96ea7b96666a`


38. > I think you are saying the adversary (but not a member) can use any of these 10 ops?
    Spot: Page 20
    Note: Yes
    Edit: `e787778225e3c18e626e9aadf4830cbd456e0c46`


39. > Please add English describing each of these in <10 words (eg, ": send blah message to foo")
    Spot: Page 20
    Note: Done
    Edit: `cd201ce4eff5d48dd01c1b3e76ed75c8bbbe13a7`


40. > Sounds like intuitively modifies wrappers. Rephrase.
    Spot: Page 21
    Note: Done
    Edit: `b33d27b7bc513b1e75a7c0a0fb386e6633aab44a`


41. > doesnt parse
    Spot: Page 23
    Note: Rephrased
    Edit: `50ed4b1b023fcb1df2f37f62e418ed51a8d3a7b9`


42. > I dont understand use of word proving but you use it later too
    Spot: Page 23
    Note: Changed to "demonstrates"
    Edit: `ec32a47097ede4ff1eaff169ad0b381fc2466930`


43. > What is this?
    Spot: Page 23
    Note: Explained the triviality guard
    Edit: `86cc0463fee50233abc8c94b11af9415c6a8ce4c`


44. > Subject verb agreement
    Spot: Page 24
    Edit: `a9a1570de091126f8e4f725c8a8d825432018433`


45. > Somewhere towards the beginning of 2, it would be nice to outline point of it all. eg, 'prove that an attacker cant use oracle ops to violate some MLS guarantees' and section 2.X will give ..., section 2.x will give oracle ops, ... I needed to take notes to figure it all out (I hope, correctly) - 2.9 helped a bit but too late (and in more detail); I really mean more of an outline to the chapter and why I care about the sections.
    Spot: Page 26
    Note: I rewrote the last paragraph of the Introduction section, expanding it to describe the thesis trajectory
    Edit: `78931a208720e99b496cb8c09feaca9c9065959d`


46. > Hoa69 is about Hoare logic, not theorem proving. The SPIN world (not SMV) is the origin of MC
    Spot: Page 27
    Note: Updated to more appropriate citations
    Edit: `6bbc20d51f1984bd0c323d3b28b5c0b82bb59cdf`


47. > Cite the false positives and/or incorrectly verified work.
    Spot: Page 27
    Note: Updated citations
    Edit: `ef41db72e7b759c4f1d539422060cbd7cad44856`


48. > Reference tamerin somewhere
    Spot: Page 27
    Edit: `3810710b881b1cc25be2ee9ff9d297e6a2aa71c1`


49. > Too strong. MC is certainly more automated, but many would argue that its only used for easy problems. I would weaken statement.
    Spot: Page 27
    Edit: `d7f95ac15ffe57381fd761f7b3d9886c2e9e5404`


50. > OK, but not really true strictly speaking. Its an LTS, which is one specific type of FSM
    Spot: Page 27
    Edit: `24855cacb8ee522e02a3feb9096189ff2a807f20`


51. > Is (12,12,8) the min size or just the size they found? Clarify
    Spot: Page 28
    Note: Elaborated
    Edit: `22f82187a690d5eedd1b260b1b7f4e86a6f66b46`


52. > What is the key magic that happens for (12,12,8) to cause problems?
    Spot: Page 28
    Note: The precise magic is not apparent to me.
    Edit: None

53. > Doesnt parse
    Spot: Page 28
    Note: Sentance fragment got cut out at some point...
    Edit: `e9d284b8e9a9693cf73976e41cee990f574d61bb`

54. > Is the current App B table the updated version? If so, need more justification/discussion since you dont get to T=12
    Spot: Page 28
    Note: Moving to results section
    Edit: `8a4e134f52cd391e07b103ac32cd308787b03536`

55. > Not correct term, but not sure what you mean to say
    Spot: Page 29
    Note: I meant "constructive" in the mathematical sense as opposed to "exeistential," i.e. the verification failure produces an interpretable counter-example instead of just stateing that one exists
    Edit: `8ee8a316b32480b07a29b47ac86845e1a3d1b997`


56. > Not true, could also be artifact of abstraction
    Spot: Page 29
    Edit: `87b0efda7c8cc3908fda5a910ca0ce96810b5cd7`


57. > Is this saying anything different from end of previous subsection?
    Spot: Page 29
    Note: Not really, backreferenced
    Edit: `aeb9b001afefa260bc64b3ff7617539588e8c6f8`


58. > I'm fine with this, but others may request more explanation
    Spot: Page 30
    Note: Got it
    Edit: None


59. > You dont mention the major reason for promela - spin!
    Spot: Page 30
    Note: Reordered sections
    Edit: Prior


60. > Rephrase. Several ambiguous readings exist depending on what "only" modifies
    Spot: Page 31
    Edit: `023e13d299c7391551e8e574ad55c215e48150cd`


61. > Do you mean interleaving?
    Spot: Page 33
    Edit: `a34d9828b855f4f29ed20ec62bf8172564af8000`


62. > General stylistic comment: you use lots of gerunds throughout section; I personally think it sounds better minimizing them.
    Spot: Page 33
    Edit: None


63. > SPIN has a book too. Not sure if you want to use that instead of Hol97, you decide. But why is God90 an appropriate ref in this context?
    Spot: Page 34
    Edit: `80fdf5e0b0dd751656616f07b75f77beab62bdc2`


64. > I have no idea whether shannon did this, but why not the MC partial order reduction papers here?
    Spot: Page 35
    Edit: `c1558fb64f855d3a17f5e4fb5719c6202d7c59f6`


65. > Which portion is that?
    Spot: Page 35
    Note: Previously rephrased


66. > Fig 4.1 needs explanation. I doubt readers can understand it.
    Spot: Page 36
    Note: Figure moved and contextualized in a new paragraph
    Edit: `2a00c7c655b33aa0ef93713eae610b288e7eaeb7`


67. > I assume real systems only have bounded queues? If so, what are bounds and why not use that?
    Spot: Page 37
    Note: Yes, added a note
    Edit: `e98a4c13d51fe7c0ad268c22f55354a8fd0f1aa8`


68. > What is ordering relation of DS, given timing issues across agents
    Spot: Page 37
    Edit: `f9bdbde41a61b3f7939b209d20d6ae3ce837625c`


69. > What is your goal in this ref? This is old and not generally used for timed systems (timed automata is 'the answer'
    Spot: Page 37
    Note: Added reference and introduction to timed automata
    Edit: `957caddb084d9130ed1fc47f36477817f0334b54`


70. > Is this a transition graph or a system architecture?
    Spot: Page 38
    Note: High-level view of components of the transition graph. Improved figure description.
    Edit: `c9d3ddeb0bc3a357b17f9d177e36eeda980512e6`


71. > Depends on LTL property, but wouldnt the verification of the t+1 case need to verify the t case anyway? If so, memoization wont help.
    Spot: Page 38
    Note: Elaborated on memoization possibility
    Edit: `9b26bae107b4c97ab81faa91edf308d0b1684768`


72. > I'm not following something. How can you restrict what \cal A does?
    Spot: Page 39
    Edit: `ea7f6ad3bb91ac0b981672db1260a1544ba1ee36`


73. > Bad notation, doesnt make sense as written (also, any constraints on i,j?)
    Spot: Page 40
    Edit: `9eca95b351aa1fd9e2028a38cc93077e1abbe039`


74. > Is this your notation or a standard?
    Spot: Page 40
    Edit: `9eca95b351aa1fd9e2028a38cc93077e1abbe039`


75. > I need to re-review above paragraph (maybe all 4.1.2) after rewrite. I see potential issues.
    Spot: Page 40
    Edit: `9eca95b351aa1fd9e2028a38cc93077e1abbe039`


76. > What does it mean to corrupt a group member?
    Spot: Page 43
    Note: Clarified in caption
    Edit: `df08e0c30707f66495607db26b9743e8a1603e5f`


77. > Is this a technical term or just informal
    Spot: Page 44
    Edit: `b6b27fbc389cef67618af74979354676a9b60b69`


78. > Are these independent or dictated by other considerations?
    Spot: Page 45
    Note: Used for unsigned values in Spin require a bit-width specification.
    Edit: None


79. > Is this still true given what you found about Spins state space encoding?
    Spot: Page 45
    Note: Yes, using unsigned values is helpful and having explicit missing values are neccissary for comparisons
    Edit: `c53cdf0e2300d2047e7b1eb869c5efba38edd18a`


80. > State each LTL wff as one English phrase/sentence too
    Spot: Page 55
    Edit: `265ad31d99fa7ff980a81063b0ea655223020c2b`


81. > What does validity checks have to do with partial order reduction?
    Spot: Page 57
    Edit: `02e0cfb5ac4e6226fdc0c3f1f8b97b2605f49744`



82. > Not sure, but I thought this was only for Spin's statistical model checking (ie, simulation)? Can you tell me where to look (I googled but dont see it at first glance).
    Spot: Page 59
    Note: See changelog on GitHub: https://github.com/nimble-code/Spin/blob/master/Doc/V5.Updates#L185
    Edit: None


83. > Doesnt parse
    Spot: Page 60
    Edit: `ad12a311bad8fa280ea09f310204a3a705b62857`


84. > OK, I guess you answer here what I asked earlier, but I think you should still state earlier what was claimed
    Spot: Page 64
    Note: Moving entired hypothesis testing discussion to Conclusion Chapter, no prior mention
    Edit: None


85. > I think giving a conclusive proof of this is paper worthy?
    Spot: Page 64
    Note: I beleive it would be publishable
    Edit: None


86. > [20] needs to be tagged differently.
    Spot: Page 75
    Edit: `472438e07f1dac78bd105610d058abe60074e2e0`


86. > Tags aren't sorted here. Use different bibtex option (I actually thought it sorted on tags)?
    Spot: Page 75
    Edit: `021d7c8f2cedb18264111c62f7e0bdd8a75f9835`
    Repo: `https://github.com/recursion-ninja/hunter-thesis-class`


87. > Your reverse citations are not standard. Check if this is allowed.
    Spot: Page 75
    Edit: `421b42a0fd80ecac7c32d52c0c75474ec72e7e08`
    Repo: `https://github.com/recursion-ninja/hunter-thesis-class`

