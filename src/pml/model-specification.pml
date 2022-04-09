#include "parameterized-constants.pml"
#include "global-state.pml"
#include "TreeKEM-v1.pml"


/********
  *
  * Advantage:
  *
  * In the following, a (`t`, `c`, `n`)-attacker is an attacker `A` that runs in time at most `t`,
  * makes at most `c` challenge queries, and never produces a group with more than `n` members.
  * The attacker wins the CGKA security game if they correctly guesses the random bit `b` in
  * the end and the safety predicate `P` evaluates to true on the queries made by the attacker.
  *
********/


/****
  *
  * Global state of verifying used for LTL.
  *
****/


/********
    *
    * Saftey Predicate (Triviality):
    *
    * Consider the following succession of attacker moves in the CKGA game.
    * We will call each move a "query," as to remain in line with the literature.
    * The attacker performs a non-empty sequence of queries to the oracles.
    * The sequence then ends with an additional query to a special "challenge" oracle.
    * By construction the sequence has at least 2 queries.
    *
    * Consider the function
    *     whichEpoch(q) : query -> Natural
    * This function returns the epoch during which the query was made.
    *
    * Now consider the array `Q` containing the sequence of queries.
    *
    *     triviality ( Q ):
    *         for  (i,j) s.t. Q[i] = corrupt(ID) and Q[j] = challenge
    *             if
    *                 whichEpoch(Q[i]) <= whichEpoch(Q[j]) AND there does not exist `k` s.t.
    *                     0 < whichEpoch(Q[i]) < whichEpoch(Q[k]) <= whichEpoch(Q[j]) AND
    *                     Q[k] = update(ID) or Q[k] = remove(ID)
    *             then
    *                 return FALSE
    *             done
    *             if
    *                 which(Q[i]) > whichEpoch(Q[j]) AND there exists `k` s.t.
    *                   whichEpoch(Q[k]) <= whichEpoch(Q[j]) AND Q[k] = hoard(ID)
    *             then
    *                 return FALSE
    *             done
    *         end
    *         return TRUE
    *
    * This predicate is described as the "Safety Predicate" `safe` in Alwen 2020.
    * We use `triviality` as a synonym from `safe` because the term "safety predicate has
    * a different connotation in  formal methods nomenclature.
    *   
********/

/****
  * Does a trivial attack exist? i.e, does the SAFE predicate hold?
  *
  * SYNC: Updated by `post_move_poll`
****/
local bool triviality = false; 


/****
  * Has the CGKA game end?
  *
  * SYNC: Bit flipped IFF at the end of `init`
****/
local bool concludedCGKA = false;


/****
  *
  * Global state of derivative variables.
  *   (Each can is defined in terms of the CGKA global state variables)
  *
****/

// Group Composition
local unsigned attendees : BITS_USERID = N;
local unsigned absentees : BITS_USERID = 0;
local unsigned groupMost : BITS_USERID = 0; // The maximum member ID during any past/present epoch.
local bool     groupDyad          = false;
local bool     groupFull          = false;

// Protocol State
local bool forcedPlay = false;
local bool revealRoot = C > 1;


/********
    *
    * Global state priniting utilities:
    *
    *   - print_challenges
    *   - print_group_composition
    *   - print_membership
    *   - print_protocol_state
    *   - print_user_hoarding
    *   - print_user_unsafe
    *
********/


inline print_challenges()
{
    d_step {
        printf("\n\tChallenges:");
        unsigned t : BITS_EPOCH;
        for ( t : FIRST_EPOCH .. FINAL_EPOCH )
        {
            if
            :: challenge[t] -> printf("\n\t    [\tTrue\t]");
            :: else         -> printf("\n\t    [\tFalse\t]");
            fi
        }
        printf("\n");
    }
}


inline print_group_composition()
{
    d_step
    {
        printf("\n\tattendees \t%d", attendees );
        printf("\n\tabsentees \t%d", absentees );
        printf("\n\tgroupDyad \t%d", groupDyad );
        printf("\n\tgroupFull \t%d", groupFull );
        printf("\n\tgroupMost \t%d", groupMost );
    }
}


inline print_membership()
{
    d_step {
        printf("\n\tMembership:");
        unsigned p : BITS_USERID;
        for ( p : FIRST_USERID .. FINAL_USERID )
        {
            if
            :: membership[p] -> printf("\n\t    [\tTrue\t]");
            :: else          -> printf("\n\t    [\tFalse\t]");
            fi
        };
        printf("\n");
    }
}


inline print_protocol_state()
{
    d_step
    {
        printf("\n\trevealRoot \t%d", revealRoot );
        printf("\n\tforcedPlay \t%d", forcedPlay );
        printf("\n\tunsafeIDs  \t%d", unsafeIDs  );
    }
}


inline print_user_hoarding()
{
    d_step {
        printf("\n\tHoarding since:");
        unsigned p : BITS_USERID;
        for ( p : FIRST_USERID .. FINAL_USERID )
        {
            if
            :: hoarding[p] == NONE -> printf("\n\t    [\tNONE\t]")
            :: else                -> printf("\n\t    [\t%d\t]", hoarding[p])
            fi
        }
        printf("\n");
    }
}


inline print_user_unsafe()
{
    d_step {
        printf("\n\tRequired healing:");
        unsigned p : BITS_USERID;
        for ( p : FIRST_USERID .. FINAL_USERID )
        {
            if
            :: unsafe[p] -> printf("\n\t    [\tTrue\t]");
            :: else      -> printf("\n\t    [\tFalse\t]");
            fi
        }
        printf("\n");
    }
}


inline print_global_state()
{
    d_step
    {
        printf("\n-=-=-=-=-=-=-=-=-=-=-=-\n-=-  GLOBAL  STATE  -=-\n-=-=-=-=-=-=-=-=-=-=-=-\n");
        print_challenges();
        print_membership();
        print_user_hoarding();
        print_user_unsafe();
        print_group_composition();
        print_protocol_state();
        print_attacker_knowledge()
    }
}


/********
    *
    * Inline utilities for after move updates:
    *   - post_move_poll
    *   - take_attendance
    *
********/


/****
  * External result variable(s):
  *   - commitmentRequired
  *   - forcedPlay
  *   - revealRoot
  *   - triviality
  *   - unsafeIDs
****/
inline post_move_poll( e )
{
    d_step {
        // Refresh "unsafeIDs"
        unsigned remainingEpochs    : BITS_EPOCH = FINAL_EPOCH - e;
        unsigned recoveriesRequired : BITS_USERID = 0;
        d_step
        {
            unsigned n : BITS_USERID;
            for ( n : FIRST_USERID .. FINAL_USERID ) {
                if
                :: unsafe[n] -> recoveriesRequired++;
                :: else
                fi
            }
        }
        unsafeIDs  = recoveriesRequired;

        // Refresh "triviality"
        triviality = unsafeIDs > 0; 

        // Refresh "forcedPlay"
        forcedPlay = unsafeIDs > 0 && unsafeIDs == remainingEpochs;
        printf("\n\tremainingEpochs\t%d\n\tunsafeIDs\t%d\n", remainingEpochs, unsafeIDs);

        // Refresh "revealRoot"
        revealRoot = !challenge[e] && (e != FINAL_EPOCH) && attackerKnowledge[e].node[ROOT] == UnknownNode;
        if
        :: !revealRoot -> skip
        :: else ->
            unsigned challengesUsed : BITS_EPOCH = 0;
            d_step
            {
                unsigned n : BITS_USERID;
                for ( n : 0 .. e )
                {
                    if
                    :: challenge[n] -> challengesUsed++;
                    :: else
                    fi
                }
            };
            revealRoot = challengesUsed < MAX_REVEAL;
        fi

        // Refresh "commitmentRequired"
        bool canHoardMember = false;
        d_step
        {
            unsigned candidateHoarders : BITS_USERID;
            candidates_for_hoarding();
            canHoardMember = candidateHoarders > 0;
    //        printf("\n canHoardMember = %d", canHoardMember);
        }
    
        bool canCorruptMember = false;
        d_step
        {
            unsigned candidateCorruptibles : BITS_USERID;
            candidates_for_corruption();
            canCorruptMember = candidateCorruptibles > 0;
    //        printf("\n canCorruptMember = %d", canCorruptMember);
        }
    
        commitmentRequired = !revealRoot && !canHoardMember && !canCorruptMember
    }
}


/****
  * External result variable(s):
  *   - absentees
  *   - attendees
  *   - groupDyad
  *   - groupFull
  *   - groupMost
****/
inline take_attendance()
{
    unsigned largestID : BITS_USERID;
    d_step {
        unsigned included : BITS_USERID = 0;
        d_step {
            unsigned n : BITS_USERID;
            for ( n : FIRST_USERID .. FINAL_USERID ) {
                 if
                 :: membership[n] -> included++; largestID = n
                 :: else
                 fi
            }
        }
        attendees = included;
        absentees = N - attendees;
        groupDyad = attendees == 2;
        groupFull = absentees == 0;
    }

    if
    :: largestID + 1 > groupMost -> groupMost = largestID + 1;
    :: else
    fi

    d_step
    {
        printf("\n\tattendees \t%d", attendees );
        printf("\n\tabsentees \t%d", absentees );
        printf("\n\tgroupDyad \t%d", groupDyad );
        printf("\n\tgroupFull \t%d", groupFull );
        printf("\n\tgroupMost \t%d", groupMost );
    }
}


/********
    *
    * User ID selection inlines:
    *   - select_corrupted
    *   - select_banisher
    *   - select_exiled
    *   - select_hoarder
    *   - select_joiner
    *   - select_sender
    *   - select_updater
    *
********/


/****
  * External result variable(s):
  *   - corruptedID
****/
inline select_corrupted()
{   atomic {

    unsigned candidateCorruptibles : BITS_USERID;
    candidates_for_corruption();
    if
    :: candidateCorruptibles == 0 -> corruptedID = NONE
    :: else ->
        unsigned selection : BITS_USERID = NONE;
        d_step
        {
            unsigned n      : BITS_USERID;
            unsigned sample : BITS_USERID;
            select ( sample : 0 .. candidateCorruptibles - 1 );
            for ( n : FIRST_USERID .. FINAL_USERID )
            {
                d_step
                {
                    if
                    :: selection == NONE ->
                        bool candidateCorruption;
                        candidate_corruption( n );
                        if
                        :: candidateCorruption ->
                            if
                            :: sample == 0 -> selection = n
                            :: sample != 0 -> sample--
                            fi
                        :: else
                        fi
                    :: else
                    fi
                }
            }
        }
        corruptedID = selection
    fi
}   }


/****
  * External result variable(s):
  *   - candidateCorruptibles
****/
inline candidates_for_corruption()
{
    unsigned remaining : BITS_EPOCH = FINAL_EPOCH - epoch;

    if
    :: unsafeIDs >= remaining -> candidateCorruptibles = 0;
    :: else ->
        unsigned candidates : BITS_USERID = 0;
        d_step
        {
            unsigned n : BITS_USERID;
            for ( n : FIRST_USERID .. FINAL_USERID )
            {
                bool candidateCorruption;
                candidate_corruption( n );
                if
                :: candidateCorruption -> candidates++
                :: else
                fi
            }
        }
        candidateCorruptibles = candidates
    fi
}


/****
  * External result variable(s):
  *   - candidateCorruption
****/
inline candidate_corruption( id )
{
    // The corrupted user must not previously been instructed to hoard!
    // Violates the "Safety Predicate SAFE" described in Alwen 2020.
    candidateCorruption = hoarding[id] == NONE && membership[id] && attackerKnowledge[epoch].node[LEAF+id] == UnknownNode
}


/****
  * External result variable(s):
  *   - banisherID
****/
inline select_banisher( banned )
{
    unsigned selectedID : BITS_USERID;
    select_sender_constrained( banned, false );
    banisherID = selectedID;
}


/****
  * External result variable(s):
  *   - exiledID
****/
inline select_exiled( forced )
{
    unsigned selectedID : BITS_USERID;
    select_sender_constrained( NONE, forced );
    exiledID = selectedID;
}


/****
  * External result variable(s):
  *   - hoarderID
****/
inline select_hoarder()
{   atomic {

    unsigned candidateHoarders : BITS_USERID;
    candidates_for_hoarding();

    if
    :: candidateHoarders == 0 -> hoarderID = NONE
    :: else ->
        unsigned selection : BITS_USERID = NONE;
        d_step
        {
            unsigned n      : BITS_USERID;
            unsigned sample : BITS_USERID;
            select ( sample : 0 .. candidateHoarders - 1 );
            for ( n : FIRST_USERID .. FINAL_USERID )
            {
                d_step
                {
                    if
                    :: selection != NONE -> skip
                    :: else ->
                        bool candidateHoarder
                        candidate_hoarder( n );
                        if
                        :: !(candidateHoarder) -> skip
                        :: else ->
                            if
                            :: sample == 0 -> selection = n
                            :: sample != 0 -> sample--
                            fi
                        fi
                    fi
                }
            }
        }
        hoarderID = selection
    fi
}   }


/****
  * External result variable(s):
  *   - candidateHoarders
****/
inline candidates_for_hoarding()
{
    unsigned candidates : BITS_USERID = 0;
    d_step
    {
        unsigned n : BITS_USERID;
        for ( n : FIRST_USERID .. FINAL_USERID )
        {
            bool candidateHoarder
            candidate_hoarder( n );
            if
            :: candidateHoarder -> candidates++
            :: else
            fi
        }
    }
    candidateHoarders = candidates
}


/****
  * External result variable(s):
  *   - candidateHoarder
****/
inline candidate_hoarder( id )
{
    candidateHoarder = hoarding[id] == NONE && membership[id]
}


/****
  * External result variable(s):
  *   - joinerID
****/
inline select_joiner()
{   atomic {

    unsigned candidateJoiners : BITS_USERID;
    candidates_for_joiner();

    unsigned selection : BITS_USERID = NONE;
    d_step
    {
        unsigned n      : BITS_USERID;
        unsigned sample : BITS_USERID;
        select(  sample : 0 .. candidateJoiners - 1 );
        for ( n : FIRST_USERID .. FINAL_USERID ) {
            if
            :: selection != NONE || membership[n] -> skip
            :: else ->
                if
                :: sample != 0 -> sample--
                :: sample == 0 -> selection = n
                fi
            fi
        }
    }
    
    joinerID = selection;
}   }


/****
  * External result variable(s):
  *   - candidateJoiners
****/
inline candidates_for_joiner()
{
    unsigned candidates : BITS_USERID = 0;
    d_step
    {
        unsigned n : BITS_USERID;
        for ( n : 0 .. groupMost - 1 )
        {
            if
            :: !(membership[n]) -> candidates++
            :: else
            fi
        }
    }

    // Consider adding the next user who has never been a member before...
    // but make the consideration *if and only if* such a user exists.
    d_step
    {
        if
        :: groupMost == N -> skip
        :: else -> candidates++
        fi
    }
    candidateJoiners = candidates
}


/****
  * External result variable(s):
  *   - senderID
****/
inline select_sender()
{
    unsigned selectedID : BITS_USERID;
    select_sender_constrained( NONE, false );
    senderID = selectedID;
}


/****
  * External result variable(s):
  *   - updaterID
****/
inline select_updater( forced )
{
    unsigned selectedID : BITS_USERID;
    select_sender_constrained( NONE, forced );
    updaterID = selectedID;
}


/****
  * External result variable(s):
  *   - selectedID
****/
inline select_sender_constrained ( banned, forced )
{   atomic {
    unsigned candidates : BITS_USERID = 0;

    d_step
    {
        unsigned n : BITS_USERID;
        for ( n : FIRST_USERID .. FINAL_USERID )
        {
            bool senderCandidate;
            sender_candidate( banned, forced, n );
            if
            :: senderCandidate -> candidates++
            :: else
            fi
        }
    }

    if
    :: candidates == 0 -> selectedID = NONE
    :: else ->
        unsigned selection : BITS_USERID = NONE;
        d_step
        {
            unsigned n      : BITS_USERID;
            unsigned sample : BITS_USERID;
            select(  sample : 0 .. candidates - 1 );
            for ( n : FIRST_USERID .. FINAL_USERID ) {
                d_step
                {
                    if
                    :: selection == NONE ->
                        bool senderCandidate;
                        sender_candidate( banned, forced, n );
                        if
                        :: senderCandidate ->
                            if
                            :: sample == 0 -> selection = n
                            :: sample != 0 -> sample--
                            fi
                        :: else
                        fi
                    :: else
                    fi
                }
            }
        }
        selectedID = selection;
    fi
}   }


/****
  * External result variable(s):
  *   - senderCandidate
****/
inline sender_candidate( banned, forced, id )
{
//    bool querryOkay = commitment || !(epochQuerried[id]);
//    bool forcesSafe = (!(forced) && querryOkay) || unsafe[id];
    bool forcesSafe = !(forced)  || unsafe[id];
    bool isAnOption = membership[id] && (id != banned);
    senderCandidate = isAnOption && forcesSafe
}


/****
  *
  * The following methods:
  *   - broadcast
  *   - propogate
  *
  * Are used by the security game moves:
  *   - insert_member
  *   - remove_member
  *   - oblige_update
  *
****/


inline broadcast ( e, sender, subject )
{
    attacker_study_message( e, sender, subject );
}


inline propogate ( sender, insert, remove )
{
    d_step {
        if
        :: insert != NONE -> membership[insert] = true
        :: remove != NONE -> membership[remove] = false
        :: else
        fi

        take_attendance();
    }
}


/********
    *
    * Oracles available to the attacker:
    *
    *   - Corrupt
    *   - Hoard
    *   - Reveal
    *
********/


inline corrupt( memberID )
{   atomic {

    printf("\n> > >\n> CGKA: Game Move = COR %d\n> > >\n", memberID);

    // Learn the secret material of the user in their current epoch
    unsigned upperBound : BITS_EPOCH = epoch;
    unsigned lowerBound : BITS_EPOCH = upperBound;

    // Learn any additional secrets they have hoarded!
    unsigned epochSavedFrom : BITS_EPOCH = hoarding[memberID];
    if
    :: epochSavedFrom < upperBound -> lowerBound = epochSavedFrom
    :: else
    fi

    printf("Corrupting from: %d -- %d\n", lowerBound, upperBound);

    // For each epoch which the member has secrets
    // (this implies that the user was a member)
    // Then the attacker learns the secrets on the direct path
    // between the member and the root node on the LBBT.
    unsigned peek : BITS_EPOCH;
    for ( peek : lowerBound .. upperBound )
    {
        if
        :: !(membership[memberID]) -> skip
        :: else ->
            printf("Passed membership guard!\n");
            unsigned off   : BITS_VERTEX = LEAF;
            unsigned level : BITS_VERTEX = TREE_ORDER + 1;
            do
            :: level == 0 -> break
            :: level != 0 ->
                d_step
                {
                    level = level / 2;
                    unsigned v : BITS_VERTEX = off+memberID;
                    printf("tree level: %d @ %d\n", level, v);
                    if
                    :: attackerKnowledge[peek].node[v] == UnknownNode -> attackerKnowledge[peek].node[v] = KnownNode
                    :: attackerKnowledge[peek].node[v] == UnknownRefs -> attackerKnowledge[peek].node[v] = KnownRefs
                    :: else
                    fi
                    off = off / 2;
                }
                printf("Check Index Post: %d\n", peek);
                if
                :: peek == upperBound ->
                    printf("UPPER BOUNDed %d\n", peek);
                    attacker_updates_knowledge( peek );
                :: else ->
                    printf("Lower Pre %d\n", peek);
                    attacker_copy_epoch_knowledge( peek  );
                    printf("Lower Post %d\n", peek);
                    attacker_updates_knowledge(   peek+1 );
                fi
                printf("Before hand off: %d\n", peek);
            od
        fi
    }
    attacker_check_knowledge( epoch );
    unsafe[memberID] = true;
}   }


inline hoard( memberID )
{
    d_step {
        printf("\n> > >\n> CGKA: Game Move = HOD %d\n> > >\n", memberID);
        hoarding[memberID] = epoch
    }
}


inline reveal()
{
    d_step {
        printf("\n> > >\n> CGKA: Game Move = RVL %d\n> > >\n", epoch);
        challenge[epoch] = true;
        attacker_learn_root( epoch );
    }
}


/********
    *
    * Oracles available to the Group Members:
    *
    *   - Insert Member ( ADD )
    *   - Remove Member ( RMV )
    *   - Oblige Update ( UPD )
    *
********/


// Precondition: joiner is not in the group!
inline insert_member( sender, joiner )
{
    d_step {
        printf("\n> > >\n> CGKA: Game Move = ADD %d %d\n> > >\n", sender, joiner);
        assert(sender < N);
        assert(joiner < N);
        propogate( sender, joiner, NONE );
    }
    broadcast( epoch + 1, sender, joiner );
}


// Precondition: exiledMemeber is in the group!
inline remove_member( sender, exiled )
{
    d_step {
        printf("\n> > >\n> CGKA: Game Move = RMV %d %d\n> > >\n", sender, exiled);
        assert(sender < N);
        assert(exiled < N);
        unsafe[exiled] = false;
        propogate( sender, NONE, exiled);
    }
    broadcast( epoch + 1, sender, exiled );
}


inline oblige_update( sender )
{
    d_step {
        printf("\n> > >\n> CGKA: Game Move = UPD %d\n> > >\n", sender);
        assert(sender < N);
        unsafe[sender] = false;
        propogate( sender, NONE, NONE );
    }
    broadcast( epoch + 1, sender, NONE );
}


/********
    *
    * Attacker moves interacting with oracles:
    *
    *   - play_move_with_commitment
    *   - play_move_without_commitment
    *
********/


inline play_move_with_commitment()
{
    unsigned exiledID : BITS_USERID, banisherID : BITS_USERID, updaterID : BITS_USERID;
    
    atomic
    {
        select_updater(  forcedPlay );
        select_exiled(   forcedPlay );
        select_banisher( exiledID   );
    };

    d_step
    {
        printf("\nEpoch (t) = %d\n", epoch );
        print_global_state()
        printf("\n\texiledID    \t%d",   exiledID );
        printf("\n\tbanisherID  \t%d", banisherID );
        printf("\n\tupdaterID   \t%d",  updaterID );
        printf("\nCOMMITTING!\n");
    }

    do
    // Update
    :: updaterID != NONE ->
        oblige_update( updaterID ); break

    // Remove
    :: !groupDyad && exiledID != NONE && banisherID != NONE ->
        remove_member( banisherID, exiledID ); break

    // Insert
    :: !groupFull && !forcedPlay -> atomic
        {
            unsigned joinerID : BITS_USERID, senderID : BITS_USERID;
            select_sender();
            select_joiner();
            insert_member( senderID, joinerID );
        }; break
    od

    post_move_poll( epoch + 1);
}


/****
  *
  * Attacker moves without advancing the epoch via one of the following oracles:
  *
  *   - Corrupt
  *   - Hoard
  *   - Reveal
  *
****/
inline play_move_without_commitment()
{   atomic
    {
        unsigned corruptedID : BITS_USERID, hoarderID : BITS_USERID;
    
        atomic
        {
            select_corrupted();
            select_hoarder();
        };
    
        d_step
        {
            printf("\nEpoch (t) = %d\n", epoch);
            print_global_state()
            printf("\n\tcanRevealKey\t%d",  revealRoot );
            printf("\n\tcorruptedID \t%d", corruptedID );
            printf("\n\thoarderID   \t%d",   hoarderID );
            printf("\nNON-Committal!\n");
        }

        do
        :: corruptedID != NONE && !forcedPlay -> corrupt( corruptedID ); break
        :: hoarderID   != NONE                -> hoard(     hoarderID ); break
        :: revealRoot                         -> reveal(              ); break
        od
    
        post_move_poll( epoch );
    }
}


/********
    *
    * Initialization inline routines, in order of execution:
    *
    *   - Initialize
    *   - Select Group
    *   - Create Group
    *   - CGKA Security Game
    *
********/


inline CGKA_initialize()
{   atomic {
    d_step
    {
        printf("\n***********************\n* CGKA: Initialize!   *\n***********************\n");

        d_step
        {
            unsigned n : BITS_USERID;
            for ( n : FIRST_USERID .. FINAL_USERID )
            {
                hoarding[n]  = NEVER;
            };
        };
        
        d_step
        {
            unsigned t : BITS_EPOCH;
            for ( t : FIRST_EPOCH .. FINAL_EPOCH )
            {
                challenge[t] = false;
            };
        };

        epoch     = 0;
        unsafeIDs = 0;
        
        concludedCGKA = false;
        triviality    = false; 

        attacker_initialize()
    };

}   }


inline CGKA_create_group()
{
    // Number of members to add
    unsigned sample : BITS_USERID;
    d_step {
        select ( sample : 2 .. N );
        unsigned n      : BITS_USERID;
        for ( n : FIRST_USERID .. FINAL_USERID )
        {
            membership[n] = n < sample;
        };
    }
    printf("\n***********************\n* CGKA: Create Group! *\n***********************\n");

    // Set the "lead" byte to be the first member in the group.
    d_step {
        unsigned id0 : BITS_USERID = 0;
        unsigned ep0 : BITS_EPOCH  = 0;
        propogate ( id0, NONE, NONE );
        broadcast ( ep0,  id0, NONE );
    }
    print_membership();
}


inline CGKA_security_game()
{
    printf("\n***********************\n* CGKA: Begin Play!   *\n***********************\n");


    // Each time the attacker takes a turn, they must decide whether or not to:
    //
    //   1. End the game; under the assumption that the attacker has won.
    //   2. Play a move which will *commit* the group members to advance to the next epoch
    //   3. Play a move which where the group members remain in the current epoch
    //
    // We call selection the options "challenge," "commitment," and "non-committal" moves, respectively.
    //
    // NOTE: option (1), is implicitly the last move in the model

    bool commitmentRequired = false;

    // Loop through all epochs
    for ( epoch : 0 .. FINAL_EPOCH)
    {

        do
        // 1. Play the Challenge Move
        //     The attacker ending the game is implicitly the last move of the model
        //     so it always happens in the last epoch.
        :: epoch == FINAL_EPOCH -> break
        
        // 2. Play a Commitment Move
        //     The attacker *may* play a move which commits to a new epoch...
        //     unless it is the last epoch.
        :: epoch != FINAL_EPOCH -> play_move_with_commitment(); break
        
        // 3. Play a Non-commital Move
        //     The attacker *may* play a move and remain in the same epoch...
        //     unless the attacker has exhausted all indempotent non-comittal moves!
        :: !(commitmentRequired) -> play_move_without_commitment()
        od;

        // After the operation is complete, check to see if the an endgame condition has been reached.
        printf("\nLOOP broken: %d", epoch);
        printf ("\n< < <\n< Moves:   %d\n< Unsafe:  %d\n< < < \n", FINAL_EPOCH - epoch, unsafeIDs);
    }
    epoch = FINAL_EPOCH;
    print_global_state();
}


init
{
    CGKA_initialize();
    CGKA_create_group();
    CGKA_security_game();
    concludedCGKA = true;
}

ltl challenge      { []( (concludedCGKA && !triviality) -> attackerKnowledge[epoch].node[ROOT] != KnownNode) }
//ltl trivial_safety { []( (triviality && epoch <= FINAL_EPOCH) -> attackerKnowledge[epoch].node[ROOT] != KnownNode) }
//ltl game_totality  { <>concludedCGKA }
//ltl attendees_more_than_one { [](attendees > 1) }
//ltl attendees_absentees_sum { [](attendees + absentees == N) }
