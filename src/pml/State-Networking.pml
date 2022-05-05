#ifndef IMPORT_SPEC_NETWORKING
#define IMPORT_SPEC_NETWORKING


#include "State-Global.pml"
#include "Parameterized-Constants.pml"
#include "TreeKEM-v1.pml"


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
local bool commitmentRequired = false;
local bool forcedPlay = false;
local bool revealRoot = C > 1;


/********
    *
    * Inline utilities for after move updates:
    *   - messaging_move
    *   - post_play_poll
    *
********/


/****
  *
  * The inline definition is used by the security game moves:
  *   - insert_member (Oracle ADD)
  *   - remove_member (Oracle RMV)
  *   - oblige_update (Oracle UPD)
  *
  * Modifies global variable(s):
  *  - membership
  *  - abstract "attacker knowledgebase"
  *
  * External result variable(s):
  *   - absentees
  *   - attendees
  *   - groupDyad
  *   - groupFull
  *   - groupMost
  *
****/
inline messaging_move ( e, inviter, insert, remove )
{
    d_step
    {
        leadership[e] = inviter;
        unsigned subject : BITS_USERID = NONE;
        d_step {
            if
            :: insert != NONE -> subject = insert; membership[insert] = true
            :: remove != NONE -> subject = remove; membership[remove] = false
            :: else
            fi
            take_attendance ();
        }
        attacker_study_message( e, inviter, subject );
    }
}


/****
  * External result variable(s):
  *   - commitmentRequired
  *   - forcedPlay
  *   - revealRoot
  *   - triviality
  *   - unsafeIDs
****/
inline post_play_poll ( e )
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
        revealRoot = !challenge[e] && (e != FINAL_EPOCH) && attackerKnowledge[e].node[ROOT] == NodeUnknown;
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
inline take_attendance ()
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


/****
  * External result variable(s):
  *   - candidateCorruptibles
****/
inline candidates_for_corruption ()
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
inline candidate_corruption ( id )
{
    // The corrupted user must not previously been instructed to hoard!
    // Violates the "Safety Predicate SAFE" described in Alwen 2020.
//    candidateCorruption = hoarding[id] == NEVER && membership[id] && attackerKnowledge[epoch].node[LEAF+id] == NodeUnknown
    candidateCorruption = membership[id] && attackerKnowledge[epoch].node[LEAF+id] == NodeUnknown
}


/****
  * External result variable(s):
  *   - candidateHoarders
****/
inline candidates_for_hoarding ()
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
inline candidate_hoarder ( id )
{
    candidateHoarder = hoarding[id] == NEVER && membership[id]
}


#endif /* IMPORT_SPEC_NETWORKING */
