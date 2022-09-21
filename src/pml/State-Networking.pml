#ifndef IMPORT_SPEC_NETWORKING
#define IMPORT_SPEC_NETWORKING


#include "State-Global.pml"
#include "Parameterized-Constants.pml"
#include "TreeKEM-v1.pml"


#define CandidateHoarderArray( buffer ) \
atomic { \
    buffer = ( ~( hoarding | startHoard ) ) & membership; \
}


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

// Protocol State
local bool commitmentRequired = false;


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
  *   - abstract "attacker knowledgebase"
  *
****/
inline messaging_move ( e, inviter )
{
    attacker_study_message ( e, inviter );
}


/****
  *
  * The inline definition is used by the security game moves:
  *   - remove_member (Oracle RMV)
  *   - oblige_update (Oracle UPD)
  *
****/
inline restore_safety ( id )
{
    d_step // MISS!
    {
        if
        :: CheckBit( unsafe, id ) ->
            {
              ClearBit( unsafe, id );
              unsafeIDs--
            }
        :: else
        fi
    }
}


/****
  * External result variable(s):
  *   - commitmentRequired
  *   - unsafeIDs
****/
inline post_play_poll ( e )
{
    d_step {
        // Unset the "active IDs"
        originID = NONE;
        targetID = NONE;

        // Refresh "unsafeIDs"
        unsigned remainingEpochs    : BITS_EPOCH = FINAL_EPOCH - e;
        unsigned recoveriesRequired : BITS_USERID = 0;
        d_step
        {
            unsigned n : BITS_USERID;
            for ( n : FIRST_USERID .. FINAL_USERID ) {
                if
                :: CheckBit( unsafe, n ) -> recoveriesRequired++;
                :: else
                fi
            }
        }
        unsafeIDs = recoveriesRequired;
        
        bool canRevealRoot = e != FINAL_EPOCH && !( learnedActiveKey );

        // Refresh "commitmentRequired"
        bool canHoardMember = false;
        d_step
        {
            unsigned candidateHoarders : BITS_USERID;
            candidates_for_hoarding ( );
            canHoardMember = candidateHoarders > 0;
        }
    
        bool canCorruptMember = false;
        d_step
        {
            unsigned candidateCorruptibles : BITS_USERID;
            candidates_for_corruption ( );
            canCorruptMember = candidateCorruptibles > 0;
        }
    
        commitmentRequired = !canRevealRoot && !canHoardMember && !canCorruptMember
    }
}


/****
  * External result variable(s):
  *   - absentees
  *   - attendees
  *   - groupMost
****/
inline take_attendance ( )
{
    unsigned largestID : BITS_USERID = 0;
    d_step {
        unsigned included : BITS_USERID = 0;
        d_step {
            unsigned n : BITS_USERID;
            for ( n : FIRST_USERID .. FINAL_USERID ) {
                 if
                 :: CheckBit( membership, n ) -> included++; largestID = n
                 :: else
                 fi
            }
        }
        attendees = included;
        absentees = N - attendees;
    }

    if
    :: largestID > groupMost -> groupMost = largestID;
    :: else
    fi
}


/****
  * External result variable(s):
  *   - candidateCorruptibles
****/
inline candidates_for_corruption ( )
{
#ifdef SELECT_VIA_LOOP
    unsigned candidates : BITS_USERID = 0;
    d_step
    {
        unsigned n : BITS_USERID;
        for ( n : FIRST_USERID .. FINAL_USERID )
        {
            bool candidateCorruption;
            candidate_corruption ( n );
            if
            :: candidateCorruption -> candidates++
            :: else
            fi
        }
    }
    candidateCorruptibles = candidates
#else
    d_step
    {
        printf ( "\nCorruption Check:    unsafe                = 0x2%x\n"  ,    unsafe                );
        printf (   "Corruption Check: ( ~unsafe )              = 0x2%x\n"  , ( ~unsafe )              );
        printf (   "Corruption Check:               membership = 0x2%x\n"  ,               membership );
        printf (   "Corruption Check: ( ~unsafe ) & membership = 0x2%x\n\n", ( ~unsafe ) & membership );
        buffer = ( ~unsafe ) & membership;
        PopCount ( buffer, buffer );
        candidateCorruptibles = buffer;
    }
#endif
}


/****
  * External result variable(s):
  *   - candidateCorruption
****/
inline candidate_corruption ( id )
{
    // The corrupted user must not previously been instructed to hoard!
    // Violates the "Safety Predicate SAFE" described in Alwen 2020.
    candidateCorruption = CheckBit( membership, id ) && !( CheckBit( unsafe, id ) ) // !( CheckBit( attackerKnowledge[epoch], LEAF + id ) )
}


/****
  * External result variable(s):
  *   - candidateHoarders
****/
inline candidates_for_hoarding ( )
{
#ifdef SELECT_VIA_LOOP
    unsigned candidates : BITS_USERID = 0;
    d_step
    {
        unsigned n : BITS_USERID;
        for ( n : FIRST_USERID .. FINAL_USERID )
        {
            bool candidateHoarder
            candidate_hoarder ( n );
            if
            :: candidateHoarder -> candidates++
            :: else
            fi
        }
    }
    candidateHoarders = candidates
#else
    d_step
    {
        printf ( "\n\tHoarding Count:      hoarding                               = 0x2%x\n"  ,      hoarding                               );
        printf (     "Hoarding Count:                 startHoard                  = 0x2%x\n"  ,                 startHoard                  );
        printf (     "Hoarding Count:                                  membership = 0x2%x\n"  ,                                  membership );
        printf (     "Hoarding Count:   ~( hoarding | startHoard )                = 0x2%x\n"  ,   ~( hoarding | startHoard )                );
        printf (     "Hoarding Count: ( ~( hoarding | startHoard ) ) & membership = 0x2%x\n"  , ( ~( hoarding | startHoard ) ) & membership );
        CandidateHoarderArray( buffer );
        PopCount ( buffer, buffer );
        candidateHoarders = buffer;
        printf (     "Hoarding Count: candidateHoarders = 0x2%x ~~ %d\n", candidateHoarders, candidateHoarders );
    }
#endif
}


/****
  * External result variable(s):
  *   - candidateHoarder
****/
inline candidate_hoarder ( id )
{
    candidateHoarder = !( CheckBit( hoarding | startHoard, id ) ) && CheckBit( membership, id )
}


#endif /* IMPORT_SPEC_NETWORKING */
