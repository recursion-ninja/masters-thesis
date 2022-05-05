#ifndef IMPORT_SPEC_SELECTION
#define IMPORT_SPEC_SELECTION

#include "Parameterized-Constants.pml"
#include "State-Global.pml"
#include "State-Networking.pml"
#include "TreeKEM-v1.pml"


/********
    *
    * User ID selection inlines:
    *   - select_corrupted
    *   - select_evictor
    *   - select_evictee
    *   - select_hoarder
    *   - select_invitee
    *   - select_inviter
    *   - select_updater
    *
********/


/****
  * External result variable(s):
  *   - corruptedID
****/
inline select_corrupted ( )
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
  *   - evictorID
****/
inline select_evictor ( banned )
{
    unsigned selectedID : BITS_USERID;
    select_member_constrained( banned );
    evictorID = selectedID;
}


/****
  * External result variable(s):
  *   - evicteeID
****/
inline select_evictee ( )
{
    unsigned selectedID : BITS_USERID;
    select_member_constrained( NONE );
    evicteeID = selectedID;
}


/****
  * External result variable(s):
  *   - hoarderID
****/
inline select_hoarder ( )
{   atomic {

    unsigned candidateHoarders : BITS_USERID;
    candidates_for_hoarding ( );

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
  *   - inviteeID
****/
inline select_invitee ( )
{   atomic {

    unsigned candidateInvitees : BITS_USERID;
    candidates_for_invitee();

    unsigned selection : BITS_USERID = NONE;
    d_step
    {
        unsigned n      : BITS_USERID;
        unsigned sample : BITS_USERID;
        select(  sample : 0 .. candidateInvitees - 1 );
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
    
    inviteeID = selection;
}   }


/****
  * External result variable(s):
  *   - inviterID
****/
inline select_inviter ( )
{
    unsigned selectedID : BITS_USERID;
    select_member_constrained ( NONE );
    inviterID = selectedID;
}


/****
  * External result variable(s):
  *   - updaterID
****/
inline select_updater ( )
{
    unsigned selectedID : BITS_USERID;
    select_member_constrained ( NONE );
    updaterID = selectedID;
}


/****
  * External result variable(s):
  *   - selectedID
****/
inline select_member_constrained ( banned )
{   atomic {
    unsigned candidateMembers : BITS_USERID = 0;
    candidates_from_members ( banned )

    if
    :: candidateMembers == 0 -> selectedID = NONE
    :: else ->
        unsigned selection : BITS_USERID = NONE;
        d_step
        {
            unsigned n      : BITS_USERID;
            unsigned sample : BITS_USERID;
            select(  sample : 0 .. candidateMembers - 1 );
            for ( n : FIRST_USERID .. FINAL_USERID ) {
                d_step
                {
                    if
                    :: selection == NONE ->
                        bool candidateMember;
                        candidate_member ( banned, n );
                        if
                        :: candidateMember ->
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
  *   - candidateInvitees
****/
inline candidates_for_invitee ( )
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
    candidateInvitees = candidates
}


/****
  * External result variable(s):
  *   - candidateMembers
****/
inline candidates_from_members ( banned )
{
    unsigned candidates : BITS_USERID = 0;
    d_step
    {
        unsigned n : BITS_USERID;
        for ( n : FIRST_USERID .. FINAL_USERID )
        {
            d_step
            {
                bool candidateMember;
                candidate_member ( banned, n )
                if
                :: candidateMember -> candidates++
                :: else
                fi
            }
        }
    }
    candidateMembers = candidates
}


/****
  * External result variable(s):
  *   - candidateMember
****/
inline candidate_member ( banned, id )
{
//    bool forcesSafe = !(forced) || unsafe[id];
    bool isAnOption = membership[id] && (id != banned);
    candidateMember = isAnOption // && forcesSafe
}


#endif /* IMPORT_SPEC_SELECTION */
