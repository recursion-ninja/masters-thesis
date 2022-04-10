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
  *   - senderID
****/
inline select_sender()
{
    unsigned selectedID : BITS_USERID;
    select_sender_constrained ( NONE, false );
    senderID = selectedID;
}


/****
  * External result variable(s):
  *   - updaterID
****/
inline select_updater( forced )
{
    unsigned selectedID : BITS_USERID;
    select_sender_constrained ( NONE, forced );
    updaterID = selectedID;
}


/****
  * External result variable(s):
  *   - selectedID
****/
inline select_sender_constrained ( banned, forced )
{   atomic {
    unsigned candidateSenders : BITS_USERID = 0;
    candidates_for_sender ( banned, forced )

    if
    :: candidateSenders == 0 -> selectedID = NONE
    :: else ->
        unsigned selection : BITS_USERID = NONE;
        d_step
        {
            unsigned n      : BITS_USERID;
            unsigned sample : BITS_USERID;
            select(  sample : 0 .. candidateSenders - 1 );
            for ( n : FIRST_USERID .. FINAL_USERID ) {
                d_step
                {
                    if
                    :: selection == NONE ->
                        bool candidateSender;
                        candidate_sender ( banned, forced, n );
                        if
                        :: candidateSender ->
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
  *   - candidateJoiners
****/
inline candidates_for_joiner ()
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
  *   - candidateSenders
****/
inline candidates_for_sender ( banned, forced )
{
    unsigned candidates : BITS_USERID = 0;
    d_step
    {
        unsigned n : BITS_USERID;
        for ( n : FIRST_USERID .. FINAL_USERID )
        {
            d_step
            {
                bool candidateSender;
                candidate_sender ( banned, forced, n )
                if
                :: candidateSender -> candidates++
                :: else
                fi
            }
        }
    }
    candidateSenders = candidates
}


/****
  * External result variable(s):
  *   - candidateSender
****/
inline candidate_sender ( banned, forced, id )
{
    bool forcesSafe = !(forced) || unsafe[id];
    bool isAnOption = membership[id] && (id != banned);
    candidateSender = isAnOption && forcesSafe
}


#endif /* IMPORT_SPEC_SELECTION */
