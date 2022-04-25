#ifndef IMPORT_SPEC_CGKAGAME
#define IMPORT_SPEC_CGKAGAME

#include "Nondeterministic-Selection.pml"
#include "Oracles.pml"
#include "Parameterized-Constants.pml"
#include "Printing.pml"
#include "State-Global.pml"
#include "State-Networking.pml"


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
  * SYNC: Updated by `post_play_poll`
****/
local bool triviality = false; 


/****
  * Has the CGKA game end?
  *
  * SYNC: Bit flipped IFF at the end of `init`
****/
local bool concludedCGKA = false;


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
    atomic
    {
        bool canInsert, 
             canRemove,
             canUpdate;

        unsigned evictorID : BITS_USERID, 
                 evicteeID : BITS_USERID, 
                 inviteeID : BITS_USERID, 
                 inviterID : BITS_USERID,
                 updaterID : BITS_USERID;
        atomic
        {
            select_evictee ( forcedPlay );
            select_evictor ( evicteeID   );
            select_invitee ( );
            select_inviter ( );
            select_updater ( forcedPlay );
            d_step
            {
                canInsert = !groupFull && !forcedPlay;
                canRemove = !groupDyad && evicteeID != NONE && evictorID != NONE;
                canUpdate = updaterID != NONE;
            }
        };
    
        d_step
        {
            print_entire_state()
            printf("\n.,.,.,.,.,.\nMove Class:\tCommitment\n`'`'`'`'`'`\n");
            printf("\nCommitment values:");
            printf("\n\tevictorID \t%d", evictorID );
            printf("\n\tevicteeID \t%d", evicteeID );
            printf("\n\tinviterID \t%d", inviterID );
            printf("\n\tinviteeID \t%d", inviteeID );
            printf("\n\tupdaterID \t%d", updaterID );
            printf("\n");
        }

        do
        :: canInsert -> insert_member( inviterID, inviteeID ); break
        :: canRemove -> remove_member( evictorID, evicteeID ); break
        :: canUpdate -> oblige_update( updaterID );            break
        od

        post_play_poll( epoch + 1);
    }
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
{
    atomic
    {
        unsigned corruptedID : BITS_USERID, hoarderID : BITS_USERID;
        atomic
        {
            select_corrupted();
            select_hoarder();
        };
    
        d_step
        {
            print_entire_state()
            printf("\n.,.,.,.,.,.\nMove Class:\tNON-Commital\n`'`'`'`'`'`\n");
            printf("\nNon-commital values:");
            printf("\n\tcanRevealKey\t%d",  revealRoot );
            printf("\n\tcorruptedID \t%d", corruptedID );
            printf("\n\thoarderID   \t%d",   hoarderID );
            printf("\n");
        }

        do
        :: corruptedID != NONE && !forcedPlay -> corrupt( corruptedID ); break
        :: hoarderID   != NONE                -> hoard(     hoarderID ); break
        :: revealRoot                         -> reveal(              ); break
        od
    
        post_play_poll( epoch );
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
                hoarding[n] = NEVER;
            };
        };
        
        d_step
        {
            unsigned t : BITS_EPOCH;
            for ( t : FIRST_EPOCH .. FINAL_EPOCH )
            {
                challenge[t]  = false;
                leadership[t] = NONE;
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

    d_step {
        unsigned id0 : BITS_USERID = 0;
        unsigned ep0 : BITS_EPOCH  = 0;
        messaging_move( ep0, id0, NONE, NONE );
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

    commitmentRequired = false;

    // Loop through all epochs
    for ( epoch : 0 .. FINAL_EPOCH)
    {

        do
        // 1. Play the Challenge Move
        //     The attacker ending the game is implicitly the last move of the model
        //     so it always happens in the last epoch.
        :: epoch == FINAL_EPOCH -> break

progressEpoch:
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
endCGKA:
    d_step
    {
        concludedCGKA = true;
        epoch = FINAL_EPOCH;
        print_entire_state();
    }
}


#endif /* IMPORT_SPEC_CGKAGAME */