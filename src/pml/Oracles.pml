#ifndef IMPORT_SPEC_ORACLES
#define IMPORT_SPEC_ORACLES

#include "Parameterized-Constants.pml"
#include "State-Global.pml"
#include "State-Networking.pml"
#include "TreeKEM-v1.pml"

/********
    *
    * Oracles available to the attacker used by "non-commital" moves:
    *
    *   - Corrupt (COR)
    *   - Hoard   (HRD)
    *   - Reveal  (RVL)
    *
********/


inline corrupt ( memberID )
{   atomic {

    d_step {
        printf("\n> > >\n> CGKA: Game Move = COR %d\n> > >\n", memberID);
        assert( memberID < N );
    }

    // Learn the secret material of the user in their current epoch...
    // plus any additional epochs they have hoarded secrets from.
    unsigned lowerBound : BITS_EPOCH = epoch
    unsigned upperBound : BITS_EPOCH = epoch;
    unsigned savedSince : BITS_EPOCH = hoarding[memberID];
    if
    :: savedSince != NEVER -> lowerBound = savedSince
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
        :: else -> d_step
            {
                attacker_learn_leaf ( peek, memberID );
                attacker_amend_knowledge ( peek );
            }
        fi
    }
    attacker_check_knowledge ( epoch );
    unsafe[memberID] = true;
}   }


inline hoard( memberID )
{
    d_step {
        assert( memberID < N );
        printf("\n> > >\n> CGKA: Game Move = HRD %d\n> > >\n", memberID);
        hoarding[memberID] = epoch
    }
}


inline reveal ()
{
    d_step {
        printf("\n> > >\n> CGKA: Game Move = RVL %d\n> > >\n", epoch);
        challenge[epoch] = true;
        attacker_learn_root( epoch );
    }
}


/********
    *
    * Oracles available to the attacker used by "commitment" moves:
    *
    *   - Insert Member ( ADD )
    *   - Remove Member ( RMV )
    *   - Oblige Update ( UPD )
    *
********/


// Precondition: invitee is not in the group!
inline insert_member( memberID, inviteeID )
{
    d_step {
        printf("\n> > >\n> CGKA: Game Move = ADD %d %d\n> > >\n", memberID, inviteeID);
        assert(  memberID < N );
        assert( inviteeID < N );
        assert( !(membership[inviteeID]) );
    }
    messaging_move( epoch + 1, memberID, inviteeID, NONE )
}


// Precondition: evicteeID is in the group!
inline remove_member( memberID, evicteeID )
{
    d_step {
        printf("\n> > >\n> CGKA: Game Move = RMV %d %d\n> > >\n", memberID, evicteeID);
        assert(  memberID < N );
        assert( evicteeID < N );
        assert( membership[evicteeID] );
        unsafe[evicteeID] = false;
    }
    messaging_move( epoch + 1, memberID, NONE, evicteeID )
}


inline oblige_update( memberID )
{
    d_step {
        printf("\n> > >\n> CGKA: Game Move = UPD %d\n> > >\n", memberID);
        assert( memberID < N );
        unsafe[memberID] = false;
    }
    messaging_move( epoch + 1, memberID, NONE, NONE )
}


#endif /* IMPORT_SPEC_ORACLES */
