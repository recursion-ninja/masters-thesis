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
    *   - Corrupt ( COR )
    *   - Hoard   ( HRD )
    *   - Reveal  ( RVL )
    *
********/


inline corrupt ( memberID )
{
    d_step
    {
        printf ( "\n> > >\n> CGKA: Move Name\t( COR : @ %d <- _ )\n> > >\n", memberID );
        assert ( memberID < N );
        targetID = memberID;
    };

    // Learn the secret material of the user in their current epoch...
    // plus any additional epochs they have hoarded secrets from.
    unsigned lowerBound : BITS_EPOCH,
             upperBound : BITS_EPOCH;
    d_step
    {
        lowerBound = epoch;
        upperBound = epoch;
        unsigned savedSince : BITS_EPOCH = hoarding[memberID];
        if
        :: savedSince != NEVER -> lowerBound = savedSince
        :: else
        fi
    };

move_corrupt: skip;
    printf ( "Corrupting from: %d -- %d\n", lowerBound, upperBound );

    // For each epoch which the member has secrets
    // (this implies that the user was a member)
    // Then the attacker learns the secrets on the direct path
    // between the member and the root node on the LBBT.
    unsigned peek : BITS_EPOCH;
    for ( peek : lowerBound .. upperBound )
    {
        if
        :: !(membership[memberID]) -> skip
        :: else -> atomic
            {
                attacker_learn_leaf      ( peek, memberID );
                attacker_amend_knowledge ( peek );
            }
        fi
    };
    unsafe[memberID] = true;
    unsafe[memberID] = true;
    attacker_check_knowledge ( epoch );
}


inline hoard ( memberID )
{
    d_step
    {
        printf ( "\n> > >\n> CGKA: Move Name\t( HRD : @ %d <- _ )\n> > >\n", memberID );
        assert ( memberID < N );
        targetID = memberID;
    };

move_hoard: skip;
    hoarding[memberID] = epoch;
}


inline reveal ( )
{
    printf ( "\n> > >\n> CGKA: Move Name\t( RVL : * _ -- _ ) @ %d\n> > >\n", epoch );

move_reveal: skip;
    d_step {
        StampBit( challenge, epoch );
        attacker_learn_root ( epoch );
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
inline insert_member ( memberID, inviteeID )
{
    d_step
    {
        printf ( "\n> > >\n> CGKA: Move Name\t( ADD : + %d <- %d )\n> > >\n", inviteeID, memberID );
        assert (  memberID < N );
        assert ( inviteeID < N );
        assert ( !(membership[inviteeID]) );

        originID =  memberID;
        targetID = inviteeID;
    };

move_insert: skip;
    messaging_move ( epoch + 1, memberID, inviteeID, NONE )
}


// Precondition: evicteeID is in the group!
inline remove_member ( memberID, evicteeID )
{
    d_step
    {
        printf ( "\n> > >\n> CGKA: Move Name\t( RMV : - %d <- %d )\n> > >\n", evicteeID, memberID );
        assert (  memberID < N );
        assert ( evicteeID < N );
        assert ( membership[evicteeID] );

        originID =  memberID;
        targetID = evicteeID;
    };

move_remove: skip;
    d_step
    {
        if
        :: unsafe[evicteeID] -> unsafeIDs--
        :: else
        fi
        unsafe[evicteeID] = false;
    };
    messaging_move ( epoch + 1, memberID, NONE, evicteeID )
}


inline oblige_update ( memberID )
{
    d_step
    {
        printf ( "\n> > >\n> CGKA: Move Name\t( UPD : @ _ <- %d )\n> > >\n", memberID );
        assert ( memberID < N );

        originID = memberID;
        targetID = NONE;
    };

move_update: skip;
    d_step
    {
        if
        :: unsafe[memberID] -> unsafeIDs--
        :: else
        fi
        unsafe[memberID] = false;
    };
    messaging_move ( epoch + 1, memberID, NONE, NONE )
}


#endif /* IMPORT_SPEC_ORACLES */
