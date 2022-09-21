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
//        assert ( memberID < N );
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
    printf ( "Learning secrets from epochs: [ %d, %d ]\n", lowerBound, upperBound );

    // For each epoch which the member has secrets
    // (this implies that the user was a member)
    // Then the attacker learns the secrets on the direct path
    // between the member and the root node on the LBBT.
    unsigned peek : BITS_EPOCH;
    for ( peek : lowerBound .. upperBound )
    {
        if
        :: CheckBit( membership, memberID ) -> atomic
            {
                attacker_learn_leaf      ( peek, memberID );
                attacker_amend_knowledge ( peek, memberID );
            }
        :: else
        fi
    };
    StampBit(    unsafe, memberID );
//    StampBit( memberKey, memberID );
    attacker_check_knowledge ( epoch );
}


inline hoard ( memberID )
{
    d_step
    {
        printf ( "\n> > >\n> CGKA: Move Name\t( HRD : @ %d <- _ )\n> > >\n", memberID );
//        assert ( memberID < N );
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
        challenged = true;
        learnedKey = true;
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
//        assert (  memberID < N );
//        assert ( inviteeID < N );
//        assert ( !( CheckBit( membership, inviteeID) ) );

        originID =  memberID;
        targetID = inviteeID;
    };

move_insert: skip;
    StampBit( membership, inviteeID )
    take_attendance ( );
    messaging_move ( epoch + 1, memberID )
}


// Precondition: evicteeID is in the group!
inline remove_member ( memberID, evicteeID )
{
    d_step
    {
        printf ( "\n> > >\n> CGKA: Move Name\t( RMV : - %d <- %d )\n> > >\n", evicteeID, memberID );
//        assert (  memberID < N );
//        assert ( evicteeID < N );
//        assert ( CheckBit( membership, evicteeID ) );

        originID =  memberID;
        targetID = evicteeID;
    };

move_remove: skip;
    restore_safety ( evicteeID );
    ClearBit( membership, evicteeID );
    take_attendance ( );
    messaging_move ( epoch + 1, memberID )
}


inline oblige_update ( memberID )
{
    d_step
    {
        printf ( "\n> > >\n> CGKA: Move Name\t( UPD : @ _ <- %d )\n> > >\n", memberID );
//        assert ( memberID < N );

        originID = memberID;
        targetID = NONE;
    };

move_update: skip;
    restore_safety ( memberID );
    messaging_move ( epoch + 1, memberID );
}


#endif /* IMPORT_SPEC_ORACLES */
