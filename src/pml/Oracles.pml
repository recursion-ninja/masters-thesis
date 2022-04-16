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
            unsigned level : BITS_VERTEX = N;
            do
            :: level == 0 -> break
            :: level != 0 ->
                d_step
                {
                    unsigned v : BITS_VERTEX = off+memberID;
                    printf("tree level: %d @ %d\n", level, v);
                    if
                    :: attackerKnowledge[peek].node[v] == NodeUnknown -> attackerKnowledge[peek].node[v] = NodeIsKnown
                    :: attackerKnowledge[peek].node[v] == MockUnknown -> attackerKnowledge[peek].node[v] = MockIsKnown
                    :: else
                    fi
                    level = level / 2;
                    off   = off   / 2;
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


// Precondition: joiner is not in the group!
inline insert_member( memberID, joinerID )
{
    d_step {
        printf("\n> > >\n> CGKA: Game Move = ADD %d %d\n> > >\n", memberID, joinerID);
        assert( memberID < N );
        assert( joinerID < N );
        assert( !(membership[exiledID]) );
    }
    messaging_move( epoch + 1, memberID, joinerID, NONE )
}


// Precondition: exiledID is in the group!
inline remove_member( memberID, exiledID )
{
    d_step {
        printf("\n> > >\n> CGKA: Game Move = RMV %d %d\n> > >\n", memberID, exiledID);
        assert( memberID < N );
        assert( exiledID < N );
        assert( membership[exiledID] );
        unsafe[exiledID] = false;
    }
    messaging_move( epoch + 1, memberID, NONE, exiledID )
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
