#ifndef IMPORT_SPEC_ORACLES
#define IMPORT_SPEC_ORACLES

#include "Parameterized-Constants.pml"
#include "Global-State.pml"
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


inline corrupt ( )
{
    printf ( "\n> > >\n> CGKA: Move Name\t( COR : @ %d <- _ )\n> > >\n", targetID );

    if
    :: CheckBit( hoardPrior, targetID ) -> learnedLegacyKey = true;
    :: else
    fi

    StampBit( memberKeys, targetID );
    attacker_learn_leaf      ( epoch, targetID );
    attacker_amend_knowledge ( epoch, targetID );
    attacker_check_knowledge ( epoch );
}


inline hoard ( )
{
    printf ( "\n> > >\n> CGKA: Move Name\t( HRD : @ %d <- _ )\n> > >\n", targetID );

    StampBit( hoardNovel, targetID )
}


inline reveal ( )
{
    printf ( "\n> > >\n> CGKA: Move Name\t( RVL : * _ -- _ ) @ %d\n> > >\n", epoch );

    challenged = true;
    learnedActiveKey = true;
    attacker_learn_root ( epoch );
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


inline insert_member ( )
{
    printf ( "\n> > >\n> CGKA: Move Name\t( ADD : + %d <- %d )\n> > >\n", targetID, originID );

    if
    :: targetID > widestID -> widestID = targetID
    :: else
    fi
    StampBit( membership, targetID )
    attacker_study_message ( epoch + 1, originID );
}


inline remove_member ( )
{
    printf ( "\n> > >\n> CGKA: Move Name\t( RMV : - %d <- %d )\n> > >\n", targetID, originID );

    ClearBit( memberKeys, targetID );
    ClearBit( membership, targetID );
    attacker_study_message ( epoch + 1, originID );
}


inline oblige_update ( )
{
    printf ( "\n> > >\n> CGKA: Move Name\t( UPD : @ _ <- %d )\n> > >\n", originID );

    ClearBit( memberKeys, originID );
    attacker_study_message ( epoch + 1, originID );
}


#endif /* IMPORT_SPEC_ORACLES */
