#ifndef IMPORT_SPEC_PRINTING
#define IMPORT_SPEC_PRINTING

#include "Parameterized-Constants.pml"
#include "State-Global.pml"
#include "State-Networking.pml"
#include "TreeKEM-v1.pml"


/********
    *
    * Global state priniting utilities:
    *   - print_challenges
    *   - print_membership
    *   - print_user_hoarding
    *   - print_user_unsafe
    *
********/


inline print_challenges ()
{
    d_step {
        printf("\n\tChallenges:");
        unsigned t : BITS_EPOCH;
        for ( t : FIRST_EPOCH .. FINAL_EPOCH )
        {
            if
            :: challenge[t] -> printf("\n\t    [\tTrue\t]");
            :: else         -> printf("\n\t    [\tFalse\t]");
            fi
        }
        printf("\n");
    }
}


inline print_membership ()
{
    d_step {
        printf("\n\tMembership:");
        unsigned p : BITS_USERID;
        for ( p : FIRST_USERID .. FINAL_USERID )
        {
            if
            :: membership[p] -> printf("\n\t    [\tTrue\t]");
            :: else          -> printf("\n\t    [\tFalse\t]");
            fi
        };
        printf("\n");
    }
}


inline print_user_hoarding ()
{
    d_step {
        printf("\n\tHoarding since:");
        unsigned p : BITS_USERID;
        for ( p : FIRST_USERID .. FINAL_USERID )
        {
            if
            :: hoarding[p] == NONE -> printf("\n\t    [\tNONE\t]")
            :: else                -> printf("\n\t    [\t%d\t]", hoarding[p])
            fi
        }
        printf("\n");
    }
}


inline print_user_unsafe ()
{
    d_step {
        printf("\n\tRequired healing:");
        unsigned p : BITS_USERID;
        for ( p : FIRST_USERID .. FINAL_USERID )
        {
            if
            :: unsafe[p] -> printf("\n\t    [\tTrue\t]");
            :: else      -> printf("\n\t    [\tFalse\t]");
            fi
        }
        printf("\n");
    }
}


/********
    *
    * Network state priniting utilities:
    *   - print_group_composition
    *   - print_protocol_state
    *
********/


inline print_group_composition ()
{
    d_step
    {
        printf("\n\tattendees \t%d", attendees );
        printf("\n\tabsentees \t%d", absentees );
        printf("\n\tgroupDyad \t%d", groupDyad );
        printf("\n\tgroupFull \t%d", groupFull );
        printf("\n\tgroupMost \t%d", groupMost );
    }
}


inline print_protocol_state ()
{
    d_step
    {
        printf("\n\trevealRoot \t%d", revealRoot );
        printf("\n\tforcedPlay \t%d", forcedPlay );
        printf("\n\tunsafeIDs  \t%d", unsafeIDs  );
    }
}


/********
    *
    * Entire state priniting utilities:
    *   - print_entire_state
    *
********/


inline print_entire_state ()
{
    d_step
    {
        printf("\n-=-=-=-=-=-=-=-=-=-=-=-\n-=-  GLOBAL  STATE  -=-\n-=-=-=-=-=-=-=-=-=-=-=-\n");
        printf("\nCurrent Epoch \t%d\n", epoch );
        print_challenges ();
        print_membership ();
        print_user_hoarding ();
        print_user_unsafe ();
        print_group_composition ();
        print_protocol_state ();
        print_attacker_knowledge ()
    }
}


#endif /* IMPORT_SPEC_PRINTING */
