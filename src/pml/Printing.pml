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


inline print_challenges ( )
{
    d_step {
        printf ( "\n\tChallenges:" );
        unsigned p : BITS_EPOCH;
        for ( p : FIRST_EPOCH .. FINAL_EPOCH )
        {
            if
            :: challenge[p] -> printf ( "\n\t  %d [\tTrue\t]" , p );
            :: else         -> printf ( "\n\t  %d [\tFalse\t]", p );
            fi
        }
        printf ( "\n" );
    }
}


inline print_membership ( )
{
    d_step {
        printf ( "\n\tMembership:" );
        unsigned p : BITS_USERID;
        for ( p : FIRST_USERID .. FINAL_USERID )
        {
            if
            :: membership[p] -> printf ( "\n\t  %d [\tTrue\t]",  p );
            :: else          -> printf ( "\n\t  %d [\tFalse\t]", p );
            fi
        };
        printf ( "\n" );
    }
}


inline print_user_hoarding ( )
{
    d_step {
        printf ( "\n\tHoarding since:" );
        unsigned p : BITS_USERID;
        for ( p : FIRST_USERID .. FINAL_USERID )
        {
            if
            :: hoarding[p] == NEVER -> printf ( "\n\t  %d [\tNEVER\t]", p )
            :: else                 -> printf ( "\n\t  %d [\t%d\t]"  , p, hoarding[p])
            fi
        }
        printf ( "\n" );
    }
}


inline print_user_unsafe ( )
{
    d_step {
        printf ( "\n\tRequired healing:" );
        unsigned p : BITS_USERID;
        for ( p : FIRST_USERID .. FINAL_USERID )
        {
            if
            :: unsafe[p] -> printf ( "\n\t  %d [\tTrue\t]" , p );
            :: else      -> printf ( "\n\t  %d [\tFalse\t]", p );
            fi
        }
        printf ( "\n" );
    }
}


/********
    *
    * Network state priniting utilities:
    *   - print_group_composition
    *   - print_protocol_state
    *
********/


inline print_group_composition ( )
{
    d_step
    {
        printf ( "\n\tGroup Composition:" );
        printf ( "\n\t  - attendees \t=  %d", attendees );
        printf ( "\n\t  - absentees \t=  %d", absentees );
        printf ( "\n\t  - groupMost \t=  %d", groupMost );
        printf ( "\n" );
    }
}


inline print_protocol_state ( )
{
    d_step
    {
        printf ( "\n\tProtocol State:" );
        printf ( "\n\t  - unsafeIDs  \t=  %d", unsafeIDs  );
        printf ( "\n" );
    }
}


/********
    *
    * Entire state priniting utilities:
    *   - print_entire_state
    *
********/


inline print_entire_state ( )
{
    d_step
    {
        printf ( "\n-=-=-=-=-=-=-=-=-=-=-=-\n-=-  GLOBAL  STATE  -=-\n-=-=-=-=-=-=-=-=-=-=-=-\n" );
        printf ( "\n\tCurrent Epoch \t%d\n", epoch );
        print_challenges         ( );
        print_membership         ( );
        print_user_hoarding      ( );
        print_user_unsafe        ( );
        print_group_composition  ( );
        print_protocol_state     ( );
        print_attacker_knowledge ( );
    }
}


#endif /* IMPORT_SPEC_PRINTING */
