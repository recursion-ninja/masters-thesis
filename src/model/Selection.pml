#ifndef IMPORT_SPEC_SELECTION
#define IMPORT_SPEC_SELECTION

#include "Bitpack/Bit-Array.pml"
#include "Parameterized-Constants.pml"
#include "Bitpack/Pop-Count.pml"
#include "Global-State.pml"
#include "TreeKEM-v1.pml"
#include "Bitpack/Bit-Array.pml"


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


inline select_from ( options, selected )
{
    atomic
    {
        if
        :: options == 0 -> printf ( "\n-=-=-=-=-=-=-\nSelection Options = NONE!\n-=-=-=-=-=-=-=-\n" );
        :: else -> skip
        fi
        
        selected = NONE;
        BITARRAY ( count );
        PopCount ( options, count );
//        printf ( "\nCount:\t%d", count );
        if
        :: count == 0 -> skip; // Leave ID as NONE!
        :: else ->
            unsigned sample : BITS_USERID;
            select ( sample : 0 .. count - 1 );
                unsigned n : BITS_USERID = FIRST_USERID;
                do
                :: selected != NONE -> break
                :: else ->
                    if
                    :: !( CheckBit ( options, n ) ) -> skip
                    :: else ->
                        if
                        :: sample == 0 -> selected = n
                        :: sample != 0 -> sample--
                        fi
                    fi
                    n++;
                od
        fi
    }
}


inline buffer_for_corrupt ( buffer )
{
    buffer = ( ~memberKeys ) & membership;
}


inline buffer_for_hoard ( buffer )
{
    buffer = ( ~( hoardPrior | hoardNovel ) ) & membership;
}


inline buffer_for_invitee ( buffer )
{
    BITARRAY ( most ) = widestID;
    if
    :: most < N - 1 -> most++
    :: else
    fi

    buffer = ( 1 << N ) - 1;
    buffer = buffer ^ ( (1 << ( most + 1 )) - 1 )
    buffer = buffer ^ ( membership ^ ( ( 1 << N ) - 1 ) );
}


inline select_corrupted ( )
{
    buffer = ( ~memberKeys ) & membership;
    select_from ( buffer, targetID );
}


inline select_evictor ( )
{
    buffer = membership;
    ClearBit( buffer, targetID );
    select_from ( buffer, originID );
}


inline select_evictee ( )
{
    buffer = membership;
    select_from ( buffer, targetID );
}


inline select_hoarder ( )
{
    buffer_for_hoard( buffer );
    select_from ( buffer, targetID );
}


inline select_invitee ( )
{
    buffer = membership;
    buffer_for_invitee( buffer );
    select_from ( buffer, targetID );
}


inline select_inviter ( )
{
    buffer = membership;
    select_from ( buffer, originID );
}


inline select_updater ( )
{
    buffer = membership;
    select_from ( buffer, originID );
}


#endif /* IMPORT_SPEC_SELECTION */
