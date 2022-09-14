#ifndef IMPORT_TWIDDLE_POPCOUNT_BYTE
#define IMPORT_TWIDDLE_POPCOUNT_BYTE

//#define BIT_WIDTH 8
#define BIT_WIDTH 16

/*
    mask-1 = 55_{16} =  85_{10} = 01010101_{2}
    mask-2 = 33_{16} =  51_{10} = 00110011_{2}
    mask-3 = 07_{16} =   7_{10} = 00000111_{2}

    out = (in        ) - ((in  >> 1) & 0x55);
    out = (out & 0x33) + ((out >> 2) & 0x33);
    out = (out & 0x07) + ((out >> 4) & 0x07);
*/
#define PopCount( pop_in, pop_out ) \
atomic { \
    pop_out = (pop_in      ) - ((pop_in  >> 1) & 85); \
    pop_out = (pop_out & 51) + ((pop_out >> 2) & 51); \
    pop_out = (pop_out &  7) +  (pop_out >> 4); \
}
/*
    printf ( "pop_in          =  0x%02x  %3d\n", pop_in,  pop_in  ); \
    printf ( "  pop_out[1]    =  0x%02x  %3d\n", pop_out, pop_out ); \
    printf ( "    pop_mid[1]  =  0x%02x  %3d\n",   ( pop_out & 51 )                               ,   ( pop_out & 51 )                               ); \
    printf ( "    pop_mid[2]  =  0x%02x  %3d\n",                        ( pop_out >> 2 )          ,                        ( pop_out >> 2 )          ); \
    printf ( "    pop_mid[3]  =  0x%02x  %3d\n", ( ( pop_out & 51 ) + ( ( pop_out >> 2 ) & 51 ) ) , ( ( pop_out & 51 ) + ( ( pop_out >> 2 ) & 51 ) ) ); \
    printf ( "  pop_out[2]    =  0x%02x  %3d\n", pop_out, pop_out ); \
    printf ( "  pop_out[3]    =  0x%02x  %3d\n", pop_out, pop_out ); \
*/

/*
    mask-1 = 5555_{16} = 21845_{10} = 0101010101010101_{2}
    mask-2 = 3333_{16} = 13107_{10} = 0011001100110011_{2}
    mask-3 = 0F0F_{16} =  3855_{10} = 0000111100001111_{2}
    mask-4 = 000F_{16} =    15_{10} = 0000000000001111_{2}

    out = (in          ) - ((in  >> 1) & 0x5555);
    out = (out & 0x3333) + ((out >> 2) & 0x3333);
    out = (out & 0x0F0F) + ((out >> 4) & 0x0F0F);
    out = (out & 0x0007) + ((out >> 8)         );

NOTE:
    Equivelent for all ( unsigned pop_in : n ) and ( unsigned pop_out : n )
    where ( n >= 1) and ( pop_in ) and ( pop_out ) are the same dimension ( n).
*/
#define POP_COUNT( pop_in, pop_out ) \
atomic { \
    pop_out = ( pop_in          ) - ( ( (pop_in) >> 1 ) & 21845 ); \
    pop_out = ( pop_out & 13107 ) + ( (  pop_out >> 2 ) & 13107 ); \
    pop_out = ( pop_out &  3855 ) + ( (  pop_out >> 4 ) &  3855 ); \
    pop_out = ( pop_out &    15 ) + ( (  pop_out >> 8 )         ); \
}


#include "Bit-Array.pml"

local unsigned output_iterate : BIT_WIDTH;
local unsigned output_twiddle : BIT_WIDTH;


inline popcount_iterate ( v )
{
    atomic
    {
        d_step {
            output_iterate = 0;
            unsigned i : BIT_WIDTH;
            for ( i : 0 .. BIT_WIDTH - 1 ) {
                 if
                 :: CheckBit( v, i ) -> output_iterate++;
                 :: else
                 fi
            }
        }
    }
}


inline popcount_twiddle ( input )
{
    POP_COUNT ( input, output_twiddle )
}



proctype TwiddlePopcount ( )
{
    unsigned maxBound : BIT_WIDTH = ( 1 << ( BIT_WIDTH - 1 ) ) + ( ( 1 << ( BIT_WIDTH - 1 ) ) - 1 );
    unsigned minBound : BIT_WIDTH = 0;
    unsigned theValue : BIT_WIDTH;

    for ( theValue : minBound .. maxBound )
    {
        popcount_iterate ( theValue );
        popcount_twiddle ( theValue );
/**
        atomic {
            printf ( "iterate ( %3d ) = %d\n"  , theValue, output_iterate );
            printf ( "twiddle ( %3d ) = %d\n\n", theValue, output_twiddle );
        }
**/
        assert ( output_iterate == output_twiddle );
    };
}

init
{
    run TwiddlePopcount ( );
}

#endif /* IMPORT_TWIDDLE_POPCOUNT_BYTE */
