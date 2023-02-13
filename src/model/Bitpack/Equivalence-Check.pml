#ifndef IMPORT_TWIDDLE_POPCOUNT
#define IMPORT_TWIDDLE_POPCOUNT

//#define BIT_ARRAY_WIDTH 8
#define BIT_ARRAY_WIDTH 16


#include "Bit-Array.pml"
#include "Pop-Count.pml"


local BitArray ( output_iterate );
local BitArray ( output_twiddle );


inline popcount_iterate ( v )
{
    atomic
    {
        d_step {
            output_iterate = 0;
            BitArray ( i );
            for ( i : 0 .. BIT_ARRAY_WIDTH - 1 ) {
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
    PopCount ( input, output_twiddle )
}


proctype verify_equivalence ( )
{
    BitArray ( maxBound ) = ( 1 << ( BIT_ARRAY_WIDTH - 1 ) ) + ( ( 1 << ( BIT_ARRAY_WIDTH - 1 ) ) - 1 );
    BitArray ( minBound ) = 0;
    BitArray ( theValue );

    for ( theValue : minBound .. maxBound )
    {
        popcount_iterate ( theValue );
        popcount_twiddle ( theValue );
        assert ( output_iterate == output_twiddle );
    };
}


init
{
    run verify_equivalence ( );
}

#endif /* IMPORT_TWIDDLE_POPCOUNT */
