#ifndef IMPORT_SPEC_BITARRAY
#define IMPORT_SPEC_BITARRAY

/********
    *
    * Operations on 'unsigned' values used as a 'Bit-Array'
    *
    *   - CheckBit
    *   - ClearBit
    *   - StampBit
    *
********/


#define CheckBit( A, I ) (   ( A &     ( 1 << ( I ) )   ) != 0 )


#define ClearBit( A, I ) A = ( A & ( ~ ( 1 << ( I ) ) ) )


#define StampBit( A, I ) A = ( A |     ( 1 << ( I ) )   )


#endif /* IMPORT_SPEC_BITARRAY */
