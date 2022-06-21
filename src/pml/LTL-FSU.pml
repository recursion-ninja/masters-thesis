#include "Parameterized-Constants.pml"
#include "State-Global.pml"


/****
  *
  * LTL: FSU (Future Secrecy with Updates)
  *
****/
#define never_trivially_hoard_then_corrupt \
( []( CGKA@move_corrupt -> hoarding[targetID] == NEVER ) )


#define future_secrecy_of_epoch( t ) \
(  \
    (  \
        <> \
        (  \
            ( CGKA@start_of_epoch ) \
        && \
            ( epoch == (t + 1) ) \
        && \
            ( !(learnedKey[t]) ) \
        )  \
    ) \
-> \
    (  \
        ( !(learnedKey[t]) ) \
    U  \
        ( CGKA@end_of_game ) \
    )  \
)


ltl FSU
{
    never_trivially_hoard_then_corrupt ->
    (   future_secrecy_of_epoch(  0 )
    &&  future_secrecy_of_epoch(  1 )
    &&  future_secrecy_of_epoch(  2 )
    &&  future_secrecy_of_epoch(  3 )
    &&  future_secrecy_of_epoch(  4 )
    &&  future_secrecy_of_epoch(  5 )
    &&  future_secrecy_of_epoch(  6 )
    &&  future_secrecy_of_epoch(  7 )
    &&  future_secrecy_of_epoch(  8 )
    &&  future_secrecy_of_epoch(  9 )
    &&  future_secrecy_of_epoch( 10 )
    )
}
