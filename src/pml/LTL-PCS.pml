#include "State-Global.pml"


/****
  *
  * LTL: PCS (Post-Compromise Security)
  *
****/
ltl PCS
{ 
    [] ( ( CGKA@start_of_epoch && ( unsafeIDs == 0 ) ) -> ( !( CheckBit( learnedKey, epoch) ) ) )
}


/*
#define corrupt_then_recover( id ) \
(  \
   ( \
      ( CGKA@move_corrupt ) \
   && \
      ( targetID == id    ) \
   ) \
-> \
    (  \
        <> \
        ( \
            (  \
                ( CGKA@move_remove ) \
            && \
                ( targetID == id ) \
            )  \
        || \
            (  \
                ( CGKA@move_update ) \
            && \
                ( originID == id ) \
            )  \
        ) \
    ) \
)


ltl PCS
{ 
    (
        []
        (  corrupt_then_recover ( 0 )
        && corrupt_then_recover ( 1 )
        && corrupt_then_recover ( 2 )
        && corrupt_then_recover ( 3 )
        )
        && CGKA@end_of_game
    )
    ->
    ( !( CheckBit( learnedKey, FINAL_EPOCH ) ) )
}


#define post_compromise_security_of_epoch( id ) \
(  \
    [] \
    (  \
        (   CGKA@start_of_epoch \
        && ( targetID == id ) \
        ) \
    -> \
        ( attackerKnowledge[epoch].node[ROOT] != NodeIsKnown ) \
    )  \
)
*/