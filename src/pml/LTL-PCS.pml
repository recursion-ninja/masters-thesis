#include "Global-State.pml"


/****
  *
  * LTL: PCS (Post-Compromise Security)
  *
****/
ltl PCS
{ 
    [] ( ( CGKA@start_of_epoch && ( memberKeys == 0 ) ) -> ( !( learnedActiveKey ) ) )
}
