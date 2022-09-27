#include "Bit-Array.pml"
#include "Global-State.pml"


/****
  *
  * LTL: FSU (Future Secrecy with Updates)
  *
  * Never corrupt a hoarder implies never learn the past
  *
****/
ltl FSU
{
    (
        []( CGKA@move_corrupt -> !( CheckBit( hoardPrior, targetID ) ) )
    )
        ->
    (
        []( !( learnedLegacyKey ) )
    )
}
