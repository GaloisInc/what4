This is a WIP migration guide for porting downstream libraries after the
what4/bv-sized change.

* Constants (no Num instance): "0" because "BV.zero w"
* All Data.Bits operations