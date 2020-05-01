This is a WIP migration guide for porting downstream libraries after the
what4/bv-sized change.

* Constants (no Num instance): "0" because "BV.zero w"
* All Data.Bits operations

First pass: resolving Integer ~ BV.BV w mismatch
* Basically, there's two scenarios -- one where you want to turn the Integer into a BV w, and one where you just want to convert.
* asUnsignedBV x ==> BV.asUnsigned <$> asBV x
* fromConcreteUnsignedBV x ==> BV.asUnsigned (fromConcreteBV x)
* bvLit sym w x ==> bvLit sym w (BV.mkBV w x)
* i <- [0..n] ==> i <- BV.enumFromToUnsigned (BV.zero w) (BV.mkBV w n)
* minSigned ==> BV.minSigned
* functions from parameterized-utils that return Integers ==> functions from bv-sized that return BVs
* Num operators ==> BV operators
* Bits operators ==> BV operators
* shifting/masking ==> BV concat/select/trunc/zext/sext

Second pass: resolving "no Num instance"
* 0 ==> BV.zero w
* 1 ==> BV.one w
* for anything else, you probably should use BV.mkBV w