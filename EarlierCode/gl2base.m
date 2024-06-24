freeze;

/*
    Dependencies: utils.m

    This module implements Magma intrinsics for working with open subgroups H of GL(2,Zhat).
    All such H are represented by their projections to GL(2,Z/NZ).

    The integer N can be be any integer for which H is the full preimage of its reduction modulo N (the least such N is the level of H).
    The trivial subgroup is represented by the trivial subgroup of GL(2,Z) (since Magma won't let us define the zero ring Integers(1)=Z/Z).
*/

/*** caching ***/

// Most of this is not used here but it's convenient to setup everything here

declare attributes RngInt: GL2Cache, SL2Cache;
ZZ := Integers();
ZZ`GL2Cache := AssociativeArray();  // place to cache global information that depends only on N (or on nothing at all)
ZZ`GL2Cache["htab"] := [];
ZZ`GL2Cache["modpolys"] := [];
ZZ`GL2Cache["ssets"] := [];
ZZ`GL2Cache["sreps"] := AssociativeArray();
ZZ`GL2Cache["scnts"] := [];
ZZ`GL2Cache["pssets"] := [];
ZZ`GL2Cache["psreps"] := AssociativeArray();
ZZ`GL2Cache["pscnts"] := [];
ZZ`GL2Cache["psindexes"] := [];
ZZ`GL2Cache["cclasses"] := AssociativeArray();
ZZ`GL2Cache["sclasses"] := AssociativeArray();
ZZ`GL2Cache["psclasses"] := AssociativeArray();
ZZ`GL2Cache["cmtwists"] := [];
ZZ`SL2Cache := AssociativeArray();
ZZ`SL2Cache["ssets"] := [];
ZZ`SL2Cache["sreps"] := AssociativeArray();
ZZ`SL2Cache["scnts"] := [];
ZZ`SL2Cache["pssets"] := [];
ZZ`SL2Cache["psreps"] := AssociativeArray();
ZZ`SL2Cache["pscnts"] := [];
ZZ`SL2Cache["psindexes"] := [];
ZZ`SL2Cache["cclasses"] := AssociativeArray();
ZZ`SL2Cache["sclasses"] := AssociativeArray();
ZZ`SL2Cache["psclasses"] := AssociativeArray();

intrinsic GL2Cache() -> Assoc
{ returns GL2Cache }
   return ZZ`GL2Cache;
end intrinsic;

declare verbose GL2, 4;

// Magma won't let us create matrix groups over the ring Z/Z so we use the trivial subgroup of GL(n,Z) to represent the unique group of level 1 for n=1,2
gl1N1 := sub<GL(1,Integers())|>; gl1N1`Order := 1; gl1N1`Level := 1; gl1N1`Index := 1; gl1N1`NegOne := true;
sl1N1 := sub<SL(1,Integers())|>; sl1N1`Order := 1; sl1N1`Level := 1; sl1N1`Index := 1; sl1N1`NegOne := true; sl1N1`SL := true;
gl2N1 := sub<GL(2,Integers())|>; gl2N1`Order := 1; gl2N1`Level := 1; gl2N1`Index := 1; gl2N1`NegOne := true; gl2N1`Genus := 0;
sl2N1 := sub<SL(2,Integers())|>; sl2N1`Order := 1; sl2N1`Level := 1; sl2N1`Index := 1; sl2N1`NegOne := true; sl2N1`Genus := 0; sl2N1`SL := true;

declare attributes Assoc: SL;

declare attributes GrpMat: Level, Index, Genus, NegOne, SL; // NegOne can be true/false/unassigned but for SL, unassigned=false.
/*
    Note that SL doesn't just mean the group has determinant 1, it means that we view it as a subgroup of SL(Zhat), which is relevant when lifting, or interpreting Index.
    If H`SL is assigned then Index = [SL:H] and H`Order = #SL/H`Index, otherwise H`Index = [GL:H] and H`Order = #GL/H`Index.
    We need to be very careful about setting Order, since Magma uses this, it helps Magma if we set it (we can compute it much more quickly than Magma can via GL2Order and SL2Order),
    but if we set incorrectly this can lead to infinite loops in the Magma kernel (e.g. orbit computations may not terminate) that cannot be exited with killing Magma.
*/

/*** Internal helper functions ***/

// utility function to propogate attributes from Hold to Hnew when they represent the same subgroup of GL(2,Zhat) or SL(2,Zhat), for n=1,2
// this function should not be called when Hnew and Hold do not represent the same group (the caller should covert/assign attributes explicitly)
function gl2copyattr(Hnew,Hold)
    assert Degree(Hold) eq 2 and Degree(Hnew) eq 2;
    assert not assigned Hold`SL and not assigned Hnew`SL;
    M := #BaseRing(Hnew); N := #BaseRing(Hold); assert IsFinite(M) and IsFinite(N);
    if assigned Hold`NegOne then Hnew`NegOne := Hold`NegOne; end if;
    if assigned Hold`Genus then Hnew`Genus := Hold`Genus; end if;
    if assigned Hold`Level then
        assert IsDivisibleBy(N,Hold`Level) and IsDivisibleBy(M,Hold`Level);
        assert assigned Hold`Index and assigned Hold`Order;
        Hnew`Level := Hold`Level; Hnew`Index := Hold`Index; Hnew`Order := ExactQuotient(GL2Size(M),Hnew`Index);
        if assigned Hold`NegOne then Hnew`NegOne := Hold`NegOne; end if;
        return Hnew;
    end if;
    assert IsDivisibleBy(M,N);
    if assigned Hold`Index then
        assert assigned Hold`Order;
        Hnew`Index := Hold`Index; Hnew`Order := ExactQuotient(GL2Size(M),Hnew`Index);
        return Hnew;
    end if;
    if assigned Hold`Order then
        Hnew`Index := ExactQuotient(GL2Size(N),Hold`Order); Hnew`Order := ExactQuotient(GL2Size(M),Hnew`Index);
    end if;
    return Hnew;
end function;

function gl1copyattr(Hnew,Hold)
    assert Degree(Hold) eq 1 and Degree(Hnew) eq 1;
    assert not assigned Hold`SL and not assigned Hnew`SL;
    M := #BaseRing(Hnew); N := #BaseRing(Hold); assert IsFinite(M) and IsFinite(N);
    if assigned Hold`NegOne then Hnew`NegOne := Hold`NegOne; end if;
    if assigned Hold`Level then
        assert IsDivisibleBy(N,Hold`Level) and IsDivisibleBy(M,Hold`Level);
        assert assigned Hold`Index and assigned Hold`Order;
        Hnew`Level := Hold`Level; Hnew`Index := Hold`Index; Hnew`Order := ExactQuotient(EulerPhi(M),Hnew`Index);
        if assigned Hold`NegOne then Hnew`NegOne := Hold`NegOne; end if;
        return Hnew;
    end if;
    assert IsDivisibleBy(M,N);
    if assigned Hold`Index then
        assert assigned Hold`Order;
        Hnew`Index := Hold`Index; Hnew`Order := ExactQuotient(EulerPhi(M),Hnew`Index);
        return Hnew;
    end if;
    if assigned Hold`Order then
        Hnew`Index := ExactQuotient(EulerPhi(N),Hold`Order); Hnew`Order := ExactQuotient(EulerPhi(M),Hnew`Index);
    end if;
    return Hnew;
end function;

function sl2copyattr(Hnew,Hold)
    assert Degree(Hold) eq 2 and Degree(Hnew) eq 2;
    assert assigned Hold`SL; Hnew`SL := true;
    M := #BaseRing(Hnew); N := #BaseRing(Hold); assert IsFinite(M) and IsFinite(N);
    if assigned Hold`NegOne then Hnew`NegOne := Hold`NegOne; end if;
    if assigned Hold`Genus then Hnew`Genus := Hold`Genus; end if;
    if assigned Hold`Level then
        assert IsDivisibleBy(N,Hold`Level) and IsDivisibleBy(M,Hold`Level);
        assert assigned Hold`Index and assigned Hold`Order;
        Hnew`Level := Hold`Level; Hnew`Index := Hold`Index; Hnew`Order := ExactQuotient(SL2Size(M),Hnew`Index);
        if assigned Hold`NegOne then Hnew`NegOne := Hold`NegOne; end if;
        return Hnew;
    end if;
    assert IsDivisibleBy(M,N);
    if assigned Hold`Index then
        assert assigned Hold`Order;
        Hnew`Index := Hold`Index; Hnew`Order := ExactQuotient(SL2Size(M),Hnew`Index);
        return Hnew;
    end if;
    if assigned Hold`Order then
        Hnew`Index := ExactQuotient(SL2Size(N), Hold`Order); Hnew`Order := ExactQuotient(SL2Size(M),Hnew`Index);
    end if;
    return Hnew;
end function;

lmset  := func<M|a where a:=Sort([r cat [Multiplicity(M,r)]:r in Set(M)])>;   // encodes a multiset of lists of integers as a list of lists of integers
llmset := func<M|a where a:=Sort([r cat [[Multiplicity(M,r)]]:r in Set(M)])>; // encodes a multiset of lists of lists of integers as a list of lists of lists of integers
isscalar := func<M|M[1][1] eq M[2][2] and M[1][2] eq 0 and M[2][1] eq 0>;

function djb2(s) h := 5381; s := BinaryString(s); for i:=1 to #s do h := BitwiseAnd(33*h+s[i],18446744073709551615); end for; return h; end function;

// precomputed by GL1CanonicalGenerators, do not change this (ever)
gl1gens := [[],[],[2],[3],[2],[5],[3],[7,5],[2],[7],[2],[7,5],[2],[3],[11,7],[15,5],[3],[11],[2],[11,17],[8,10],[13],[5],[7,13,17],[2],[15],[2],[15,17],[2],[11,7],[3],[31,5],[23,13],[3],[22,31],[19,29],[2],[21],[14,28],[31,21,17],[6],[29,31],[3],[23,13],[11,37],[5],[5],[31,37,17],[3],[27],[35,37],[27,41],[2],[29],[12,46],[15,29,17],[20,40],[31],[2],[31,41,37],[2],[3],[29,10],[63,5],[27,41],[23,13],[2],[35,37],[47,28],[57,31],[7],[55,37,65],[5],[39],[26,52],[39,21],[45,57],[53,67],[3],[31,21,17],[2],[47],[2],[43,29,73],[52,71],[3],[59,31],[23,45,57],[3],[11,37],[66,15],[47,5],[32,34],[5],[77,21],[31,37,65],[5],[3],[56,46],[51,77],[2],[35,37],[5],[79,53,41],[71,22,31],[55],[2],[55,29],[6],[67,101],[38,76],[15,85,17],[3],[77,97],[47,51],[59,89],[92,28],[61],[52,71],[31,61,41,97],[2],[63],[83,88],[63,65],[2],[29,73],[3],[127,5],[44,46],[27,41],[2],[67,89,13],[115,78],[69],[56,82],[103,69,105],[3],[47,97],[2],[71,57,101],[95,52],[7],[79,67],[127,37,65],[117,31],[5],[50,52],[75,113],[2],[101,127],[6],[39,77,97],[137,37],[45,57],[32,96],[79,53,145],[5],[3],[107,55],[31,101,97],[24,120],[83],[2],[83,129],[56,67,46],[85],[5],[127,85,113,73],[2],[137,71],[20,154],[87,89],[2],[59,31],[127,101],[111,133,145],[119,61],[3],[2],[91,101,37],[2],[157,15],[62,124],[47,93,97],[112,76],[125,127],[35,122],[95,5],[29,136],[77,21],[19],[127,133,65],[5],[5],[131,157,106],[99,101],[2],[155,145],[3],[151,101,177],[68,136],[103],[59,176],[103,137,37],[42,6],[5],[47,28],[79,53,145],[134,78],[71,127,31],[2],[107,161],[143,7],[109],[87,46],[55,109,137],[94,127],[115],[74,151],[111,177,101],[171,105],[149,187],[3],[127,197,129],[101,127],[3],[2],[115,77,97],[6],[47,51],[155,199,211],[175,117,89],[3],[209,145],[142,146],[119,61],[80,82],[171,71],[7],[31,181,161,97],[7],[123],[2],[123,185],[197,101],[83,211],[210,40],[63,125,65],[167,85],[127],[6],[127,29,73],[24,166],[3],[86,52,241],[255,5],[3],[173,175],[38,113],[131,157,41],[146,118],[133],[5],[199,133,89,145],[107,161],[115,211],[179,181],[135,69],[2],[191,217],[6],[239,69,241],[92,157,106],[3],[177,101],[139,185,97],[5],[141],[218,127],[71,141,57,241],[3],[95,193],[3],[143,149],[191,172,211],[79,67],[206,211],[127,37,65],[3],[117,31],[98,199],[147,5],[2],[197,199],[237,61],[223,149,113],[56,244],[151],[93,235],[151,101,277],[87,218],[157],[203,103],[191,229,97],[62,246],[137,37],[5],[155,45,57],[104,211],[187,251],[17],[79,157,209,145],[10],[5],[281,127,136],[159,161],[2],[107,55],[233,89],[191,261,257],[215,109],[185,281],[20,154],[163,245],[27,301],[165],[110,115],[247,165,129],[283,99],[221,67,211],[3],[167,85],[38,298],[5],[202,136],[127,85,113,241],[10],[171],[227,229],[171,137,241],[156,34],[191,325],[3],[87,173,89],[116,277,166],[175],[2],[175,233,205],[2],[127,101],[326,28],[287,133,321],[3],[119,61],[72,291],[179,181],[239,52,190],[181],[7],[271,181,281,217],[2],[183],[122,244],[183,157,197],[147,151],[245,307],[6],[47,277,97],[83,334],[297,261],[213,267],[187,125,313],[2],[35,309],[251,127],[95,189,193],[262,118],[29,325],[2],[191,77,21],[128,130],[19],[5],[127,133,257],[232,276,211],[5],[173,46],[195,5],[2],[131,157,301],[139,120],[295,197,297],[263,133],[199],[317,161],[199,353,145],[5],[3],[134,115,211],[351,101,177],[3],[269,337],[249,313],[203,305],[326,82],[59,379],[112,298],[103,205,137,241],[21],[247,211],[275,277],[207,5],[178,120],[47,235],[167,251],[287,261,353],[140,280],[343,287],[2],[211,281,337,241],[2],[213],[236,334],[319,213,161],[52,326],[143,7],[367,246],[215,109],[287,79,67],[87,261],[7],[271,325,353],[5],[311,127],[146,262,31],[219,333],[116,419],[293,151],[15],[111,221,177,321],[344,199],[171,105],[2],[223,149,409],[357,181],[3],[299,151],[127,197,129],[3],[101,127],[288,375],[227,229],[152,157],[229],[92,66,106],[343,229,305,97],[13],[235],[137,190],[231,277,281],[2],[155,199,211],[3],[175,117,321],[311,187,406],[3],[2],[235,209,145],[269,337],[377,381],[158,319],[119,237,297],[431,89],[317,319],[77,401],[239,409,309],[425,55],[7],[13],[31,421,161,97],[223,261],[7],[323,346,442],[243,365],[292,296],[245],[3],[367,245,185],[164,328],[197,101],[2],[247,329,457],[88,205],[457,287],[56,397,46],[63,373,65],[143,78],[167,85],[7],[251,377],[335,172],[257],[5],[127,253,281,73],[102,406],[277,419],[170,340],[255,257],[2],[341,307,241],[220,78],[511,5],[191,325],[3],[207,211],[259,173,433],[189,287],[297,113],[347,175],[391,261,417,41],[3],[407,379],[2],[263,133],[176,127,451],[5],[156,375],[463,133,353,145],[5],[107,161],[119,415],[267,381,477],[288,170],[179,181],[322,216],[135,269,337],[359,181],[271],[199,442],[271,461,217],[2],[277],[182,364],[511,69,513],[437,6],[365,157,379],[2],[275,277],[245,307],[177,101],[59,495],[415,277,185,97],[80,477],[5],[371,112,76],[279,141],[2],[497,127],[431,261],[351,421,337,241],[188,409,496],[3],[2],[283,377,193],[227,116],[3],[407,325],[143,285,433],[3],[191,457,211],[3],[287,365,353],[383,19],[493,211],[277,51],[127,325,65],[5],[3],[194,391],[291,117,321],[416,85],[389,199],[266,320],[439,293,297],[326,352,496],[295],[2],[295,197,493],[249,96],[237,61],[395,199],[223,149,113],[3],[353,541],[477,171,71],[299,449],[200,202],[93,235],[7],[151,301,401,577],[7],[87,519],[470,136],[303,157],[122,486],[203,103],[3],[191,229,97],[407,262,379],[367,551],[236,287],[307,137,37],[2],[5],[206,247,211],[463,309,353,57],[3],[413,211],[2],[311,497,561],[461,28],[17],[535,92],[79,469,209,145],[2],[323],[419,343,496],[315,5],[445,409],[281,127,451],[3],[159,317,161],[212,424],[319],[382,511],[319,425,373],[248,197],[233,89],[569,433],[511,261,257],[3],[215,109],[11],[323,185,281],[431,517,46],[343,477],[5],[487,325,569],[178,474],[27,301],[218,94,127],[327,165],[2],[437,115],[132,526],[575,165,129],[74,370],[283,99],[2],[331,221,397,541],[2],[3],[443,613,547],[167,333,417],[267,381,211],[371,631],[465,553],[335,5],[224,226],[537,471],[123,551],[127,421,449,577],[5],[347],[326,352],[339,509],[2],[227,229],[486,393],[511,341,137,241],[455,229],[497,375],[5],[343,533,325],[412,551],[3],[230,235],[431,517,433],[54,638],[461,277,511],[3],[347,521],[155,199,442],[349],[557,141],[175,349,233,553],[411,375],[351],[467,469],[351,477,101],[2],[677,379],[667,39],[639,133,321],[236,142,616],[3],[304,204],[355,473,61],[2],[427,291],[317,82],[535,357,537],[373,530],[239,409,547],[287,651,496],[359,181],[479,7],[7],[11],[271,181,641,577],[619,211],[363],[242,7],[363,545],[552,176],[485,607],[5],[183,365,521,561],[2],[147,151],[173,562],[367,245,673],[6],[373],[491,442,346],[415,645,97],[68,672],[83,703],[3],[371,297,261],[248,457,40],[213,267],[5],[559,373,497,313],[597,151],[375],[416,334],[375,409,309],[108,323],[251,127],[3],[95,565,193],[503,508],[639,495],[152,6],[379,29,325],[2],[381],[254,277,166],[191,381,457,401],[6],[509,511],[437,442],[383,401],[596,307,496],[5],[119,651],[511,517,257],[11],[617,661,211],[515,517],[387,5],[2],[173,433],[652,251],[583,389,393],[260,556,631],[391],[534,457],[391,521,157,301],[640,78],[139,511],[407,379],[687,197,689],[472,476],[263,133],[2],[395,593],[527,268],[317,161],[227,568],[199,397,353,145],[184,612],[5],[266,637,691],[399,401],[2],[533,115,211],[377,52],[351,101,577],[713,181],[3],[585,78],[403,269,337],[162,346,281],[249,313],[539,271],[607,405,305],[3],[731,487],[3],[407,465,785],[272,277],[519,705],[327,491],[511,613,545,241],[173,476],[21],[92,703,379],[411,657,621],[2],[275,277],[3],[207,413,417],[551,727,376],[591,533],[2],[415,461,649],[2],[167,251],[278,559],[703,261,769],[52,785],[557,697],[502,506],[419,761,705],[218,406],[421],[11],[631,421,281,337,241],[2],[423],[563,565],[423,213],[677,171],[659,757],[122,365],[319,213,161],[284,286],[477,751],[741,668],[427,569,433],[2],[367,673],[191,172,496],[215,429,537],[3],[287,79,67],[2],[431,517,261],[575,493,211],[7],[5],[703,325,353],[347,521],[5],[290,292],[435,745,561],[475,793],[581,697,31],[470,404],[655,437,769],[389,199],[553,419],[127,626],[439,293,589],[2],[15],[587,295],[111,661,177,321],[3],[785,199],[2],[443,613,105],[296,532,61],[445],[5],[223,445,593,409],[255,638],[357,181],[650,244],[447,449],[800,381],[299,151],[717,181],[127,645,129],[599,691,235],[3],[466,871],[451,101,577],[54,426],[739,375],[302,388,820],[679,453,681],[182,726],[605,157],[2],[455,229],[506,406],[547,521,561],[17],[799,229,305,97],[167,749],[13],[611,367,856],[459,693],[787,526],[137,649],[7],[231,461,737,281],[308,619],[463],[782,859],[463,617,661,673],[852,76],[3],[722,829],[639,581,321],[3],[311,187,871],[248,344],[467,469],[623,328],[469],[562,596,496],[703,469,209,145],[5],[269,337],[314,10],[471,377,381],[2],[629,319],[534,47],[591,709,769],[596,757,136],[431,89],[2],[475,317,793],[366,443],[77,401],[635,319],[239,477,409,785],[3],[425,55],[192,401],[479,485],[320,871,727],[13],[549,414],[511,901,641,577],[3],[223,261],[857,109],[483,489],[387,391],[323,829,925],[5],[727,485,849],[647,343,154],[777,781],[6],[487,245],[696,141],[3],[326,352,301],[367,245,673],[3],[653,817],[90,804],[491,197,101],[110,442],[493],[5],[247,493,329,457],[592,396],[581,205],[659,283,757],[495,457,781],[603,691],[551,397,541],[6],[63,869,65],[332,334],[143,575],[797,401],[499,665,85],[7],[7],[704,298],[751,501,377]];
gl1screps := [[1],[1],[1,2],[1,3],[1,2],[1,5],[1,3],[1,3,5,7],[1,2],[1,3],[1,2],[1,5,7,11],[1,2],[1,3],[1,2,7,11],[1,3,5,7],[1,3],[1,5],[1,2],[1,3,11,13],[1,2,5,10],[1,7],[1,5],[1,5,7,11,13,17,19,23],[1,2],[1,5],[1,2],[1,3,5,11],[1,2],[1,7,11,17],[1,3],[1,3,5,7],[1,2,5,7],[1,3],[1,2,3,6],[1,5,7,11],[1,2],[1,3],[1,2,7,14],[1,3,7,11,13,17,21,31],[1,3],[1,5,11,13],[1,2],[1,3,7,13],[1,2,7,11],[1,5],[1,5],[1,5,7,11,13,17,19,23],[1,3],[1,3],[1,2,5,7],[1,3,5,7],[1,2],[1,5],[1,2,3,6],[1,3,5,11,15,17,29,31],[1,2,5,10],[1,3],[1,2],[1,7,11,13,17,19,23,29],[1,2],[1,3],[1,2,5,10],[1,3,5,7],[1,2,3,6],[1,5,7,17],[1,2],[1,3,5,15],[1,2,5,7],[1,3,19,23],[1,7],[1,5,7,11,13,17,19,23],[1,5],[1,5],[1,2,7,11],[1,3,7,13],[1,2,3,6],[1,5,7,17],[1,3],[1,3,7,11,13,17,21,31],[1,2],[1,3],[1,2],[1,5,11,13,19,29,43,47],[1,2,3,6],[1,3],[1,2,5,10],[1,3,5,7,13,15,17,19],[1,3],[1,7,11,17],[1,2,3,5],[1,3,5,7],[1,2,11,13],[1,5],[1,2,7,14],[1,5,7,11,13,17,19,23],[1,5],[1,3],[1,2,5,7],[1,3,11,13],[1,2],[1,5,7,35],[1,3],[1,3,5,7,11,23,29,33],[1,2,11,13,17,19,22,26],[1,3],[1,2],[1,5,7,11],[1,2],[1,3,7,19],[1,2,11,13],[1,3,5,11,15,17,29,31],[1,3],[1,5,13,29],[1,2,7,11],[1,3,7,17],[1,2,7,14],[1,11],[1,3,11,13],[1,7,11,13,17,19,23,29,31,41,43,53,61,71,73,83],[1,2],[1,7],[1,2,7,11],[1,3,7,13],[1,2],[1,5,11,13],[1,3],[1,3,5,7],[1,2,7,11],[1,3,7,11],[1,2],[1,5,7,13,17,23,31,35],[1,2,3,5],[1,3],[1,2,7,11],[1,3,5,7,13,15,19,41],[1,3],[1,5,7,29],[1,2],[1,3,11,13,19,23,37,41],[1,2,5,10],[1,7],[1,2,5,10],[1,5,7,11,13,17,19,23],[1,2,7,11],[1,5],[1,2,5,10],[1,3,5,15],[1,2],[1,7,11,17],[1,3],[1,3,5,7,11,13,15,33],[1,2,5,7],[1,3,13,29],[1,2,3,6],[1,5,7,11,17,23,37,43],[1,2],[1,3],[1,2,11,19],[1,3,7,11,13,17,21,31],[1,3,5,11],[1,5],[1,2],[1,3,13,23],[1,2,7,14,19,23,29,37],[1,5],[1,5],[1,5,11,13,17,19,23,29,31,37,43,47,59,65,73,79],[1,2],[1,3,11,13],[1,2,5,10],[1,3,5,11],[1,2],[1,5,11,19],[1,2,3,6],[1,3,5,7,13,15,17,19],[1,2,5,10],[1,3],[1,2],[1,7,11,13,17,19,23,29],[1,2],[1,3,5,11],[1,2,5,7],[1,3,5,7,11,13,17,31],[1,2,3,6],[1,5,11,13],[1,2,3,6],[1,3,5,11],[1,2,5,10],[1,3,7,21],[1,7],[1,5,7,11,13,17,19,23],[1,5],[1,5],[1,2,7,11,14,17,19,22],[1,3,5,11],[1,2],[1,5,7,17],[1,3],[1,3,7,11,13,17,21,31],[1,2,7,14],[1,3],[1,2,3,5],[1,5,7,11,19,35,37,53],[1,2,3,6],[1,3],[1,2,5,7],[1,3,5,7,11,23,29,33],[1,2,3,6],[1,11,13,17,19,23,37,41],[1,2],[1,3,5,7],[1,2,7,11],[1,5],[1,2,13,19],[1,5,7,11,13,17,19,23],[1,3,5,11],[1,11],[1,2,5,7],[1,3,7,13,19,21,31,37],[1,2,3,5],[1,5,11,13],[1,3],[1,3,5,11,15,17,29,31],[1,2,7,11],[1,3],[1,2],[1,5,7,11,13,29,31,59],[1,2],[1,3,7,11],[1,2,5,10,17,23,31,43],[1,3,5,7,15,17,21,35],[1,3],[1,5,7,17],[1,2,11,13],[1,3,11,13],[1,2,7,14],[1,3,11,13],[1,7],[1,7,11,13,17,19,23,29,31,41,43,53,61,71,73,83],[1,7],[1,7],[1,2],[1,3,7,17],[1,2,3,6],[1,5,7,11],[1,2,3,5],[1,3,5,7,13,15,17,19],[1,2,11,13],[1,3],[1,2],[1,5,11,13,19,29,43,47],[1,2,5,7],[1,3],[1,2,7,11,13,23,26,31],[1,3,5,7],[1,3],[1,5,7,11],[1,2,3,5],[1,3,7,11,17,21,33,51],[1,2,5,10],[1,17],[1,5],[1,5,7,13,17,19,23,29,31,35,37,59,67,73,89,95],[1,2,7,14],[1,3,5,15],[1,2,7,14],[1,3,5,15],[1,2],[1,7,11,17],[1,3],[1,3,5,7,13,15,19,41],[1,2,5,10,17,19,23,37],[1,3],[1,2,3,6],[1,5,7,11,29,31,35,37],[1,2],[1,3],[1,2,11,13],[1,3,11,13,17,19,23,29,31,37,39,41,43,47,57,61],[1,3],[1,5,13,17],[1,2],[1,3,7,13],[1,2,7,11,13,14,17,31],[1,5,7,17],[1,3,5,11],[1,5,7,11,13,17,19,23],[1,3],[1,3,7,11],[1,2,5,7],[1,3,5,7],[1,2],[1,5,11,13],[1,2,3,6],[1,3,5,7,15,17,19,21],[1,2,5,7],[1,3],[1,2,5,10],[1,7,11,13,17,19,23,29],[1,2,3,6],[1,3],[1,2,5,7],[1,3,5,7,11,13,15,33],[1,2,3,6],[1,5,7,35],[1,2],[1,3,5,13,15,19,29,39],[1,2,5,10],[1,3,7,11],[1,11],[1,5,7,11,17,19,23,29,35,37,41,43,47,55,61,73],[1,5],[1,5],[1,2,11,13,17,19,22,26],[1,3,11,17],[1,2],[1,5,11,19],[1,2,3,6],[1,3,7,11,13,17,21,31],[1,2,7,11],[1,3,5,11],[1,2,3,5],[1,5,7,11],[1,2,3,6],[1,3],[1,2,5,10],[1,3,5,7,13,17,23,43],[1,3,5,11],[1,7,17,19,23,29,37,59],[1,2],[1,3,5,15],[1,2,11,13],[1,5],[1,2,11,17],[1,5,11,13,17,19,23,29,31,37,43,47,59,65,73,79],[1,5],[1,5],[1,2,5,10],[1,3,11,13,19,29,37,43],[1,2,3,6],[1,5,13,29],[1,3],[1,3,5,7,11,13,15,33],[1,2,7,11,13,17,19,26],[1,3],[1,2],[1,5,7,11,17,19,23,37],[1,2],[1,3,19,23],[1,2,7,14],[1,3,5,7,13,15,17,19],[1,3],[1,5,11,13],[1,2,7,11],[1,3,11,13],[1,2,5,10,11,13,22,26],[1,7],[1,7],[1,7,11,13,17,19,23,29,31,41,43,53,61,71,73,83],[1,2],[1,7],[1,2,5,7],[1,3,5,11,17,19,23,37],[1,2,7,11],[1,5,7,11],[1,3],[1,3,5,7,11,13,17,31],[1,2,7,11],[1,3,13,19],[1,2,3,6],[1,5,7,11,13,17,35,43],[1,2],[1,3,7,13],[1,2,7,11],[1,3,5,7,11,15,21,33],[1,2,3,5],[1,5,11,13],[1,2],[1,3,7,11,13,17,21,31],[1,2,5,7],[1,7],[1,5],[1,5,7,11,13,17,19,23],[1,2,3,6,13,23,26,29],[1,5],[1,2,7,11],[1,3,5,7],[1,2],[1,7,11,17,19,29,43,47],[1,3,5,15],[1,3,5,11,15,17,29,31],[1,2,5,10],[1,3],[1,2,3,6],[1,5,7,13,17,23,31,35],[1,2],[1,3],[1,2,5,10,11,22,41,55],[1,3,7,11,13,17,21,31],[1,3],[1,5,7,17],[1,2,3,6],[1,3,19,29],[1,2,7,11],[1,3,5,11],[1,2,5,7],[1,5,7,11,13,19,23,35,37,41,47,53,55,73,89,91],[1,7],[1,3,11,23],[1,2,5,10],[1,3,5,7],[1,2,3,6],[1,5,7,29],[1,2,3,6],[1,3,5,7,11,23,29,33],[1,2,5,10],[1,3,7,13],[1,2],[1,11,13,17,19,23,29,37,41,43,47,53,59,61,79,103],[1,2],[1,3],[1,2,5,10],[1,3,5,7,11,13,23,33],[1,2,3,6],[1,5,7,11],[1,2,3,6],[1,3,5,7],[1,2,5,7,10,14,17,31],[1,3,13,19],[1,7],[1,5,7,11,13,17,19,23],[1,5],[1,3,5,11],[1,2,7,11,19,23,37,59],[1,3,11,13],[1,2,5,10],[1,5,7,23],[1,3],[1,3,7,13,17,19,21,23,31,37,39,41,43,59,69,97],[1,2,5,10],[1,3,5,15],[1,2],[1,5,7,11,13,19,23,41],[1,2,3,6],[1,3],[1,2,5,10],[1,3,5,11,15,17,29,31],[1,3],[1,7,11,17],[1,2,3,6],[1,3,5,7],[1,2,7,14],[1,5],[1,2,3,6,11,22,33,61],[1,5,7,11,13,17,23,29,31,41,43,59,61,67,71,97],[1,5],[1,7],[1,2,5,7],[1,3,7,11,13,17,21,31],[1,2],[1,5,13,17,23,29,31,43],[1,3],[1,3,5,7,15,17,21,35],[1,2,7,11,13,14,17,34],[1,3],[1,2],[1,5,7,11,17,23,37,43],[1,2,3,6],[1,3,11,13],[1,2,7,11],[1,3,5,7,11,13,23,33],[1,2,3,6],[1,5,7,17],[1,2,7,14],[1,3,5,11,13,15,19,29],[1,2,11,19],[1,7],[1,13],[1,7,11,13,17,19,23,29,31,41,43,53,61,71,73,83],[1,2,7,14],[1,7],[1,2,5,10,11,13,22,26],[1,3,7,13],[1,2,7,14],[1,5],[1,3],[1,3,5,7,11,15,17,21],[1,2,7,14],[1,3,19,23],[1,2],[1,5,7,11,13,17,23,31],[1,2,3,5],[1,3,5,15],[1,2,7,14,19,23,29,37],[1,3,5,7,13,15,17,19],[1,3,11,13],[1,5,11,13],[1,2],[1,3,11,13],[1,2,5,10],[1,11],[1,5],[1,5,11,13,17,19,23,29,31,37,43,47,59,65,73,79],[1,2,11,13],[1,5,7,13],[1,2,7,14],[1,3,5,11],[1,2],[1,7,11,13,23,31,47,59],[1,3,5,11],[1,3,5,7],[1,2,5,10],[1,3],[1,2,3,6],[1,5,7,11,17,31,37,71],[1,2,5,10],[1,3,5,15],[1,2,7,14],[1,3,7,11,17,21,23,29,31,33,37,41,51,53,67,79],[1,3],[1,5,11,19],[1,2],[1,3,17,19],[1,2,11,13,17,19,22,26],[1,5],[1,3,5,13],[1,5,7,13,17,19,23,29,31,35,37,59,67,73,89,95],[1,5],[1,3,7,19],[1,2,5,10],[1,3,5,11,13,15,29,47],[1,2,3,6],[1,5,7,23],[1,2,3,6],[1,3,5,7,15,19,21,41],[1,2,5,7],[1,3],[1,2,3,6],[1,7,11,13,17,19,23,29],[1,2],[1,3],[1,2,5,7],[1,3,5,7,13,15,19,41],[1,2,3,6],[1,5,11,17,19,23,37,55],[1,2],[1,3,5,7],[1,2,5,7],[1,3,7,19],[1,2,11,13],[1,5,7,11,13,17,19,29,31,35,37,41,47,97,139,143],[1,3,5,15],[1,5],[1,2,7,11,13,14,19,38],[1,3,7,17],[1,2],[1,5,11,13],[1,2,3,6],[1,3,11,13,17,19,23,29,31,37,39,41,43,47,57,61],[1,2,5,7,13,26,29,31],[1,3],[1,2],[1,5,7,11,13,17,19,59],[1,2,3,6],[1,3],[1,2,5,10],[1,3,5,7,11,13,15,17],[1,3],[1,7,11,13,17,29,31,53],[1,2],[1,3,5,7,15,17,21,35],[1,2,7,11],[1,3,5,11],[1,2,7,11],[1,5,7,11,13,17,19,23],[1,5],[1,3],[1,2,5,10],[1,3,7,11,13,17,21,51],[1,2,3,5],[1,5,7,11],[1,2,3,6],[1,3,5,7,11,17,23,37],[1,2,7,11,14,17,19,22],[1,3],[1,2],[1,5,11,13,19,29,43,47],[1,2,3,6],[1,3,11,13],[1,2,13,23],[1,3,5,7,15,17,19,21],[1,3],[1,5,7,17],[1,2,3,6,11,13,19,22],[1,3,7,13],[1,2,11,19],[1,5,17,31],[1,7],[1,7,11,13,17,19,23,29,31,41,43,53,61,71,73,83],[1,7],[1,3,13,29],[1,2,7,14],[1,3,11,13],[1,2,3,6],[1,5,7,11],[1,3],[1,3,5,7,11,13,15,33],[1,2,5,10,13,17,23,37],[1,3,7,11],[1,2,5,10],[1,5,7,11,19,35,37,53],[1,2],[1,3],[1,2,7,11,17,19,37,59],[1,3,5,13,15,17,19,29,31,37,39,43,57,67,87,89],[1,3],[1,5,17,31],[1,2],[1,3,7,11,13,19,21,33],[1,2,5,7],[1,11],[1,3,5,15],[1,5,7,11,17,19,23,29,35,37,41,43,47,55,61,73],[1,2],[1,5],[1,2,5,7,10,14,17,31],[1,3,5,7],[1,2,3,5],[1,11,13,17,19,23,37,41],[1,3],[1,3,5,7,11,17,23,29],[1,2,5,7],[1,3],[1,2,3,6],[1,5,7,11,17,19,23,61],[1,2,3,5],[1,3,7,17],[1,2,7,11],[1,3,7,11,13,17,21,31],[1,3],[1,5,7,11],[1,2],[1,3,5,11,13,19,37,39],[1,2,7,11,13,17,19,26],[1,3,5,13],[1,5],[1,5,7,11,13,17,19,23],[1,2,7,14],[1,3,7,11],[1,2,5,10,11,13,17,22],[1,3,5,15],[1,2],[1,5,11,13],[1,2,3,6],[1,3,5,7,13,17,23,43],[1,2,5,7],[1,3,5,11],[1,2],[1,7,13,17,19,23,29,31,37,53,59,61,67,83,89,131],[1,2],[1,3],[1,2,5,7,10,14,19,35],[1,3,5,7,15,19,21,57],[1,2,3,6,17,23,29,31],[1,5,11,13],[1,2,5,10],[1,3,5,15],[1,2,5,10],[1,3,11,17],[1,2,13,23],[1,5,11,13,17,19,23,29,31,37,43,47,59,65,73,79],[1,5],[1,5],[1,2,7,11],[1,3,5,7],[1,2],[1,5,11,19],[1,3,5,15],[1,3,7,11,13,19,21,29,31,33,37,41,43,47,57,111],[1,2,11,13],[1,3,7,13],[1,2],[1,5,7,11,13,29,31,59],[1,2,3,6],[1,3],[1,2,5,7],[1,3,5,7,11,13,15,33],[1,2,3,6],[1,7,11,13,17,19,29,47],[1,2],[1,3,5,15],[1,2,5,10,17,23,31,43],[1,5],[1,2,7,14],[1,5,7,11,13,17,19,23,31,35,37,47,65,67,73,77],[1,3,5,13],[1,7],[1,2,5,10],[1,3,11,13,19,23,37,41],[1,2],[1,5,7,17],[1,2,3,5],[1,3,5,7,13,15,17,19],[1,2,7,11,13,14,19,23],[1,3],[1,2,3,5],[1,5,7,11,13,31,35,65],[1,2],[1,3,7,11],[1,2,7,14],[1,3,5,7,11,13,33,39],[1,3,5,11],[1,5,11,13,31,37,47,53],[1,2,3,6,17,29,31,37],[1,3,7,21],[1,2,7,14],[1,7],[1,11],[1,7,11,13,17,19,23,29,31,41,43,53,61,71,73,83],[1,3,11,13],[1,3],[1,2,7,11],[1,3,7,17],[1,2,7,11],[1,5,7,17],[1,3],[1,3,5,11,15,17,19,23,29,31,33,37,43,55,57,61],[1,2],[1,3,7,11],[1,2,3,6],[1,5,7,11,17,19,37,47],[1,2],[1,3],[1,2,11,13,17,19,22,26],[1,3,5,7,11,13,17,31],[1,2,3,6],[1,5,7,11],[1,2],[1,3,11,13,19,23,29,33],[1,2,5,7,10,14,17,31],[1,3,13,23],[1,5],[1,5,7,11,13,17,19,23,29,35,41,43,47,55,73,109],[1,2,7,11],[1,5],[1,2,11,13],[1,3,5,7,13,15,19,29],[1,2,3,5],[1,7,11,17],[1,3],[1,3,5,7,11,15,21,33],[1,2,5,10],[1,3,5,11],[1,2,3,6],[1,5,11,13,19,29,43,47],[1,2],[1,3],[1,2,5,7,13,17,26,34],[1,3,7,11,13,17,21,31,33,39,41,43,51,61,77,103],[1,3],[1,5,7,11],[1,2,3,6],[1,3,7,21],[1,2,7,11,13,23,26,31],[1,5],[1,2,5,10],[1,5,7,11,13,17,19,23],[1,7],[1,3,13,19,23,29,31,43],[1,2,5,7],[1,3,5,11],[1,2],[1,5,7,11],[1,2,3,6],[1,3,5,7,17,19,31,53],[1,2,5,10,11,13,22,26],[1,3],[1,2,3,6],[1,7,11,17,19,23,29,37,41,43,47,79,109,131,133,137],[1,2,7,14],[1,3,5,15],[1,2,5,10],[1,3,5,11,15,17,29,31],[1,2,3,6],[1,5,17,19],[1,2],[1,3,5,7],[1,2,5,7],[1,3,13,29],[1,3,13,23],[1,5,7,13,17,19,23,29,31,35,37,59,67,73,89,95],[1,2,5,10],[1,5],[1,2,7,11,14,17,19,22],[1,3,7,17],[1,2],[1,5,11,13,29,37,41,55],[1,3,5,13],[1,3,7,11,13,17,21,31],[1,2,7,14],[1,3],[1,2,5,7],[1,5,7,11,13,17,19,23],[1,2,3,6,11,17,19,22],[1,3,5,11],[1,2,5,7],[1,3,5,7,19,23,29,41],[1,3],[1,7,11,17],[1,2],[1,3,5,11,17,23,37,59],[1,2,13,23],[1,5,7,13],[1,2,11,22],[1,5,7,11,13,19,23,35,37,41,47,53,55,73,89,91],[1,2,5,10],[1,7],[1,2,5,10,17,19,23,37],[1,3,11,13,23,29,31,33],[1,2],[1,5,11,13],[1,3],[1,3,5,7,13,19,31,57],[1,2,7,14,19,23,29,37],[1,3,11,13],[1,2],[1,5,7,11,29,31,35,37],[1,2],[1,3,13,19],[1,2,23,31],[1,3,5,7,11,23,29,33],[1,3,11,13],[1,5,17,19],[1,2,13,26],[1,3,7,13,17,23,37,51],[1,2,11,13],[1,11],[1,11],[1,11,13,17,19,23,29,31,37,41,43,47,53,59,61,71,73,79,83,101,103,107,109,113,127,173,187,193,211,241,281,311],[1,2],[1,13],[1,2,11,13],[1,3,11,17],[1,2,3,6],[1,5,13,17],[1,2,3,6],[1,3,5,7,11,13,23,33],[1,2,11,19],[1,3,11,13],[1,2,5,7],[1,5,7,11,13,17,19,83],[1,2],[1,3,11,17],[1,2,7,11,13,14,17,31],[1,3,5,7,13,17,23,43],[1,3],[1,5,7,17,23,31,41,43],[1,2],[1,3,11,13,19,23,29,33],[1,2,5,10,11,13,17,22],[1,7],[1,5],[1,5,7,11,13,17,19,23],[1,2,11,13],[1,5],[1,2,5,7],[1,3,5,11,13,19,29,39],[1,2,3,6],[1,7,11,17,19,23,37,59],[1,2,3,6],[1,3,5,7,11,13,17,23],[1,2,5,7],[1,3,5,15],[1,2,3,6],[1,5,7,11,13,19,23,41],[1,2],[1,3],[1,2,7,14],[1,3,7,13,17,19,21,23,31,37,39,41,43,59,69,97],[1,3],[1,5,11,13],[1,2],[1,3,5,7,15,21,29,35],[1,2,7,11,13,17,26,31],[1,5],[1,5],[1,5,7,11,13,17,19,23,31,35,41,47,53,67,85,97],[1,3,13,23],[1,3,17,19],[1,2,5,7],[1,3,5,7],[1,2,5,10],[1,5,11,13],[1,2,3,6],[1,3,5,11,15,17,29,31],[1,2,5,7,10,14,29,31],[1,3],[1,2,3,6],[1,7,11,13,17,19,23,29],[1,2,3,6],[1,3,7,21],[1,2,5,10,11,17,19,22],[1,3,5,7,11,13,17,23],[1,2,3,6],[1,5,7,23],[1,2],[1,3,5,15],[1,2,5,7],[1,3,11,19,23,33,37,61],[1,7],[1,5,7,11,13,17,23,29,31,41,43,59,61,67,71,97],[1,2,5,7],[1,5],[1,2,7,11,13,14,31,47],[1,3,7,13],[1,2,3,6],[1,5,7,35],[1,3],[1,3,7,11,13,17,21,29,31,37,43,47,59,73,79,89],[1,2,11,13],[1,3],[1,2,7,14],[1,5,13,17,19,23,29,31,43,47,53,67,83,85,95,97],[1,2,3,6],[1,3],[1,2,5,10],[1,3,5,7,15,17,21,35],[1,3],[1,7,11,13,17,41,47,61],[1,2,3,5],[1,3,5,7],[1,2,11,19],[1,5],[1,2,3,6,7,14,19,38],[1,5,7,11,17,19,23,29,35,37,41,43,47,55,61,73],[1,5],[1,3,11,17],[1,2,5,7],[1,3,11,13,17,23,29,51],[1,2],[1,5,7,11],[1,3,5,7],[1,3,5,7,11,13,23,33],[1,2,11,13,17,19,22,26],[1,3,7,13],[1,2],[1,5,7,11,17,19,35,37],[1,2,5,10],[1,3,7,21],[1,2,11,13],[1,3,5,11,13,15,19,23,29,31,33,41,43,47,53,57],[1,3],[1,5,11,19],[1,2,7,11],[1,3,7,13],[1,2,5,7,10,14,31,35],[1,13],[1,3,17,23],[1,7,11,13,17,19,23,29,31,41,43,53,61,71,73,83],[1,3],[1,5,7,17],[1,2,7,11],[1,3,7,13],[1,2,11,13],[1,5,11,13,19,29,37,41],[1,3],[1,3,5,7,13,15,17,19],[1,2,5,7,10,13,14,26],[1,3,7,19],[1,2],[1,5,7,11],[1,2,3,5],[1,3],[1,2,7,11,14,17,19,22],[1,3,5,7,11,15,17,21],[1,3],[1,5,7,35],[1,2,3,6],[1,3,11,13,19,23,37,41],[1,2,5,10],[1,7],[1,5],[1,5,7,11,13,17,19,23,29,31,37,43,47,59,97,113],[1,2,7,11],[1,3,5,15],[1,2,5,10,11,17,22,34],[1,3,5,7,15,21,23,29],[1,2,5,10],[1,7,17,19,23,29,37,59],[1,3],[1,3,5,7,13,15,17,19],[1,2,5,7],[1,3,11,13],[1,2,3,6],[1,5,7,11,13,17,19,35],[1,2],[1,3],[1,2,11,13],[1,3,7,11,13,17,21,31]];

/*** GL1 functions ***/

intrinsic GL1Ambient(R::RngIntRes) -> GrpMat
{ Returns GL(1,R) with Order, Index, and Level attributes set. }
    G := GL(1,R); G`Order := EulerPhi(#R); G`NegOne := true; G`Index := 1; G`Level := 1;
    return G;
end intrinsic;

intrinsic GL1Ambient(N::RngIntElt) -> GrpMat
{ Returns GL(1,Z/NZ) (or trivial subgroup of GL(1,Z) when N=1) with Order, Index, NegOne, Level attributes set. }
    return N eq 1 select gl1N1 else GL1Ambient(Integers(N));
end intrinsic;

intrinsic GL1Order(H::GrpMat) -> RngIntElt
{ The index of H in its parent. }
    if assigned H`Order then return H`Order; end if;
    if not IsFinite(BaseRing(H)) then assert H eq gl1N1; return 1; end if;
    H`Order := #sub<M|[ipi(g[1][1]):g in Generators(H)]> where ipi := Inverse(pi) where M,pi:=MultiplicativeGroup(BaseRing(H));
    return H`Order;
end intrinsic;

intrinsic GL1Index(H::GrpMat) -> RngIntElt
{ The index of H in its parent. }
    if assigned H`Index then return H`Index; end if;
    if not IsFinite(BaseRing(H)) then assert H eq gl2N1; return [1]; end if;
    if not assigned H`Order then H`Order := GL1Order(H); end if;
    H`Index := EulerPhi(#BaseRing(H)) div H`Order;
    return H`Index;
end intrinsic;

intrinsic GL1Level(H::GrpMat) -> RngIntElt, GrpMat
{ The least integer N such that H is the full inverse image of its reduction modulo N, along with its reduction modulo N and its index. }
    require Degree(H) eq 1: "H should be a subgroup of GL(1,Z/NZ).";
    require not assigned H`SL: "H should be a subgroup of GL1 that is not marked as a subgroup of SL1.";
    N := #BaseRing(H);  if not IsFinite(N) then assert H eq gl1N1; return 1,gl1N1; end if;
    if assigned H`Level then return H`Level, N eq H`Level select H else gl1copyattr(ChangeRing(H,Integers(H`Level)),H); end if;
    cGL1 := EulerPhi(N);
    if not assigned H`Order then H`Order := GL1Order(H); end if;
    if not assigned H`Index then H`Index := cGL1 div H`Order; end if;
    if H`Order eq cGL1 then return 1,gl1N1; elif IsPrime(N) then H`Level := N; return H`Level,H; end if;
    M := N;
    for p in PrimeDivisors(N) do
        while N gt p and N mod p eq 0 and cGL1*GL1Order(ChangeRing(H,Integers(N div p))) eq EulerPhi(N div p)*H`Order do N div:= p; end while;
    end for;
    H`Level := N;
    return N, N eq M select H else gl1copyattr(ChangeRing(H,Integers(N)),H);
end intrinsic;

intrinsic GL1Lift(H::GrpMat,M::RngIntElt) -> GrpMat
{ The full preimage in GL(1,Z/MZ) of H in GL(1,Z/NZ) for a multiple M of N. }
    require Degree(H) eq 1: "H should be a subgroup of GL(1,Z/NZ).";
    require not assigned H`SL: "H should be a subgroup of GL1 that is not marked as a subgroup of SL1.";
    R := BaseRing(H); N := #R; if not IsFinite(N) then assert H eq gl1N1; return GL1Ambient(M); end if;
    if M eq N then return H; end if;
    require IsDivisibleBy(M,N): "Target level must be divisible by #BaseRing(H).";
    GL1 := GL(1,Integers(M));
    _,pi := ChangeRing(GL1,R);
    gens := [GL1![a]:a in {pi(g)^Order(R!pi(g)):g in Generators(m)}] where m,pi:=MultiplicativeGroup(Integers(M));
    return gl1copyattr(sub<GL1|gens,H @@ pi>,H); // this is fast
end intrinsic;

intrinsic GL1Project(H::GrpMat,M::RngIntElt) -> GrpMat
{ The projection to GL(2,Z/MZ) of the full preimage in GL(2,Z/LCM(M,N)Z) of H in GL(2,Z/NZ); here M may be any positive integer.
  If H`Level is set and M is a multiple of H`Level then the level (along with the known index and order) will be preserved. }
    require Degree(H) eq 1: "H should be a subgroup of GL(1,Z/NZ).";
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    N := #BaseRing(H); if not IsFinite(N) then assert H eq gl1N1; return GL1Ambient(M); end if;
    if M eq 1 then return gl1N1; elif N eq M then return H; end if;
    if not IsDivisibleBy(N,M) then N := LCM(M,N); H := GL1Lift(H,N); if N eq M then return H; end if; end if;
    return assigned H`Level and IsDivisibleBy(M,H`Level) select gl1copyattr(ChangeRing(Integers(M))) else ChangeRing(H,Integers(M));
end intrinsic;

// Do not change this function
intrinsic GL1CanonicalGenerators(N::RngIntElt) -> SeqEnum[RngIntElt]
{ Returns a canonical list of integers that generate (Z/NZ)*. }
    if N le #gl1gens then return gl1gens[N]; end if;
    if N le 2 then return [Integers()|]; end if;
    pp := Factorization(N); q := [a[1]^a[2] : a in pp];
    gens := [Integers()|];
    if pp[1][1] eq 2 then
        if pp[1][2] gt 1 then Append(~gens,CRT([q[1]-1,1],[q[1],N div q[1]])); end if;
        if pp[1][2] gt 2 then Append(~gens,CRT([5,1],[q[1],N div q[1]])); end if;
        pp := pp[2..#pp]; q := q[2..#q];
    end if;
    for i:=1 to #q do Append(~gens,CRT([PrimitiveRoot(q[i]),1],[q[i],N div q[i]])); end for;
    return gens;
end intrinsic;

/*** GL2/SL2 ambients ***/

intrinsic GL2Ambient(R::RngIntRes) -> GrpMat
{ Returns GL(2,R) with Order, Index, NegOne, Level attributes set. }
    G := GL(2,R); G`Order := GL2Size(#R); G`NegOne := true; G`Index := 1; G`Level := 1; G`Genus := 0;
    return G;
end intrinsic;

intrinsic GL2Ambient(N::RngIntElt) -> GrpMat
{ Returns GL(2,Z/NZ) (or trivial subgroup of GL(2,Z) when N=1) with Order, Index, NegOne, Level attributes set. }
    return N eq 1 select gl2N1 else GL2Ambient(Integers(N));
end intrinsic;

intrinsic GL2Ambient(D::GrpMat) -> GrpMat
{ Returns the largest subgroup of GL(2,Z/NZ) with the specified determinant image, with Order, Index, NegOne attributes set (and Level if Level is set for D). }
    require Degree(D) eq 1: "DeterminantImage must a be a subgroup of GL1.";
    R := BaseRing(D); if not IsFinite(R) then assert D eq gl1N1; return gl2N1; end if;
    G := sub<GL2|[GL2!g:g in Generators(SL(2,R))] cat [GL2![g[1][1],0,0,1]:g in Generators(D)]> where GL2 := GL(2,R);
    G`NegOne := true; G`Index := GL1Index(D); G`Order := GL2Size(#R) div G`Index;
    if assigned D`Level then assert IsDivisibleBy(#R,D`Level); G`Level := D`Level; end if;
    return G;
end intrinsic;

intrinsic SL2Ambient(R::RngIntRes) -> GrpMat
{ Returns SL(2,Z/NZ) with Order, Index, and Level attributes set. }
    G := SL(2,R); G`SL := true; G`Order := SL2Size(#R); G`NegOne := true; G`Index := 1; G`Level := 1; G`Genus := 0;
    return G;
end intrinsic;

intrinsic SL2Ambient(N::RngIntElt) -> GrpMat
{ Returns SL(2,Z/NZ) (or the trivial subgroup of SL(2,Z) when N=1) with SL, Order, Index, NegOne, Level attributes set. }
    return N eq 1 select sl2N1 else SL2Ambient(Integers(N));
end intrinsic;

/*** GL2/SL2 lift/project ***/

// IMPORTANT: do not change anything that would impact the lifting functions below, we want the generators of the lift to be canonical

function gl1ker(N,M)
    gens := GL1CanonicalGenerators(M);
    RM := Integers(M); RN := Integers(N);
    gens := [(RM!g)^Order(RN!g): g in gens];
    return [Integers(M)|g:g in gens|g ne 1];
end function;

intrinsic GL2ElementLifter(N::RngIntElt,M::RngIntElt) -> UserProgram
{ Returns a function that will canonically lift an element of GL(2,Z/NZ) to GL(2,Z/MZ) for given integers N dividing M (it is canonical in the sense that the generators of the output are a deterministic function of the generators of the input). }
    require IsDivisibleBy(M,N): "Domain level (first parameter) must divide codomain level (second parameter).";
    if N eq M then return func<h|h>; end if;
    GL2 := GL(2,Integers(M)); M2 := MatrixRing(Integers(),2); m := &*[a[1]^a[2]:a in Factorization(M)|N mod a[1] eq 0];
    return func<h|GL2!CRT([M2!h,Identity(M2)],[m,M div m])>;
end intrinsic;

intrinsic GL2Lift(H::GrpMat,M::RngIntElt) -> GrpMat
{ The full preimage in GL(2,Z/MZ) of H in GL(2,Z/NZ) for a multiple N of M. }
    if assigned H`SL then return SL2Lift(H,M); end if;
    N := #BaseRing(H); if not IsFinite(N) then assert H eq gl2N1; return GL2Ambient(M); end if;
    if M eq N then return H; end if;
    require IsDivisibleBy(M,N): "Target level M must be divisible by #BaseRing(H).";
    K := sub<GL2|[GL2![1,N,0,1],GL2![1,0,N,1],GL2![1+N,N,-N,1-N]] cat [GL2![a,0,0,1]:a in A] cat [lift(h):h in Generators(H)]> where A:=gl1ker(N,M) where lift := GL2ElementLifter(N,M) where GL2 := GL(2,Integers(M));
    // assert ChangeRing(K,Integers(N)) eq H and GL2Size(M)*#H eq GL2Size(N)*#K;
    return gl2copyattr(K,H);
end intrinsic;

intrinsic GL2Lifter(N::RngIntElt,M::RngIntElt) -> UserProgram
{ Returns a function that will canonically lift a subgroup of GL(2,Z/NZ) to GL(2,Z/MZ) (it is canonical in the sense that the generators of the output are a deterministic function of the generators of the input). }
    require IsDivisibleBy(M,N): "Target level M must be divisible by source level N";
    if N eq M then return func<H|H>; end if;
    if N eq 1 then return func<H|GL2Ambient(M)>; end if;
    GL2 := GL(2,Integers(M));
    gens := [GL2![1,N,0,1],GL2![1,0,N,1],GL2![1+N,N,-N,1-N]] cat [GL2![a,0,0,1]:a in A] where A:=gl1ker(N,M);
    lift := GL2ElementLifter(N,M);
    return func<H|gl2copyattr(sub<GL2|gens,[lift(h):h in Generators(H)]>,H)>;
end intrinsic;

intrinsic GL2Lifter(M::RngIntElt) -> UserProgram
{ Returns a function that will canonically lift a subgroup of GL(2,Z/NZ) to GL(2,Z/MZ) for any integer N dividing M (it is canonical in the sense that the generators of the output are a deterministic function of the generators of the input). }
    X := AssociativeArray();
    for N in Divisors(M) do X[N] := GL2Lifter(N,M); end for;
    return func<H|not IsFinite(BaseRing(H)) select GL2Ambient(M) else X[#BaseRing(H)](H)>;
end intrinsic;

intrinsic GL2Project(H::GrpMat,M::RngIntElt) -> GrpMat
{ The projection of H (viewed as a subgroup of GL(2,Zhat)) to GL(2,Z/MZ); will lift+project as required. }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    N := #BaseRing(H); if not IsFinite(N) then assert H eq gl2N1; return GL2Ambient(M); end if;
    if M eq 1 then return gl2N1; elif N eq M then return H; end if;
    if not IsDivisibleBy(N,M) then N := LCM(M,N); H := GL2Lift(H,N); if N eq M then return H; end if; end if;
    if assigned H`Level and IsDivisibleBy(M,H`Level) then return gl2copyattr(ChangeRing(H,Integers(M)),H); end if;
    HH := ChangeRing(H,Integers(M));
    if M le 2 or (assigned H`NegOne and H`NegOne) then HH`NegOne := true; end if;
    return HH;
end intrinsic;

intrinsic GL2ProjectKernel(H::GrpMat,M::RngIntElt) -> GrpMat
{ The projection to GL(2,Z/MZ) of the kernel of reduction mod-m of H, where m=N/gcd(M,N); requires m coprime to GCD(M,N). }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    N := #BaseRing(H); if not IsFinite(N) then assert H eq gl2N1; return GL2Ambient(M); end if;
    d := GCD(M,N); m := N div d; require GCD(m,d) eq 1: "N/gcd(M,N) must be coprime to gcd(M,N)";
    return m eq 1 select GL2Project(H,M) else (GL2Project(Kernel(pi),M) where _,pi:=ChangeRing(H,Integers(m)));
end intrinsic;

intrinsic SL2Level(H::GrpMat) -> RngIntElt, GrpMat
{ The least integer N such that H cap SL2 is the full inverse image of its reduction modulo N, along with corresponding subgroup of SL2. }
    if not assigned H`SL then return SL2Level(SL2Intersection(H)); end if;
    N := #BaseRing(H); if not IsFinite(N) then assert H eq sl2N1; return 1,sl2N1; end if;
    if assigned H`Level then return H`Level, N eq H`Level select H else (H`Level eq 1 select gl2N1 else sl2copyattr(ChangeRing(H,Integers(H`Level)),H)); end if;
    cSL2 := SL2Size(N);
    if not assigned H`Order then H`Order := SL2Order(H); end if;
    if not assigned H`Index then H`Index := cSL2 div H`Order; end if;
    if H`Order eq cSL2 then return 1,sl2N1; elif IsPrime(N) then H`Level := N; return H`Level,H; end if;
    M := N;
    function project(H,M) HH := ChangeRing(H,M); HH`SL := true; return HH; end function;
    for p in PrimeDivisors(N) do
        while N gt p and N mod p eq 0 and cSL2*SL2Order(project(H,Integers(N div p))) eq SL2Size(N div p)*H`Order do N div:= p; end while;
    end for;
    H`Level := N;
    if N eq M then H`Level := N; return H`Level, H; end if;
    return N, N eq M select H else sl2copyattr(ChangeRing(H,Integers(N)),H);
end intrinsic;

intrinsic SL2ElementLifter(N::RngIntElt,M::RngIntElt) -> UserProgram
{ Returns a function that will canonically lift an element of SL(2,Z/NZ) to SL(2,Z/MZ) for given integers N dividing M (it is canonical in the sense that the generators of the output are a deterministic function of the generators of the input). }
    require IsDivisibleBy(M,N): "Domain level (first parameter) must divide codomain level (second parameter).";
    if N eq M then return func<h|h>; end if;
    SL2 := SL(2,Integers(M)); M2 := MatrixRing(Integers(),2); Q := [a[1]^a[2]:a in Factorization(M)|N mod a[1] eq 0];
    function hensel(h,q)
        assert Determinant(h) eq 1;
        h := ChangeRing(M2!h,Integers(q)); i := GCD(h[1][1],q) eq 1 and GCD(h[2][2],q) eq 1 select 1 else 2; d := 1/h[2][3-i];
        while Determinant(h) ne 1 do h[1][i] +:= (-1)^i*d*(Determinant(h)-1); end while;
        return M2!h;
    end function;
    return func<h|SL2!CRT([hensel(h,q):q in Q] cat [Identity(M2)],Q cat [M div &*Q])>;
end intrinsic;

intrinsic SL2Lift(H::GrpMat,M::RngIntElt) -> GrpMat
{ The full preimage in SL(2,Z/MZ) of H in SL(2,Z/NZ) for a multiple M of N. }
    require assigned H`SL: "H should be a subgroup of SL2 that is marked as a subgroup of SL2.";
    N := #BaseRing(H); if not IsFinite(N) then assert H eq sl2N1; return SL2Ambient(M); end if;
    if M eq N then return H; end if;
    require IsDivisibleBy(M,N): "Target level M must be divisible by #BaseRing(H).";
    K := sub<SL2|[SL2![1,N,0,1],SL2![1,0,N,1],SL2![1+N,N,-N,1-N]] cat [lift(h):h in Generators(H)]> where lift := SL2ElementLifter(N,M) where SL2 := SL(2,Integers(M));
    // assert ChangeRing(K,Integers(N)) eq H and SL2Size(M)*#H eq SL2Size(N)*#K;
    return sl2copyattr(K,H);
end intrinsic;

intrinsic SL2Lifter(N::RngIntElt,M::RngIntElt) -> UserProgram
{ Returns a function that will canonically lift a subgroup of GL(2,Z/NZ) to GL(2,Z/MZ) (it is canonical in the sense that the generators of the output are a deterministic function of the generators of the input). }
    require IsDivisibleBy(M,N): "Target level M must be divisible by source level N";
    if N eq M then return func<H|H>; end if;
    if N eq 1 then return func<H|SL2Ambient(M)>; end if;
    R := Integers(N); SL2 := SL(2,Integers(M));
    gens := [SL2![1,N,0,1],SL2![1,0,N,1],SL2![1+N,N,-N,1-N]];
    lift := SL2ElementLifter(N,M);
    return func<H|sl2copyattr(sub<SL2|gens,[lift(h):h in Generators(H)]>,H)>;
end intrinsic;

intrinsic SL2Lifter(M::RngIntElt) -> UserProgram
{ Returns a function that will canonically lift a subgroup of GL(2,Z/NZ) to GL(2,Z/MZ) for any integer N dividing M (it is canonical in the sense that the generators of the output are a deterministic function of the generators of the input). }
    X := AssociativeArray();
    for N in Divisors(M) do X[N] := SL2Lifter(N,M); end for;
    return func<H|X[#BaseRing(H)](H)>;
end intrinsic;

intrinsic SL2Project(H::GrpMat,M::RngIntElt) -> GrpMat
{ The projection of H (viewed as a subgroup of SL(2,Zhat)) to SL(2,Z/MZ); will lift+project as required. }
    require assigned H`SL: "H should be a subgroup of SL2 that is marked as a subgroup of SL2.";
    N := #BaseRing(H); if not IsFinite(N) then assert H eq sl2N1; return SL2Ambient(M); end if;
    if M eq 1 then return sl2N1; elif N eq M then return H; end if;
    if not IsDivisibleBy(N,M) then N := LCM(M,N); H := SL2Lift(H,N); if N eq M then return H; end if; end if;
    if assigned H`Level and IsDivisibleBy(M,H`Level) then return sl2copyattr(ChangeRing(H,Integers(M)),H); end if;
    HH := ChangeRing(H,Integers(M)); HH`SL := true;
    if M le 2 or (assigned H`NegOne and H`NegOne) then HH`NegOne := true; end if;
    return HH;
end intrinsic;

/*** GL2/SL2 size/order/index/level functions ***/

intrinsic SL2Size(N::RngIntElt) -> RngIntElt
{ The cardinality of SL(2,Z/NZ). }
    if N eq 1 
        then return 1; end if;
    P := PrimeDivisors(N);
    return N*(N div &*P)^2*&*[p^2-1:p in P];
end intrinsic;

intrinsic PSL2Size(N:RngIntElt) -> RngIntElt
{ The cardinality of PSL(2,Z/NZ). }
    if N eq 1 then return 1; end if;
    P := PrimeDivisors(N); v2 := Valuation(N,2);
    e := v2 gt 2 select 4 else (v2 eq 2 select 2 else 1);
    e *:= v2 gt 0 select 2^(#P-1) else 2^#P;
    return N*(N div &*P)^2*&*[(p^2-1):p in P] div e;
end intrinsic;

intrinsic GL2Size(N::RngIntElt) -> RngIntElt
{ The cardinality of GL(2,Z/NZ). }
    return EulerPhi(N)*SL2Size(N);
end intrinsic;

intrinsic GL2BorelSize(N::RngIntElt) -> RngIntElt
{ The cardinality of the subgroup of upper triangular matrices in GL(2,Z/NZ). }
    return EulerPhi(N)^2*N;
end intrinsic;

intrinsic GL2Borel1Size(N::RngIntElt) -> RngIntElt
{ The cardinality of the subgroup of upper triangular matrices in GL(2,Z/NZ). }
    return EulerPhi(N)*N;
end intrinsic;

intrinsic SL2BorelSize(N:RngIntElt) -> RngIntElt
{ The cardinality of the subgroup of upper triangular matrices in GL(2,Z/NZ). }
    return EulerPhi(N)*N;
end intrinsic;

intrinsic PGL2Size(N::RngIntElt) -> RngIntElt
{ The cardinality of GL(2,Z/NZ). }
    return SL2Size(N);
end intrinsic;

intrinsic PGL2Order(H::GrpMat) -> RngIntElt
{ The order of the image of H in PGL(2,BaseRing(H)).  This can be computed very quickly. }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    if not IsFinite(BaseRing(H)) then assert H eq gl2N1; return 1; end if;
    X := {@ x : x in Z @} where Z := sub<RSpace(G)|[1,0]>^G where G:=GL(2,BaseRing(H));
    S := SymmetricGroup(#X);
    pi := hom<H->S|g:->S![Index(X,X[i]^g):i in [1..#X]]>;
    return #Image(pi);
end intrinsic;

intrinsic GL2Order(H::GrpMat:guess:=0) -> RngIntElt
{ The order of the specified subgroup H of GL(2,Z/NZ).  This is faster than #H when N and #H are at all large (say N >= 24 and #H >= 1024). Optional parameter guess will guide the decision on when to call #H or not.}
    if assigned H`SL then return SL2Order(H); end if;
    if assigned H`Order then return H`Order; end if;
    N := #BaseRing(H);
    if N le 24 or IsPrime(N) or (guess gt 0 and guess lt 1024) then H`Order := #H; return H`Order; end if;
    gens := Generators(H);
    G,P,pi := GL2BorelPC(N);
    V := sub<RSpace(H)|[0,1]>;          // The standard upper triangular Borel B is the stabilizer of V
    X := [V]; Xsize := #Orbit(H,V);     // cardinality of H is #Orbit(H,V) * (H cap B), by the orbit-stabilizer theorem
    T := AssociativeArray(Parent(V)); T[V] := Identity(H);
    S := sub<P|>; Ssize := 1; Smax := GL2BorelSize(N) div GL2DeterminantIndex(H);
    for i:=1 to Xsize do
        y := X[i];
        for g in gens do
            z := y^g; a := T[y]*g;
            b, h := IsDefined(T,z);
            if b then
                h := a*h^-1;
                if not pi(h) in S then S := sub<P|S,pi(h)>; Ssize := #S; if Ssize eq Smax then H`Order := Xsize*Ssize; return H`Order; end if; end if;
            else
                Append(~X,z); T[z] := a;
            end if;
        end for;
    end for;
    H`Order := Xsize*Ssize;
    return H`Order;
end intrinsic;

intrinsic GL2TriangularSubgroup(H::GrpMat:Upper:=true) -> GrpMat
{ The intersection of H with the Borel subgroup of upper (or lower) triangular matrices. }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    N := #BaseRing(H); if not IsFinite(N) then assert H eq gl2N1; return gl2N1; end if;
    gens := Generators(H);
    G,P,pi := GL2BorelPC(N); if not Upper then pi := func<h|pi(Transpose(h))>; end if;
    V := Upper select sub<RSpace(H)|[0,1]> else sub<RSpace(H)|[1,0]>;
    X := [V]; Xsize := #Orbit(H,V);
    T := AssociativeArray(Parent(V)); T[V] := Identity(H);
    S := sub<P|>; Ssize := 1; Smax := assigned H`Order select (H`Order div Xsize) else (GL2BorelSize(N) div GL2DeterminantIndex(H)); L := [];
    for i:=1 to Xsize do
        y := X[i];
        for g in gens do
            z := y^g; a := T[y]*g;
            b, h := IsDefined(T,z);
            if b then
                h := a*h^-1;
                if not pi(h) in S then S := sub<P|S,pi(h)>; Ssize := #S; Append(~L,h); if Ssize eq Smax then break; end if; end if;
            else
                Append(~X,z); T[z] := a;
            end if;
        end for;
        if Ssize eq Smax then break; end if;
    end for;
    if not assigned H`Order then H`Order := Xsize*Ssize; else assert H`Order eq Xsize*Ssize; end if;
    K := sub<H|L>; K`Order := Ssize; if assigned H`NegOne then K`NegOne := true; end if;
    return K;
end intrinsic;

intrinsic GL2Triangular1Subgroup(H::GrpMat:Upper:=true) -> GrpMat
{ The intersection of H with the Borel1 subgroup of upper (or lower) triangular matrices with a 1 in the *bottom* right. }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    N := #BaseRing(H); if not IsFinite(N) then assert H eq gl2N1; return gl2N1; end if;
    K := &or[h[2][1] ne 0:h in Generators(H)] select GL2TriangularSubgroup(H:Upper:=Upper) else H;
    gens := Generators(K);
    G,P,pi := GL2Borel1PC(N); if not Upper then pi := func<h|pi(Transpose(h))>; end if;
    V := Upper select RSpace(K)![0,1] else RSpace(K)![1,0];
    X := [V]; Xsize := #Orbit(K,V);
    T := AssociativeArray(Parent(V)); T[V] := Identity(H);
    S := sub<P|>; Ssize := 1; Smax := assigned K`Order select (K`Order div Xsize) else (GL2Borel1Size(N) div GL2DeterminantIndex(H)); L := [];
    for i:=1 to Xsize do
        y := X[i];
        for g in gens do
            z := y^g; a := T[y]*g;
            b, h := IsDefined(T,z);
            if b then
                h := a*h^-1;
                if not pi(h) in S then S := sub<P|S,pi(h)>; Ssize := #S; Append(~L,h); if Ssize eq Smax then break; end if; end if;
            else
                Append(~X,z); T[z] := a*g;
            end if;
        end for;
        if Ssize eq Smax then break; end if;
    end for;
    if not assigned K`Order then K`Order := Xsize*Ssize; else assert K`Order eq Xsize*Ssize; end if;
    L := sub<K|L>; L`Order := Ssize; if assigned K`NegOne then L`NegOne := true; end if;
    return L;
end intrinsic;

intrinsic GL2Index(H::GrpMat) -> RngIntElt
{ The index of H in GL(2,Z/NZ) (use GL2RelativeIndex to get index in ambient). }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    if assigned H`Index then return H`Index; end if;
    N := #BaseRing(H); if not IsFinite(N) then assert H eq gl2N1; return 1; end if;
    H`Index := GL2Size(#BaseRing(H)) div GL2Order(H);
    return H`Index;
end intrinsic;

intrinsic GL2DeterminantIndex(H::GrpMat) -> RngIntElt
{ The index of det(H) in GL1. }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    R := BaseRing(H); if not IsFinite(R) then assert H eq gl2N1; return 1; end if;
    return EulerPhi(#R) div #sub<M|[ipi(Determinant(h)):h in Generators(H)]> where ipi := Inverse(pi) where M,pi := MultiplicativeGroup(R);
end intrinsic;

intrinsic GL2RelativeIndex(H::GrpMat) -> RngIntElt
{ The index of H in its ambient (the preimage of det(H) in GL(2,Z/NZ)). }
    return GL2Index(H) div GL2DeterminantIndex(H);
end intrinsic;

intrinsic SL2Order(H::GrpMat) -> RngIntElt
{ The order of the specified subgroup H of SL(2,Z/NZ) (or its intersection with SL(2,Z/NZ)).  This is much faster than #(H meet SL2), even when H is small. }
    if not assigned H`SL then return SL2Order(SL2Intersection(H)); end if;
    if assigned H`Order then return H`Order; end if;
    N := #BaseRing(H); if N le 24 or IsPrime(N) then H`Order := #H; return H`Order; end if;
    gens := Generators(H);
    G,P,pi := SL2BorelPC(N);
    V := sub<RSpace(G)|[0,1]>;
    X := [V]; Xsize := #Orbit(H,V);
    T := AssociativeArray(); T[V] := Identity(H);
    S := sub<P|>;  Ssize := 1; Smax := SL2BorelSize(N);
    for i:=1 to Xsize do
        y := X[i];
        for g in gens do
            z := y^g; a := T[y]*g;
            b, h := IsDefined(T,z);
            if b then
                h := a*h^-1;
                if not pi(h) in S then S := sub<P|S,pi(h)>; Ssize := #S;
                    if Ssize eq Smax then H`Order := Xsize*Ssize; return H`Order; end if;
                end if;
            else
                Append(~X,z); T[z] := a;
            end if;
        end for;
    end for;
    H`Order := Xsize*Ssize;
    return H`Order;
end intrinsic;

intrinsic SL2Intersection(H::GrpMat) -> GrpMat
{ The intersection of the specified subgroup of GL(2,Z/NZ) with SL(2,Z/NZ).  For large composite N this is much faster than H meet SL(2,Integers(N)). }
    if assigned H`SL then return H; end if;
    if not IsFinite(BaseRing(H)) then return sl2N1; end if;
    gens := Generators(H);
    if not assigned H`SL and &and[Determinant(g) eq 1:g in gens] then
        HH := sub<SL(2,BaseRing(H))|H>; HH`SL := true; // make a copy, we cannot simply set H`SL because it will change the meaning of H`Index
        if assigned H`Order then HH`Order := H`Order; HH`Index := SL2Size(#BaseRing(H)) div HH`Order; end if;
        if assigned H`NegOne then HH`NegOne := H`NegOne; end if;
        return HH;
    end if;
    SL2 := SL(2,BaseRing(H));
    N := #BaseRing(H); if N le 46 or IsPrime(N) then HH := H meet SL2; HH`SL := true; return HH; end if;
    ZZ := Integers();
    n := GL1Order(GL2DeterminantImage(H));
    A := []; S := {}; for g in gens do d:=ZZ!(Determinant(g)^-1); Include(~S,d); A[d]:=g; end for;
    while #S lt n do for i,j in S do k := i*j mod N; A[k] := A[i]*A[j]; Include(~S,k); end for; end while;
    K := sub<SL2|[g*A[ZZ!Determinant(g)]:g in Generators(H)]>; K`SL := true;
    n := GL2Order(H) div n;
    while SL2Order(K) lt n do K:=sub<SL2|K,g*A[ZZ!Determinant(g)] where g:=Random(H)>; K`SL := true; end while;
    K`Order := n;
    return K;
end intrinsic;

intrinsic SL2Index(H::GrpMat) -> RngIntElt
{ Index of H cap SL(2,Z/NZ) in SL(2,Z/NZ). }
    if not assigned H`SL then return SL2Index(SL2Intersection(H)); end if;
    if assigned H`Index then return H`Index; end if;
    H`Index := SL2Size(#BaseRing(H)) div SL2Order(H);
    return H`Index;
end intrinsic;

intrinsic PSL2Index(H::GrpMat) -> RngIntElt
{ Index of H cap SL(2,Z/NZ) in SL(2,Z/NZ). }
    require assigned H`SL: "H should be a subgroup of SL2 that is marked as a subgroup of SL2.";
    return SL2Index(SL2IncludeNegativeOne(H));
end intrinsic;

intrinsic GL2Level(H::GrpMat) -> RngIntElt, GrpMat
{ Returns the least integer N such that H is the full inverse image of its reduction modulo N along with the reduction of H mod N and its index. }
    if assigned H`SL then return SL2Level(H); end if;
    N := #BaseRing(H); if not IsFinite(N) then assert H eq gl2N1; return 1,gl2N1; end if;;
    if assigned H`Level then return H`Level, N eq H`Level select H else (H`Level eq 1 select gl2N1 else gl2copyattr(ChangeRing(H,Integers(H`Level)),H)); end if;
    cGL2 := GL2Size(N);
    if not assigned H`Order then H`Order := GL2Order(H); end if;
    if not assigned H`Index then H`Index := cGL2 div H`Order; end if;
    if H`Order eq cGL2 then return 1,gl2N1; elif IsPrime(N) then H`Level := N; return H`Level,H; end if;
    M := N;
    for p in PrimeDivisors(N) do
        while N gt p and N mod p eq 0 and (cGL2*GL2Order(ChangeRing(H,Integers(N div p)):guess:=m*H`Order div cGL2) eq m*H`Order where m:=GL2Size(N div p)) do N div:= p; end while;
    end for;
    H`Level := N;
    if N eq M then H`Level := N; return H`Level, H; end if;
    return N, N eq M select H else gl2copyattr(ChangeRing(H,Integers(N)),H);
end intrinsic;

intrinsic GL2Levels(H::GrpMat) -> SeqEnum
{ Sorted list of pairs <N,i> such that the reduction of H modulo N has level i greater than the index of its reduction modulo any divisor of i, starting wtih <1,1> and ending with the level and index of H. }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    R := BaseRing(H); N := #R; if not IsFinite(N) then assert H eq gl2N1; return [[1,1]]; end if;
    cGL2 := GL2Size(N);
    if not assigned H`Order then H`Order := GL2Order(H); end if;
    if not assigned H`Index then H`Index := cGL2 div H`Order; end if;
    if H`Order eq cGL2 then return [[1,1]]; elif IsPrime(N) or (assigned H`Level and IsPrime(H`Index)) then return [[1,1], [H`Level,H`Index]]; end if;
    X := AssociativeArray(); X[1] := 1; X[N]:= H`Index;
    for M in ProperDivisors(N) do X[M] := GL2Size(M) div GL2Order(ChangeRing(H,Integers(M))); end for;
    L := Sort([[M,X[M]] : M in Keys(X) | &and[X[M div p] lt X[M] : p in PrimeDivisors(N) | IsDivisibleBy(M,p)]]);
    if not assigned H`Level then H`Level := L[#L][1]; end if;
    return L;
end intrinsic;

intrinsic GL2RelativeLevel(H::GrpMat) -> RngIntElt
{ The least integer N such that H is the full inverse image of its reduction modulo N in the subgroup of matrices with the same determinant image. }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    N := #BaseRing(H); if not IsFinite(N) then assert H eq gl2N1; return 1,gl2N1; end if;
    gl2size := func<N|N eq 1 select 1 else GL2Size(N) div GL1Index(ChangeRing(D,Integers(N)))> where D := GL2DeterminantImage(H);
    cGL2 := gl2size(N);
    if not assigned H`Order then H`Order := GL2Order(H); end if;
    if H`Order eq cGL2 then return 1; elif IsPrime(N) then return N; end if;
    for p in PrimeDivisors(N) do
        while N gt p and N mod p eq 0 and cGL2*GL2Order(GL2Project(H,N div p):guess:=m*H`Order) eq m*H`Order where m:=gl2size(N div p) do N div:= p; end while;
    end for;
    return N;
end intrinsic;

/*** GL2/SL2 generators (creating groups from generators.properties) ***/

intrinsic GL2FromGenerators(level::RngIntElt,index::RngIntElt,gens::SeqEnum[SeqEnum[RngIntElt]]:LevelNotKnown:=false) -> GrpMat
{ Create a subgroup of GL(2,Z/NZ) from a list of generators (will handle level 1), setting `Level, `Index, `Order. }
    if level eq 1 then return gl2N1; end if;
    H := sub<GL(2,Integers(level))|gens>; H`Index := index;H`Order := ExactQuotient(GL2Size(level),index);
    if LevelNotKnown then _,H := GL2Level(H); else H`Level:=level; end if;
    return H;
end intrinsic;

intrinsic GL2FromGenerators(level::RngIntElt,index::RngIntElt,negone::BoolElt,gens::SeqEnum[SeqEnum[RngIntElt]]:LevelNotKnown:=false) -> GrpMat
{ Create a subgroup of GL(2,Z/NZ) from a list of generators (will handle level 1), setting `Level, `Index, `Order, `NegOne. }
    if level eq 1 then return gl2N1; end if;
    H := sub<GL(2,Integers(level))|gens>; H`Index := index; H`NegOne := negone; H`Order := ExactQuotient(GL2Size(level),index);
    if LevelNotKnown then _,H := GL2Level(H); else H`Level:=level; end if;
    return H;
end intrinsic;

intrinsic GL2FromGenerators(level::RngIntElt,index::RngIntElt,genus::RngIntElt,negone::BoolElt,gens::SeqEnum[SeqEnum[RngIntElt]]:LevelNotKnown:=false) -> GrpMat
{ Create a subgroup of GL(2,Z/NZ) from a list of generators (will handle level 1), setting `Level, `Index, `Order, `NegOne. }
    if level eq 1 then return gl2N1; end if;
    H := sub<GL(2,Integers(level))|gens>; H`Index := index; H`Genus := genus; H`NegOne := negone; H`Order := ExactQuotient(GL2Size(level),index);
    if LevelNotKnown then _,H := GL2Level(H); else H`Level:=level; end if;
    return H;
end intrinsic;

intrinsic GL2FromGenerators(level::MonStgElt,index::MonStgElt,gens::MonStgElt:LevelNotKnown:=false) -> GrpMat
{ Create a subgroup of GL(2,Z/NZ) from a list of generators (will handle level 1), setting `Level, `Index, `Order,. }
    return GL2FromGenerators(atoi(level),atoi(index),atoiii(gens):LevelNotKnown:=LevelNotKnown);
end intrinsic;

intrinsic GL2FromGenerators(level::MonStgElt,index::MonStgElt,negone::MonStgElt,gens::MonStgElt:LevelNotKnown:=false) -> GrpMat
{ Create a subgroup of GL(2,Z/NZ) from a list of generators (will handle level 1), setting `Level, `Index, `Order, `NegOne. }
    return GL2FromGenerators(atoi(level),atoi(index),negone eq "1",atoiii(gens):LevelNotKnown:=LevelNotKnown);
end intrinsic;

intrinsic GL2FromGenerators(level::MonStgElt,index::MonStgElt,genus::MonStgElt,negone::MonStgElt,gens::MonStgElt:LevelNotKnown:=false) -> GrpMat
{ Create a subgroup of GL(2,Z/NZ) from a list of generators (will handle level 1), setting `Level, `Index, `Order, `NegOne. }
    return GL2FromGenerators(atoi(level),atoi(index),atoi(genus),negone eq "1",atoiii(gens):LevelNotKnown:=LevelNotKnown);
end intrinsic;

intrinsic GL2FromGenerators(r::SeqEnum[MonStgElt]) -> GrpMat
{ Create a subgroup of GL(2,Z/NZ) from a list of strings specifying level, index, gens. }
    return GL2FromGenerators(r[1],r[2],r[3]);
end intrinsic;

intrinsic SL2FromGenerators(level::RngIntElt,index::RngIntElt,gens::SeqEnum[SeqEnum[RngIntElt]]:LevelNotKnown:=false) -> GrpMat
{ Create a subgroup of SL(2,Z/NZ) from a list of generators (will handle level 1), setting `SL, `Level, `Index, `Order. }
    if level eq 1 then return sl2N1; end if;
    H := sub<SL(2,Integers(level))|gens>; H`SL:=true; H`Index := index; H`Order := ExactQuotient(SL2Size(level),index);
    if LevelNotKnown then _,H := SL2Level(H); else H`Level:=level; end if;
    return H;
end intrinsic;

intrinsic SL2FromGenerators(level::RngIntElt,index::RngIntElt,negone::BoolElt,gens::SeqEnum[SeqEnum[RngIntElt]]:LevelNotKnown:=false) -> GrpMat
{ Create a subgroup of SL(2,Z/NZ) from a list of generators (will handle level 1), setting `SL, `Level, `Index, `Order, `NegOne. }
    if level eq 1 then return sl2N1; end if;
    H := sub<SL(2,Integers(level))|gens>; H`SL:=true; H`Index := index; H`NegOne := negone; H`Order := ExactQuotient(SL2Size(level),index);
    if LevelNotKnown then _,H := SL2Level(H); else H`Level:=level; end if;
    return H;
end intrinsic;

intrinsic SL2FromGenerators(level::RngIntElt,index::RngIntElt,genus::RngIntElt,negone::BoolElt,gens::SeqEnum[SeqEnum[RngIntElt]]:LevelNotKnown:=false) -> GrpMat
{ Create a subgroup of SL(2,Z/NZ) from a list of generators (will handle level 1), setting `SL, `Level, `Index, `Order, `NegOne. }
    if level eq 1 then return sl2N1; end if;
    H := sub<SL(2,Integers(level))|gens>; H`SL:=true; H`Index := index; H`Genus := genus; H`NegOne := negone; H`Order := ExactQuotient(SL2Size(level),index);
    if LevelNotKnown then _,H := SL2Level(H); else H`Level:=level; end if;
    return H;
end intrinsic;

intrinsic SL2FromGenerators(level::MonStgElt,index::MonStgElt,gens::MonStgElt:LevelNotKnown:=false) -> GrpMat
{ Create a subgroup of SL(2,Z/NZ) from a list of generators (will handle level 1), setting `SL, `Level, `Index, `Order. }
    return SL2FromGenerators(atoi(level),atoi(index),atoiii(gens):LevelNotKnown:=LevelNotKnown);
end intrinsic;

intrinsic SL2FromGenerators(level::MonStgElt,index::MonStgElt,negone::MonStgElt,gens::MonStgElt:LevelNotKnown:=false) -> GrpMat
{ Create a subgroup of GL(2,Z/NZ) from a list of generators (will handle level 1), setting `Level, `Index, `Order, `NegOne. }
    return SL2FromGenerators(atoi(level),atoi(index),negone eq "1",atoiii(gens):LevelNotKnown:=LevelNotKnown);
end intrinsic;

intrinsic SL2FromGenerators(level::MonStgElt,index::MonStgElt,genus::MonStgElt,negone::MonStgElt,gens::MonStgElt:LevelNotKnown:=false) -> GrpMat
{ Create a subgroup of GL(2,Z/NZ) from a list of generators (will handle level 1), setting `Level, `Index, `Order, `NegOne. }
    return SL2FromGenerators(atoi(level),atoi(index),atoi(genus),negone eq "1",atoiii(gens):LevelNotKnown:=LevelNotKnown);
end intrinsic;

intrinsic SL2FromGenerators(r::SeqEnum[MonStgElt]) -> GrpMat
{ Create a subgroup of SL(2,Z/NZ) from a list of strings specifying level, index, gens. }
    return SL2FromGenerators(r[1],r[2],r[3]);
end intrinsic;

intrinsic GL2Generators(H::GrpMat) -> SeqEnum
{ Returns a sorted list of generators of H as a list of 4-tuples of integers. }
    return L where L := Sort([Universe([[1]])|[Integers()|a:a in Eltseq(g)]:g in Generators(H)]);
end intrinsic;

intrinsic SL2Generators(H::GrpMat) -> SeqEnum
{ Returns a sorted list of generators of H as a list of 4-tuples of integers. }
    return L where L := Sort([Universe([[1]])|[Integers()|a:a in Eltseq(g)]:g in Generators(H)]);
end intrinsic;

intrinsic GL2RandomizeGenerators(H::GrpMat) -> GrpMat
{ Returns a random conjugate of H with randomly chosen generators (useful for testing). }
    if assigned H`SL then return SL2RandomizeGenerators(H); end if;
    N := #BaseRing(H); if not IsFinite(N) then return H; end if;
    G := GL2Ambient(N);
    K := H^Random(G);
    KK := sub<G|Random(K)>;
    n := GL2Order(H); while GL2Order(KK) lt n do KK := sub<G|KK,Random(K)>; end while;
    return gl2copyattr(KK,H);
end intrinsic;

intrinsic SL2RandomizeGenerators(H::GrpMat) -> GrpMat
{ Returns a random conjugate of H with randomly chosen generators (useful for testing). }
    N := #BaseRing(H); if not IsFinite(N) then return H; end if;
    G := GL2Ambient(N);
    K := H^Random(G);
    KK := sub<G|Random(K)>; KK`SL := true;
    n := SL2Order(H); while SL2Order(KK) lt n do KK := sub<G|KK,Random(K)>; KK`SL := true; end while;
    return sl2copyattr(KK,H);
end intrinsic;

intrinsic GL2Transpose(H::GrpMat) -> GrpMat
{ Given a subgroup H of GL(2,R) for some ring R returns the transposed subgroup, preserving its attributes. }
    if assigned H`SL then return SL2Transpose(H); end if;
    if not IsFinite(BaseRing(H)) then assert H eq gl2N1; return H; end if;
    return gl2copyattr(sub<GL(2,BaseRing(H))|[Transpose(g):g in Generators(H)]>,H);
end intrinsic;

intrinsic SL2Transpose(H::GrpMat) -> GrpMat
{ Given a subgroup H of SL(2,R) for some ring R returns the transposed subgroup, preserving its attributes. }
    require assigned H`SL: "H should be a subgroup of SL2 that is marked as a subgroup of SL2.";
    if not IsFinite(BaseRing(H)) then assert H eq sl2N1; return H; end if;
    return sl2copyattr(sub<GL(2,BaseRing(H))|[Transpose(g):g in Generators(H)]>,H);
end intrinsic;


/*** GL2/SL2 permuration characters/representations ***/

gl2permrepalgs := ["cc","enum","action","gl2action","default"];
sl2permrepalgs := ["cc","enum","action","defaultoraction","default"];

// precomputed heruistic permrep algorithmic choices based on level,order,index
gl2permrepdat := [<1,6,1>,<2,3,3>,<3,2,3>,<4,12,1>,<4,24,2>,<4,72,3>,<8,6,2>,<8,12,3>,<8,36,1>,<8,60,1>,<8,192,2>,<8,360,3>,<8,576,1>,<12,4,2>,<12,8,3>,<12,24,3>,<12,168,1>,<12,324,3>,<12,1008,2>,<12,1944,2>,<16,3,1>,<16,6,3>,<16,18,3>,<16,30,2>,<16,96,1>,<16,180,1>,<16,288,1>,<16,1440,2>,<16,1536,1>,<16,2880,1>,<16,4608,2>,<16,8640,1>,<20,660,1>,<20,3960,1>,<24,4,3>,<24,12,4>,<24,20,1>,<24,84,2>,<24,120,1>,<24,162,2>,<24,192,2>,<24,504,1>,<24,972,1>,<24,1092,2>,<24,4032,1>,<24,6552,2>,<24,8064,2>,<24,15552,2>,<24,24192,1>,<32,9,3>,<32,15,3>,<32,48,1>,<32,90,2>,<32,144,2>,<32,720,1>,<32,768,2>,<32,1440,2>,<32,2304,2>,<32,2448,1>,<32,4320,1>,<32,12288,1>,<32,14688,2>,<32,23040,2>,<32,36864,2>,<32,69120,2>,<36,8,3>,<36,56,1>,<36,108,4>,<36,336,1>,<36,648,2>,<36,3420,1>,<36,8748,1>,<36,20520,1>,<36,52488,2>,<40,12,3>,<40,72,4>,<40,330,2>,<40,1980,2>,<40,7500,2>,<40,15840,1>,<40,31680,1>,<40,45000,2>,<40,95040,2>,<44,6072,2>,<44,36432,2>,<48,2,3>,<48,6,3>,<48,10,4>,<48,32,3>,<48,42,3>,<48,60,4>,<48,81,3>,<48,96,1>,<48,252,3>,<48,480,2>,<48,486,1>,<48,546,1>,<48,960,1>,<48,1536,2>,<48,2016,1>,<48,2880,1>,<48,3276,2>,<48,4032,1>,<48,7776,2>,<48,12096,1>,<48,20160,1>,<48,26208,2>,<48,38880,1>,<48,52416,2>,<48,64512,2>,<48,120960,2>,<56,12180,2>,<56,73080,2>,<60,220,2>,<60,1320,1>,<60,14880,2>,<60,89280,1>,<64,24,3>,<64,45,1>,<64,72,3>,<64,360,2>,<64,384,2>,<64,720,2>,<64,1152,1>,<64,1224,2>,<64,2160,1>,<64,6144,2>,<64,7344,1>,<64,11520,2>,<64,18432,1>,<64,34560,1>,<64,58752,1>,<64,98304,2>,<64,117504,1>,<72,28,3>,<72,40,1>,<72,54,4>,<72,64,3>,<72,168,3>,<72,324,2>,<72,364,1>,<72,1344,2>,<72,1710,1>,<72,2184,2>,<72,2688,1>,<72,4374,1>,<72,5184,2>,<72,8064,1>,<72,10260,1>,<72,25308,1>,<72,26244,2>,<72,82080,1>,<72,108864,1>,<80,6,1>,<80,36,3>,<80,165,3>,<80,288,1>,<80,576,1>,<80,990,1>,<80,1728,1>,<80,3750,1>,<80,7920,1>,<80,15840,1>,<80,22500,2>,<80,34440,2>,<80,47520,1>,<80,79200,1>,<84,24,1>,<84,144,1>,<84,39732,2>,<84,57624,1>,<88,3036,2>,<88,18216,2>,<88,145728,1>,<92,51888,1>,<96,5,1>,<96,16,3>,<96,21,2>,<96,30,1>,<96,48,3>,<96,126,1>,<96,240,1>,<96,243,2>,<96,256,2>,<96,273,2>,<96,480,1>,<96,768,2>,<96,816,3>,<96,1008,1>,<96,1440,2>,<96,1638,2>,<96,2016,1>,<96,3888,1>,<96,4896,2>,<96,6048,2>,<96,10080,2>,<96,12288,1>,<96,13104,1>,<96,19440,1>,<96,23040,2>,<96,26208,1>,<96,32256,1>,<96,60480,2>,<96,131040,2>,<100,132,3>,<100,792,2>,<104,74412,1>,<108,36,3>,<108,112,3>,<108,216,2>,<108,1140,1>,<108,2916,2>,<108,6840,1>,<108,17496,2>,<108,236196,2>,<112,6090,2>,<112,36540,1>,<116,102660,2>,<120,24,3>,<120,110,3>,<120,660,2>,<120,2500,2>,<120,5280,1>,<120,7440,1>,<120,10560,2>,<120,15000,1>,<120,31680,2>,<120,44640,2>,<120,113460,2>,<128,12,1>,<128,36,3>,<128,180,2>,<128,192,2>,<128,360,2>,<128,576,2>,<128,612,3>,<128,1080,2>,<128,3072,2>,<128,3672,2>,<128,5760,1>,<128,9216,2>,<128,17280,2>,<128,29376,1>,<128,49152,2>,<128,58752,2>,<128,786432,1>,<132,2024,3>,<132,12144,2>,<132,150348,2>,<140,178920,2>,<144,2,3>,<144,20,3>,<144,27,3>,<144,32,1>,<144,84,4>,<144,162,1>,<144,182,2>,<144,672,1>,<144,855,2>,<144,960,2>,<144,1092,2>,<144,1344,1>,<144,2187,1>,<144,2592,1>,<144,4032,1>,<144,5130,2>,<144,6720,2>,<144,8736,2>,<144,12654,2>,<144,12960,1>,<144,13122,2>,<144,17472,2>,<144,21504,2>,<144,40320,1>,<144,41040,2>,<144,54432,2>,<144,194472,2>,<156,246480,2>,<160,18,1>,<160,144,1>,<160,288,2>,<160,495,3>,<160,864,1>,<160,1875,1>,<160,3960,2>,<160,4608,2>,<160,7920,2>,<160,11250,2>,<160,13824,1>,<160,17220,2>,<160,23760,1>,<160,39600,2>,<164,285852,2>,<168,72,1>,<168,156,2>,<168,576,1>,<168,936,2>,<168,1152,1>,<168,3456,2>,<168,4060,2>,<168,19866,2>,<168,24360,2>,<168,28812,2>,<176,1518,2>,<176,9108,2>,<176,72864,1>,<176,352440,2>,<180,440,2>,<180,684,1>,<180,4104,1>,<180,4960,2>,<180,29760,1>,<184,25944,2>,<192,8,1>,<192,15,4>,<192,24,3>,<192,63,4>,<192,120,4>,<192,128,1>,<192,240,1>,<192,384,2>,<192,408,2>,<192,504,2>,<192,720,2>,<192,819,3>,<192,1008,2>,<192,1944,2>,<192,2048,1>,<192,2448,1>,<192,3024,2>,<192,3840,2>,<192,5040,2>,<192,6144,1>,<192,6552,2>,<192,9720,2>,<192,11520,2>,<192,13104,2>,<192,16128,2>,<192,19584,2>,<192,30240,1>,<192,39168,2>,<192,65520,2>,<192,456288,2>,<200,66,3>,<200,396,2>,<200,1500,2>,<200,3168,2>,<200,6336,1>,<200,9000,2>,<200,19008,2>,<200,515100,2>,<200,937500,1>,<204,546312,2>,<208,37206,2>,<212,612468,2>,<216,18,3>,<216,56,4>,<216,108,3>,<216,448,1>,<216,570,1>,<216,728,2>,<216,896,1>,<216,1458,2>,<216,1728,2>,<216,2688,1>,<216,3420,2>,<216,8436,2>,<216,8748,1>,<216,27360,1>,<216,36288,2>,<216,118098,2>,<216,647460,2>,<220,60,1>,<220,360,2>,<220,878460,2>,<224,3045,2>,<224,18270,2>,<224,721392,2>,<232,51330,2>,<240,12,4>,<240,55,3>,<240,96,4>,<240,192,2>,<240,330,2>,<240,576,1>,<240,1250,1>,<240,2640,2>,<240,3720,1>,<240,4032,1>,<240,5280,2>,<240,7500,2>,<240,7776,1>,<240,11480,2>,<240,15840,2>,<240,22320,1>,<240,24192,2>,<240,26400,2>,<240,56730,2>,<252,8,3>,<252,48,3>,<252,13244,2>,<252,19208,1>,<252,1024128,2>,<256,6,3>,<256,18,3>,<256,90,3>,<256,96,1>,<256,180,1>,<256,288,1>,<256,306,1>,<256,540,1>,<256,1536,1>,<256,1836,1>,<256,2880,2>,<256,4608,1>,<256,8640,2>,<256,14688,2>,<256,24576,2>,<256,29376,1>,<256,393216,2>,<256,6291456,2>,<260,1123980,2>,<264,1012,3>,<264,6072,2>,<264,48576,2>,<264,75174,2>,<272,1285608,2>,<276,17296,1>,<276,1342740,2>,<280,2436,2>,<280,14616,2>,<280,89460,2>,<288,10,3>,<288,16,4>,<288,42,3>,<288,80,4>,<288,81,3>,<288,91,2>,<288,160,2>,<288,256,1>,<288,272,2>,<288,336,1>,<288,480,2>,<288,546,2>,<288,672,1>,<288,1296,1>,<288,1632,2>,<288,2016,2>,<288,2565,1>,<288,3360,2>,<288,4368,2>,<288,6327,2>,<288,6480,2>,<288,6561,1>,<288,7680,1>,<288,8736,2>,<288,10752,2>,<288,20160,1>,<288,20520,1>,<288,27216,2>,<288,43680,2>,<288,97236,2>,<296,1653900,2>,<300,264,3>,<300,2976,2>,<300,17856,1>,<300,1721400,2>,<312,84,1>,<312,504,1>,<312,24804,1>,<312,123240,1>,<312,1934868,2>,<312,2399124,1>,<320,72,3>,<320,144,3>,<320,432,2>,<320,1980,2>,<320,2304,2>,<320,3960,1>,<320,5625,2>,<320,6912,2>,<320,8610,2>,<320,11880,2>,<320,19800,2>,<324,12,1>,<324,72,1>,<324,380,3>,<324,972,1>,<324,2280,2>,<324,5832,2>,<324,78732,1>,<324,2165292,2>,<324,6377292,2>,<328,142926,2>,<332,2328648,2>,<336,78,2>,<336,288,1>,<336,468,2>,<336,576,1>,<336,1728,2>,<336,2030,2>,<336,2880,2>,<336,9216,2>,<336,9933,2>,<336,12180,2>,<336,14406,1>,<336,17280,2>,<344,2588772,2>,<348,34220,1>,<352,759,1>,<352,4554,1>,<352,36432,2>,<352,176220,2>,<356,2867580,2>,<360,220,4>,<360,342,3>,<360,1760,2>,<360,2052,1>,<360,2480,2>,<360,3520,1>,<360,5000,1>,<360,10560,2>,<360,14880,2>,<360,16416,2>,<360,37820,2>,<360,2964780,2>,<368,12972,1>,<380,3483840,2>,<384,12,4>,<384,60,3>,<384,64,1>,<384,120,2>,<384,192,3>,<384,252,1>,<384,360,1>,<384,504,1>,<384,972,1>,<384,1024,1>,<384,1224,1>,<384,1512,2>,<384,1920,1>,<384,2520,2>,<384,3072,2>,<384,3276,2>,<384,4860,2>,<384,5760,1>,<384,6552,2>,<384,8064,2>,<384,9792,2>,<384,15120,2>,<384,16384,2>,<384,19584,2>,<384,32760,2>,<384,228144,2>,<384,3594432,2>,<392,1740,2>,<392,10440,2>,<392,3822588,2>,<396,4048,2>,<396,50116,2>,<396,3940200,2>,<400,198,3>,<400,750,2>,<400,1584,2>,<400,3168,2>,<400,4500,1>,<400,6888,2>,<400,9504,2>,<400,15840,2>,<400,257550,2>,<400,468750,2>,<408,273156,1>,<416,18603,1>,<420,59640,1>,<420,4696860,2>,<424,306234,2>,<432,9,3>,<432,54,1>,<432,224,1>,<432,285,1>,<432,364,2>,<432,448,2>,<432,729,2>,<432,864,2>,<432,1344,1>,<432,1710,1>,<432,2912,2>,<432,4218,2>,<432,4320,2>,<432,4374,1>,<432,5824,2>,<432,13440,2>,<432,13680,2>,<432,18144,2>,<432,59049,2>,<432,64824,2>,<432,323730,2>,<440,180,3>,<440,1440,2>,<440,2880,1>,<440,8640,1>,<440,439230,2>,<444,5544672,2>,<448,9135,2>,<448,360696,2>,<452,5848428,2>,<456,6004380,2>,<464,25665,1>,<464,6324552,2>,<468,82160,2>,<476,6825840,2>,<480,6,4>,<480,48,1>,<480,96,2>,<480,165,3>,<480,288,1>,<480,625,1>,<480,1320,2>,<480,1860,3>,<480,2016,2>,<480,2640,2>,<480,3750,2>,<480,3888,2>,<480,4608,2>,<480,5740,1>,<480,7920,2>,<480,11160,2>,<480,12096,2>,<480,13200,2>,<480,26208,2>,<480,28365,2>,<480,6998640,2>,<484,552,3>,<484,3312,2>,<492,95284,2>,<500,7906500,2>,<504,24,3>,<504,192,1>,<504,312,2>,<504,384,2>,<504,1152,1>,<504,6622,2>,<504,8120,1>,<504,9604,1>,<504,15552,1>,<504,512064,2>,<512,45,3>,<512,48,4>,<512,90,3>,<512,144,3>,<512,153,1>,<512,270,1>,<512,768,1>,<512,918,1>,<512,1440,2>,<512,2304,1>,<512,4320,2>,<512,7344,1>,<512,12288,1>,<512,14688,2>,<512,196608,1>,<512,3145728,2>,<512,8487168,2>,<520,561990,2>,<524,9095592,2>,<528,506,3>,<528,3036,2>,<528,24288,2>,<528,37587,1>,<528,117480,2>,<536,9732420,2>,<540,1368,1>,<540,9920,2>,<540,9951120,2>,<544,144,3>,<544,864,1>,<544,642804,2>,<544,12027024,2>,<552,8648,1>,<552,671370,2>,<552,10626828,2>,<560,1218,2>,<560,4920,2>,<560,7308,2>,<560,44730,2>,<560,11093880,2>,<564,11332452,2>,<576,8,3>,<576,40,3>,<576,80,2>,<576,128,1>,<576,136,3>,<576,168,2>,<576,240,1>,<576,273,3>,<576,336,1>,<576,648,2>,<576,816,1>,<576,1008,1>,<576,1680,1>,<576,2184,2>,<576,3240,2>,<576,3840,2>,<576,4368,2>,<576,5376,2>,<576,10080,2>,<576,10260,2>,<576,13608,2>,<576,21840,2>,<576,48618,2>,<576,152096,2>,<580,20532,2>,<584,12576732,1>,<588,5676,1>,<588,8232,1>,<588,19765032,2>,<592,826950,2>,<600,132,3>,<600,500,1>,<600,1056,2>,<600,1488,1>,<600,2112,2>,<600,3000,1>,<600,6336,2>,<600,8928,2>,<600,22692,2>,<600,171700,1>,<600,312500,2>,<600,860700,2>,<612,182104,2>,<612,14467068,2>,<620,15039960,2>,<624,42,3>,<624,252,3>,<624,2016,1>,<624,4032,1>,<624,12402,1>,<624,61620,1>,<624,967434,2>,<624,1199562,2>,<624,15331992,2>,<632,15927348,2>,<636,204156,2>,<640,36,3>,<640,72,3>,<640,216,1>,<640,990,2>,<640,1152,1>,<640,1980,2>,<640,3456,2>,<640,4305,2>,<640,5940,2>,<640,9900,2>,<648,36,4>,<648,190,3>,<648,486,1>,<648,576,1>,<648,896,1>,<648,1140,2>,<648,2812,2>,<648,2916,2>,<648,9120,2>,<648,12096,2>,<648,39366,2>,<648,215820,2>,<648,1082646,2>,<648,3188646,2>,<656,71463,1>,<660,120,1>,<660,292820,2>,<660,18132180,2>,<664,1164324,2>,<672,144,1>,<672,234,2>,<672,288,2>,<672,864,1>,<672,1015,1>,<672,1440,1>,<672,1872,2>,<672,3744,2>,<672,4608,2>,<672,6090,2>,<672,7203,2>,<672,8640,1>,<672,240464,2>,<672,19136208,2>,<684,180,3>,<684,1080,1>,<684,23457780,1>,<688,1294386,2>,<692,20890788,1>,<696,17110,2>,<696,21254100,2>,<700,35784,2>,<704,2277,1>,<704,18216,2>,<704,88110,2>,<704,21993312,2>,<712,1433790,2>,<716,23133960,2>,<720,110,3>,<720,171,2>,<720,192,3>,<720,880,1>,<720,1026,1>,<720,1344,1>,<720,1760,2>,<720,2500,1>,<720,2592,1>,<720,5280,2>,<720,7440,2>,<720,8064,1>,<720,8208,2>,<720,18910,2>,<720,1482390,2>,<732,24715248,2>,<736,6486,2>,<744,25947372,1>,<756,16,3>,<756,341376,2>,<756,27219780,2>,<760,1741920,2>,<764,28090752,2>,<768,2,1>,<768,6,3>,<768,30,3>,<768,60,3>,<768,96,3>,<768,126,3>,<768,180,1>,<768,252,4>,<768,486,2>,<768,512,1>,<768,612,2>,<768,756,1>,<768,960,1>,<768,1260,2>,<768,1536,2>,<768,1638,2>,<768,2430,2>,<768,2880,2>,<768,3276,2>,<768,4032,2>,<768,4896,2>,<768,7560,2>,<768,8192,2>,<768,9792,2>,<768,16380,2>,<768,114072,2>,<768,131072,2>,<768,1797216,2>,<776,29431740,1>,<780,49296,2>,<780,374660,2>,<784,870,2>,<784,5220,2>,<784,1911294,2>,<792,2024,1>,<792,16192,2>,<792,25058,1>,<792,1970100,2>,<792,31285188,2>,<800,375,1>,<800,792,2>,<800,1584,2>,<800,2250,1>,<800,3444,3>,<800,4752,2>,<800,7920,2>,<800,128775,2>,<800,234375,1>,<816,136578,2>,<816,428536,2>,<828,447580,2>,<840,812,2>,<840,4872,2>,<840,29820,2>,<840,2348430,2>,<848,153117,2>,<864,27,3>,<864,112,1>,<864,160,3>,<864,182,3>,<864,224,2>,<864,432,1>,<864,544,1>,<864,672,1>,<864,855,1>,<864,1120,2>,<864,1456,2>,<864,2109,2>,<864,2160,2>,<864,2187,2>,<864,2912,2>,<864,3584,1>,<864,6720,2>,<864,6840,2>,<864,9072,2>,<864,32412,2>,<864,161865,2>,<880,720,1>,<880,1440,1>,<880,4320,1>,<880,7200,2>,<880,70488,2>,<880,219615,1>,<888,551300,2>,<888,2772336,2>,<896,180348,2>,<900,992,4>,<900,5952,2>,<900,573800,2>,<904,2924214,2>,<912,3002190,2>,<924,3612,1>,<928,3162276,2>,<936,28,3>,<936,168,3>,<936,8268,2>,<936,41080,2>,<936,644956,2>,<936,799708,2>,<952,3412920,2>,<960,24,3>,<960,48,3>,<960,144,3>,<960,660,2>,<960,768,1>,<960,930,2>,<960,1008,1>,<960,1320,2>,<960,1875,2>,<960,1944,1>,<960,2304,1>,<960,3960,2>,<960,5580,2>,<960,6048,1>,<960,6600,2>,<960,13104,2>,<960,3499320,2>,<968,276,3>,<968,1656,1>,<968,13248,2>,<972,24,3>,<972,324,2>,<972,760,2>,<972,1944,2>,<972,26244,2>,<972,721764,2>,<972,2125764,2>,<980,25560,2>,<984,47642,2>,<996,776216,2>,<1000,300,1>,<1000,1800,1>,<1000,103020,2>,<1000,187500,1>,<1000,3953250,2>,<1008,96,1>,<1008,156,4>,<1008,192,3>,<1008,576,1>,<1008,960,2>,<1008,3072,1>,<1008,3311,1>,<1008,4060,2>,<1008,5760,1>,<1008,7776,1>,<1008,256032,2>,<1012,264,3>,<1012,1584,1>,<1024,24,3>,<1024,72,4>,<1024,135,3>,<1024,384,1>,<1024,459,2>,<1024,720,1>,<1024,1152,1>,<1024,2160,1>,<1024,3672,1>,<1024,6144,1>,<1024,7344,1>,<1024,98304,1>,<1024,1572864,1>,<1024,4243584,2>,<1032,862924,2>,<1040,280995,2>,<1048,4547796,1>,<1056,253,3>,<1056,1518,2>,<1056,12144,1>,<1056,58740,2>,<1068,955860,2>,<1072,4866210,2>,<1080,684,2>,<1080,3520,1>,<1080,4960,1>,<1080,5472,1>,<1080,129492,2>,<1080,988260,2>,<1080,4975560,1>,<1088,72,3>,<1088,432,1>,<1088,3456,1>,<1088,6912,1>,<1088,321402,2>,<1088,6013512,2>,<1100,12,3>,<1100,72,3>,<1100,175692,2>,<1104,4324,2>,<1104,335685,2>,<1104,5313414,2>,<1120,2460,3>,<1120,3654,2>,<1120,22365,1>,<1120,5546940,2>,<1128,5666226,1>,<1140,1161280,2>,<1148,40836,2>,<1152,20,3>,<1152,40,1>,<1152,64,3>,<1152,84,3>,<1152,120,3>,<1152,168,3>,<1152,324,1>,<1152,408,1>,<1152,504,2>,<1152,640,1>,<1152,840,2>,<1152,1024,2>,<1152,1092,2>,<1152,1620,1>,<1152,1920,2>,<1152,2184,2>,<1152,2688,2>,<1152,3264,2>,<1152,5040,2>,<1152,5130,2>,<1152,6528,2>,<1152,6804,2>,<1152,10920,2>,<1152,24309,2>,<1152,76048,2>,<1152,1198144,2>,<1160,10266,2>,<1168,6288366,2>,<1176,2838,2>,<1176,3480,2>,<1176,4116,1>,<1176,1274196,2>,<1176,9882516,1>,<1184,413475,2>,<1188,1313400,2>,<1200,250,1>,<1200,528,1>,<1200,1056,2>,<1200,1500,2>,<1200,3168,2>,<1200,4464,1>,<1200,5280,1>,<1200,11346,2>,<1200,85850,2>,<1200,156250,1>,<1200,430350,2>,<1224,91052,2>,<1224,7233534,2>,<1240,7519980,1>,<1248,126,3>,<1248,1008,1>,<1248,2016,1>,<1248,6201,1>,<1248,10080,1>,<1248,30810,2>,<1248,483717,2>,<1248,599781,2>,<1248,7665996,2>,<1260,19880,2>,<1260,1565620,2>,<1264,7963674,2>,<1272,102078,2>,<1280,18,3>,<1280,36,3>,<1280,108,3>,<1280,495,2>,<1280,576,1>,<1280,990,2>,<1280,1728,1>,<1280,2970,2>,<1280,4950,2>,<1296,18,4>,<1296,243,1>,<1296,288,3>,<1296,448,1>,<1296,570,1>,<1296,1406,2>,<1296,1440,1>,<1296,1458,1>,<1296,4560,2>,<1296,6048,1>,<1296,19683,2>,<1296,21608,2>,<1296,107910,2>,<1296,541323,2>,<1296,1594323,2>,<1300,224796,2>,<1320,480,1>,<1320,960,1>,<1320,2880,1>,<1320,146410,2>,<1320,9066090,2>,<1328,582162,2>,<1332,1848224,2>,<1344,72,3>,<1344,144,3>,<1344,432,1>,<1344,720,2>,<1344,936,2>,<1344,1872,2>,<1344,2304,1>,<1344,3045,1>,<1344,4320,2>,<1344,9360,2>,<1344,65184,2>,<1344,120232,2>,<1344,9568104,2>,<1352,5724,1>,<1356,1949476,2>,<1368,540,1>,<1368,1332,2>,<1368,4320,1>,<1368,2001460,2>,<1368,11728890,2>,<1376,647193,2>,<1380,268548,2>,<1384,10445394,2>,<1392,8555,1>,<1392,2108184,2>,<1392,10627050,2>,<1400,17892,2>,<1408,9108,2>,<1408,44055,2>,<1408,10996656,2>,<1424,716895,2>,<1428,2275280,2>,<1432,11566980,2>,<1440,2,4>,<1440,96,3>,<1440,440,4>,<1440,513,1>,<1440,672,2>,<1440,880,2>,<1440,1250,1>,<1440,1296,1>,<1440,1536,1>,<1440,2640,2>,<1440,3720,2>,<1440,4032,1>,<1440,4104,2>,<1440,4400,2>,<1440,8736,2>,<1440,9455,2>,<1440,741195,2>,<1440,2332880,2>,<1452,1104,1>,<1452,13668,2>,<1464,12357624,1>,<1472,3243,2>,<1480,330780,2>,<1488,12973686,2>,<1500,344280,2>,<1500,2635500,2>,<1512,64,3>,<1512,128,3>,<1512,384,1>,<1512,5184,1>,<1512,170688,2>,<1512,13609890,1>,<1520,870960,2>,<1528,14045376,1>,<1536,15,3>,<1536,16,1>,<1536,30,3>,<1536,48,4>,<1536,63,3>,<1536,90,3>,<1536,126,3>,<1536,256,1>,<1536,306,2>,<1536,378,2>,<1536,480,1>,<1536,630,1>,<1536,768,1>,<1536,819,1>,<1536,1215,1>,<1536,1440,1>,<1536,1638,2>,<1536,2016,2>,<1536,2448,1>,<1536,3780,2>,<1536,4096,1>,<1536,4896,2>,<1536,8190,2>,<1536,57036,2>,<1536,65536,1>,<1536,898608,2>,<1536,1048576,2>,<1536,2829056,2>,<1552,14715870,2>,<1560,24648,2>,<1560,187330,2>,<1568,435,4>,<1568,2610,2>,<1568,103056,2>,<1568,955647,2>,<1572,3031864,2>,<1584,1012,2>,<1584,8096,2>,<1584,12529,2>,<1584,39160,2>,<1584,985050,2>,<1584,15642594,2>,<1600,396,1>,<1600,792,2>,<1600,1125,2>,<1600,1722,2>,<1600,2376,2>,<1600,3960,2>,<1608,3244140,2>,<1620,3317040,2>,<1624,420,1>,<1624,2520,1>,<1632,288,1>,<1632,68289,2>,<1632,214268,2>,<1632,4009008,2>,<1656,223790,2>,<1656,3542276,2>,<1680,406,4>,<1680,576,1>,<1680,1640,2>,<1680,2436,2>,<1680,3456,1>,<1680,14910,2>,<1680,1174215,2>,<1680,3697960,1>,<1692,3777484,2>,<1728,56,3>,<1728,80,3>,<1728,112,3>,<1728,216,1>,<1728,272,3>,<1728,336,1>,<1728,560,2>,<1728,728,2>,<1728,1080,1>,<1728,1280,1>,<1728,1456,2>,<1728,1792,1>,<1728,3360,1>,<1728,3420,2>,<1728,4536,2>,<1728,7280,2>,<1728,16206,2>,<1740,6844,1>,<1752,4192244,2>,<1760,360,1>,<1760,720,1>,<1760,2160,1>,<1760,3600,1>,<1760,35244,2>,<1764,1892,3>,<1764,2744,2>,<1764,146304,2>,<1764,6588344,2>,<1776,275650,2>,<1776,1386168,2>,<1780,573516,2>,<1792,90174,2>,<1800,496,3>,<1800,1000,2>,<1800,2112,2>,<1800,2976,2>,<1800,7564,2>,<1800,286900,2>,<1800,592956,2>,<1808,1462107,2>,<1824,1501095,2>,<1836,4822356,2>,<1848,1806,2>,<1856,1581138,2>,<1860,480,1>,<1860,2880,1>,<1860,5013320,1>,<1872,14,3>,<1872,84,3>,<1872,672,1>,<1872,1344,1>,<1872,4134,2>,<1872,322478,2>,<1872,399854,2>,<1872,5110664,2>,<1896,5309116,1>,<1900,696768,2>,<1904,1706460,2>,<1908,68052,1>,<1920,12,3>,<1920,24,3>,<1920,72,3>,<1920,330,2>,<1920,384,1>,<1920,465,3>,<1920,504,1>,<1920,660,2>,<1920,972,2>,<1920,1152,1>,<1920,1980,2>,<1920,2790,2>,<1920,3024,1>,<1920,3300,2>,<1920,6552,2>,<1920,1749660,2>,<1932,191820,2>,<1936,828,2>,<1936,6624,2>,<1936,32040,2>,<1944,162,3>,<1944,192,1>,<1944,380,1>,<1944,972,1>,<1944,3040,2>,<1944,4032,1>,<1944,13122,1>,<1944,71940,2>,<1944,360882,2>,<1944,1062882,2>,<1960,12780,2>,<1968,23821,2>,<1980,788040,2>,<1980,6044060,2>,<1992,388108,2>,<2000,150,4>,<2000,900,1>,<2000,3168,2>,<2000,51510,2>,<2000,93750,1>,<2000,1976625,2>,<2016,6,1>,<2016,48,3>,<2016,96,3>,<2016,288,1>,<2016,480,1>,<2016,624,2>,<2016,1248,2>,<2016,1536,1>,<2016,2030,1>,<2016,2880,1>,<2016,3888,1>,<2016,128016,2>,<2016,6378736,2>,<2024,792,1>,<2024,6336,1>,<2028,18960,2>,<2048,36,3>,<2048,192,1>,<2048,360,1>,<2048,576,1>,<2048,1080,1>,<2048,1836,2>,<2048,3072,1>,<2048,3672,1>,<2048,49152,1>,<2048,786432,1>,<2048,2121792,2>,<2052,60,3>,<2052,360,1>,<2052,7819260,2>,<2064,431462,2>,<2076,6963596,1>,<2088,7084700,2>,<2096,2273898,2>,<2100,939372,2>,<2112,759,1>,<2112,6072,2>,<2112,7331104,2>,<2116,2256,2>,<2136,477930,2>,<2144,2433105,2>,<2148,7711320,2>,<2160,342,2>,<2160,864,1>,<2160,1760,1>,<2160,2688,1>,<2160,2736,1>,<2160,64746,2>,<2160,494130,2>,<2160,2487780,2>,<2176,36,4>,<2176,216,3>,<2176,1728,1>,<2176,3456,1>,<2176,160701,2>,<2176,3006756,2>,<2184,342732,2>,<2196,8238416,2>,<2200,36,3>,<2200,288,1>,<2200,576,1>,<2200,1728,1>,<2200,87846,2>,<2208,2162,2>,<2208,2656707,2>,<2232,8649124,2>,<2240,2773470,2>,<2244,8844,2>,<2256,2833113,2>,<2268,113792,2>,<2268,9073260,2>,<2280,580640,2>,<2280,1200876,2>,<2292,9363584,2>,<2296,20418,2>,<2304,2,4>,<2304,20,3>,<2304,32,3>,<2304,42,3>,<2304,60,3>,<2304,84,3>,<2304,162,1>,<2304,252,1>,<2304,320,2>,<2304,420,2>,<2304,512,2>,<2304,546,2>,<2304,810,1>,<2304,960,1>,<2304,1092,2>,<2304,1344,1>,<2304,1632,2>,<2304,2520,2>,<2304,2565,2>,<2304,3264,2>,<2304,3402,2>,<2304,5460,2>,<2304,38024,2>,<2304,599072,2>,<2320,5133,2>,<2324,332664,2>,<2328,9810580,2>,<2336,3144183,2>,<2352,1740,2>,<2352,2058,2>,<2352,637098,2>,<2352,4941258,2>,<2376,58860,2>,<2376,656700,2>,<2376,10428396,2>,<2380,1365168,2>,<2400,264,4>,<2400,528,2>,<2400,750,1>,<2400,1584,2>,<2400,2640,2>,<2400,5673,2>,<2400,42925,2>,<2400,78125,2>,<2400,215175,2>,<2400,1399728,2>,<2420,79860,1>,<2448,3616767,2>,<2480,3759990,1>,<2496,504,1>,<2496,1008,1>,<2496,5040,1>,<2496,15405,2>,<2496,3832998,2>,<2500,1581300,2>,<2520,1624,2>,<2520,9940,2>,<2520,423540,2>,<2520,782810,2>,<2528,3981837,2>,<2544,51039,2>,<2560,54,4>,<2560,288,1>,<2560,864,1>,<2560,1485,2>,<2560,2475,1>,<2592,144,3>,<2592,224,3>,<2592,703,4>,<2592,720,2>,<2592,729,2>,<2592,2240,2>,<2592,2280,2>,<2592,3024,2>,<2592,10804,2>,<2592,53955,2>,<2600,112398,2>,<2640,240,1>,<2640,480,1>,<2640,1440,1>,<2640,23496,2>,<2640,73205,2>,<2640,4533045,2>,<2652,42024,2>,<2656,291081,2>,<2664,684,1>,<2664,924112,2>,<2680,1946484,2>,<2688,216,1>,<2688,360,1>,<2688,468,2>,<2688,936,2>,<2688,1152,1>,<2688,2160,1>,<2688,4680,2>,<2688,32592,2>,<2688,4784052,2>,<2700,1984,2>,<2700,1990224,2>,<2704,2862,2>,<2712,974738,2>,<2736,666,3>,<2736,2160,1>,<2736,1000730,2>,<2736,5864445,2>,<2744,546084,2>,<2760,134274,2>,<2768,5222697,1>,<2784,1054092,2>,<2784,5313525,2>,<2800,2218776,2>,<2808,56,3>,<2808,2756,2>,<2816,4554,2>,<2816,5498328,2>,<2856,1137640,2>,<2860,102180,2>,<2864,5783490,2>,<2880,48,3>,<2880,220,3>,<2880,336,1>,<2880,440,2>,<2880,648,1>,<2880,768,1>,<2880,1320,2>,<2880,1860,2>,<2880,2016,1>,<2880,2052,2>,<2880,2200,2>,<2880,4368,2>,<2880,1166440,2>,<2904,552,1>,<2904,4416,1>,<2904,6834,2>,<2916,108,4>,<2916,648,1>,<2916,8748,1>,<2916,240588,2>,<2916,708588,2>,<2928,6178812,2>,<2940,670980,2>,<2960,165390,2>,<2976,6486843,2>,<3000,100,4>,<3000,600,1>,<3000,62500,2>,<3000,172140,2>,<3000,1317750,2>,<3024,32,4>,<3024,64,3>,<3024,192,1>,<3024,1920,1>,<3024,2592,1>,<3024,6804945,2>,<3036,528,1>,<3040,435480,2>,<3056,7022688,2>,<3072,24,3>,<3072,45,4>,<3072,128,1>,<3072,189,3>,<3072,240,3>,<3072,315,2>,<3072,384,1>,<3072,720,1>,<3072,1008,2>,<3072,1224,1>,<3072,1890,1>,<3072,2048,2>,<3072,2448,2>,<3072,4095,2>,<3072,28518,2>,<3072,32768,2>,<3072,449304,2>,<3072,524288,2>,<3072,1414528,2>,<3100,3007992,2>,<3104,7357935,1>,<3108,792096,2>,<3120,12324,2>,<3120,93665,2>,<3136,1305,2>,<3136,51528,2>,<3144,1515932,1>,<3168,506,2>,<3168,4048,1>,<3168,19580,2>,<3168,492525,2>,<3168,7821297,2>,<3200,198,3>,<3200,396,3>,<3200,861,2>,<3200,1188,1>,<3200,1980,2>,<3204,318620,2>,<3216,1622070,2>,<3240,329420,2>,<3240,1658520,2>,<3248,210,3>,<3248,1260,1>,<3264,144,1>,<3264,1152,1>,<3264,2304,1>,<3264,2004504,2>,<3280,840,1>,<3300,24,4>,<3300,3626436,2>,<3312,111895,2>,<3312,1771138,2>,<3332,975120,2>,<3360,288,1>,<3360,820,4>,<3360,1218,2>,<3360,1728,1>,<3360,7455,2>,<3360,1848980,2>,<3364,3540,2>,<3380,86460,2>,<3384,1888742,2>,<3400,30300,2>,<3420,4691556,2>,<3444,13612,2>,<3456,40,3>,<3456,56,3>,<3456,108,3>,<3456,168,3>,<3456,280,1>,<3456,364,2>,<3456,540,1>,<3456,640,1>,<3456,728,2>,<3456,896,1>,<3456,1088,2>,<3456,1680,2>,<3456,1710,1>,<3456,2176,2>,<3456,2268,2>,<3456,3640,2>,<3456,8103,2>,<3468,32136,2>,<3480,3422,2>,<3480,4250820,1>,<3500,1129500,2>,<3504,2096122,2>,<3520,180,1>,<3520,360,1>,<3520,1080,1>,<3520,1800,1>,<3528,946,4>,<3528,1372,1>,<3528,73152,2>,<3528,424732,2>,<3528,3294172,2>,<3552,137825,2>,<3552,693084,2>,<3560,286758,2>,<3564,437800,2>,<3580,4626792,1>,<3584,45087,2>,<3600,500,2>,<3600,1056,2>,<3600,1488,2>,<3600,3782,2>,<3600,296478,2>,<3612,924,1>,<3672,2411178,2>,<3696,903,3>,<3712,790569,2>,<3720,1440,1>,<3720,3660,2>,<3720,2506660,2>,<3744,42,3>,<3744,336,1>,<3744,672,1>,<3744,3360,1>,<3744,161239,2>,<3744,199927,2>,<3744,2555332,2>,<3780,5443956,2>,<3792,2654558,2>,<3800,348384,2>,<3808,853230,2>,<3816,34026,2>,<3840,6,3>,<3840,12,4>,<3840,36,3>,<3840,165,3>,<3840,192,1>,<3840,252,1>,<3840,330,4>,<3840,486,1>,<3840,576,1>,<3840,990,2>,<3840,1395,2>,<3840,1512,1>,<3840,1650,2>,<3840,3276,2>,<3840,874830,2>,<3864,95910,2>,<3872,3312,2>,<3872,16020,2>,<3880,5886348,2>,<3888,6,3>,<3888,96,3>,<3888,486,1>,<3888,1520,1>,<3888,2016,2>,<3888,6561,1>,<3888,35970,2>,<3888,180441,2>,<3888,531441,1>,<3920,1584840,2>,<3960,960,1>,<3960,394020,2>,<3960,3022030,2>,<3984,194054,2>,<4000,75,4>,<4000,450,1>,<4000,1584,2>,<4000,25755,2>,<4000,46875,1>,<4032,24,3>,<4032,48,3>,<4032,144,3>,<4032,240,3>,<4032,312,4>,<4032,624,2>,<4032,768,1>,<4032,1440,1>,<4032,1944,2>,<4032,3120,2>,<4032,64008,2>,<4032,3189368,2>,<4048,3168,1>,<4056,9480,2>,<4056,148836,2>,<4056,184548,1>,<4088,1796676,2>,<4096,18,1>,<4096,96,3>,<4096,180,1>,<4096,288,1>,<4096,540,1>,<4096,918,1>,<4096,1536,1>,<4096,1836,1>,<4096,24576,1>,<4096,393216,1>,<4096,1060896,2>,<4104,180,1>,<4104,1440,1>,<4104,3909630,2>,<4116,1176,1>,<4116,2823576,2>,<4128,215731,2>,<4152,3481798,2>,<4176,702728,2>,<4176,3542350,2>,<4192,1136949,2>,<4200,469686,2>,<4224,3036,2>,<4224,3665552,1>,<4232,1128,2>,<4256,37968,2>,<4272,238965,2>,<4284,2066724,2>,<4296,3855660,1>,<4312,347508,2>,<4320,432,1>,<4320,880,2>,<4320,1344,1>,<4320,1368,2>,<4320,247065,2>,<4320,1243890,2>,<4324,1104,1>,<4352,18,4>,<4352,108,4>,<4352,864,1>,<4352,1728,1>,<4352,1503378,2>,<4356,4556,2>,<4356,358200,2>,<4368,171366,1>,<4392,4119208,2>,<4400,144,1>,<4400,288,1>,<4400,864,1>,<4400,1440,1>,<4416,1081,3>,<4440,110260,2>,<4464,4324562,2>,<4480,1386735,2>,<4488,4422,2>,<4500,114760,2>,<4500,878500,2>,<4536,128,3>,<4536,1728,1>,<4536,56896,2>,<4536,4536630,1>,<4560,290320,2>,<4560,600438,2>,<4584,4681792,1>,<4592,10209,2>,<4608,10,4>,<4608,16,3>,<4608,30,3>,<4608,42,3>,<4608,126,3>,<4608,160,3>,<4608,210,3>,<4608,256,1>,<4608,273,3>,<4608,405,1>,<4608,480,1>,<4608,546,2>,<4608,672,1>,<4608,816,2>,<4608,1260,1>,<4608,1632,2>,<4608,1701,2>,<4608,2730,2>,<4608,19012,2>,<4608,299536,2>,<4624,75624,2>,<4648,166332,2>,<4656,4905290,1>,<4680,228060,2>,<4704,870,1>,<4704,1029,1>,<4704,318549,2>,<4704,2470629,1>,<4704,2733744,2>,<4752,29430,2>,<4752,5214198,2>,<4760,682584,2>,<4800,132,3>,<4800,264,3>,<4800,792,1>,<4800,1320,2>,<4800,699864,2>,<4824,1081380,2>,<4840,39930,2>,<4860,1105680,2>,<4872,840,1>,<4872,3036300,2>,<4896,1336336,2>,<4900,5112,2>,<4960,1879995,2>,<4992,252,1>,<4992,504,1>,<4992,2520,1>,<4992,1916499,2>,<5000,60,3>,<5000,360,1>,<5000,20604,2>,<5000,37500,1>,<5000,790650,2>,<5040,192,1>,<5040,812,2>,<5040,1152,1>,<5040,4970,2>,<5040,211770,2>,<5040,391405,2>,<5120,144,3>,<5120,432,1>,<5184,72,3>,<5184,112,3>,<5184,360,1>,<5184,1120,2>,<5184,1140,1>,<5184,1512,1>,<5184,5402,2>,<5280,240,1>,<5280,720,1>,<5280,1200,1>,<5280,11748,2>,<5280,636240,2>,<5292,48768,2>,<5292,3888540,2>,<5304,21012,2>,<5328,342,4>,<5328,5256,2>,<5340,191172,2>,<5360,973242,1>,<5376,234,3>,<5376,468,4>,<5376,576,1>,<5376,1080,1>,<5376,2340,2>,<5376,2392026,2>,<5400,992,2>,<5400,197652,2>,<5400,995112,2>,<5408,1431,3>,<5424,487369,2>,<5472,1080,1>,<5472,500365,2>,<5488,273042,2>,<5508,1607452,2>,<5512,1404,1>,<5520,67137,2>,<5580,160,4>,<5580,960,1>,<5600,1109388,2>,<5616,28,3>,<5616,224,1>,<5616,448,1>,<5616,1378,4>,<5632,2277,2>,<5632,2749164,2>,<5700,90600,2>,<5712,568820,2>,<5720,51090,2>,<5724,22684,2>,<5728,2891745,2>,<5760,8,4>,<5760,24,3>,<5760,110,3>,<5760,168,3>,<5760,220,3>,<5760,324,1>,<5760,384,1>,<5760,660,1>,<5760,930,2>,<5760,1008,1>,<5760,1026,2>,<5760,1100,2>,<5760,2184,2>,<5760,583220,2>,<5764,826872,1>,<5808,2208,1>,<5832,324,3>,<5832,1344,1>,<5832,4374,2>,<5832,23980,2>,<5832,120294,2>,<5832,354294,1>,<5856,3089406,2>,<5880,335490,2>,<6000,50,3>,<6000,300,1>,<6000,31250,1>,<6000,658875,2>,<6032,486504,2>,<6048,2,3>,<6048,32,3>,<6048,96,3>,<6048,160,3>,<6048,512,1>,<6048,960,1>,<6048,1296,1>,<6072,2112,1>,<6080,217740,2>,<6084,6320,2>,<6112,3511344,2>,<6144,12,3>,<6144,120,3>,<6144,192,3>,<6144,360,1>,<6144,504,1>,<6144,612,4>,<6144,945,2>,<6144,1024,1>,<6144,1224,1>,<6144,14259,2>,<6144,16384,2>,<6144,224652,2>,<6144,262144,2>,<6156,20,4>,<6156,120,3>,<6156,2606420,2>,<6200,1503996,2>,<6216,396048,2>,<6240,2016,1>,<6240,6162,2>,<6256,55896,2>,<6272,25764,2>,<6288,757966,2>,<6300,313124,2>,<6336,2024,2>,<6348,58380,2>,<6400,594,2>,<6400,990,2>,<6408,159310,2>,<6432,811035,2>,<6444,2570440,2>,<6480,288,1>,<6480,164710,2>,<6496,630,1>,<6528,72,3>,<6528,576,1>,<6528,1152,1>,<6560,420,3>,<6600,96,3>,<6600,192,3>,<6600,576,1>,<6600,1813218,2>,<6624,885569,2>,<6664,487560,2>,<6720,144,3>,<6720,864,1>,<6720,1872,2>,<6724,6972,2>,<6728,1770,4>,<6732,1315188,2>,<6760,43230,2>,<6768,944371,1>,<6800,15150,2>,<6804,3024420,2>,<6840,2345778,2>,<6844,1740,1>,<6888,6806,2>,<6912,20,3>,<6912,54,3>,<6912,84,3>,<6912,140,3>,<6912,182,3>,<6912,270,1>,<6912,320,1>,<6912,364,3>,<6912,448,1>,<6912,544,1>,<6912,840,1>,<6912,855,1>,<6912,1088,2>,<6912,1134,1>,<6912,1820,2>,<6936,16068,2>,<6960,1711,2>,<6960,2125410,2>,<6972,110888,2>,<7000,564750,2>,<7008,1048061,2>,<7040,540,1>,<7040,900,1>,<7056,212366,2>,<7104,346542,2>,<7120,143379,2>,<7128,218900,2>,<7128,3476132,2>,<7140,455056,2>,<7160,2313396,2>,<7200,528,1>,<7200,1891,3>,<7200,148239,2>,<7200,466576,2>,<7220,183360,2>,<7260,26620,2>,<7260,1648380,2>,<7320,1860,1>,<7344,1205589,2>,<7400,66156,2>,<7440,1830,2>,<7440,1253330,2>,<7488,168,3>,<7488,336,1>,<7488,1680,1>,<7488,1277666,2>,<7500,68856,2>,<7560,2721978,2>,<7584,1327279,1>,<7616,426615,2>,<7632,17013,2>,<7680,6,3>,<7680,18,3>,<7680,96,3>,<7680,126,3>,<7680,288,1>,<7680,495,1>,<7680,756,1>,<7680,825,1>,<7680,1638,2>,<7680,437415,2>,<7728,47955,2>,<7744,1656,2>,<7744,8010,2>,<7744,1999392,2>,<7760,2943174,2>,<7776,48,3>,<7776,240,3>,<7776,760,1>,<7776,1008,1>,<7776,17985,2>,<7840,792420,2>,<7920,480,1>,<7920,7832,2>,<7920,197010,2>,<7920,1511015,2>,<7968,97027,2>,<7992,228,3>,<8000,225,3>,<8000,792,1>,<8040,648828,2>,<8060,1156920,2>,<8064,12,3>,<8064,24,3>,<8064,72,1>,<8064,120,3>,<8064,156,3>,<8064,312,3>,<8064,384,1>,<8064,720,1>,<8064,1560,2>,<8064,32004,2>,<8064,1594684,2>,<8092,401520,2>,<8096,1584,1>,<8100,663408,2>,<8112,74418,2>,<8112,92274,2>,<8112,1179384,2>,<8176,898338,2>,<8184,2358852,2>,<8192,48,3>,<8192,90,1>,<8192,144,1>,<8192,270,1>,<8192,459,1>,<8192,768,1>,<8192,918,1>,<8192,12288,1>,<8192,196608,1>,<8192,530448,2>,<8208,720,1>,<8208,1954815,2>,<8232,588,1>,<8232,1411788,2>,<8304,1740899,1>,<8352,351364,2>,<8352,1771175,2>,<8448,1518,2>,<8512,18984,2>,<8568,1033362,2>,<8580,34060,2>,<8588,307812,2>,<8592,1927830,2>,<8624,173754,2>,<8640,216,3>,<8640,440,1>,<8640,672,1>,<8640,684,1>,<8640,621945,2>,<8664,316020,2>,<8704,54,3>,<8704,432,1>,<8704,864,1>,<8704,751689,2>,<8712,2278,3>,<8712,179100,2>,<8712,2844108,2>,<8736,1472016,2>,<8748,36,3>,<8748,216,3>,<8748,2916,1>,<8748,80196,2>,<8748,236196,1>,<8800,72,3>,<8800,144,3>,<8800,432,1>,<8800,720,1>,<8820,223660,2>,<8844,2244,1>,<8880,55130,2>,<8928,2162281,2>,<8976,2211,3>,<9000,200,1>,<9000,57380,2>,<9000,439250,2>,<9072,64,3>,<9072,864,1>,<9072,2268315,2>,<9120,145160,2>,<9168,2340896,2>,<9180,585360,2>,<9216,8,3>,<9216,80,3>,<9216,105,3>,<9216,128,3>,<9216,240,1>,<9216,336,1>,<9216,408,3>,<9216,630,1>,<9216,816,1>,<9216,1365,2>,<9216,9506,2>,<9216,149768,2>,<9248,37812,2>,<9248,707472,1>,<9296,83166,2>,<9300,96,3>,<9300,576,1>,<9312,2452645,2>,<9360,114030,2>,<9408,9312,2>,<9408,1366872,2>,<9504,2607099,2>,<9520,341292,2>,<9600,132,3>,<9600,396,1>,<9600,660,1>,<9600,349932,2>,<9648,540690,1>,<9660,38364,2>,<9680,19965,1>,<9720,552840,2>,<9744,420,1>,<9744,1518150,1>,<9792,668168,2>,<9800,2556,3>,<9900,157608,2>,<9900,1208812,2>,<9940,2520,1>,<9976,89268,2>,<9984,126,3>,<9984,252,3>,<9984,1260,1>,<10000,30,4>,<10000,180,3>,<10000,10302,2>,<10000,18750,1>,<10080,96,3>,<10080,576,1>,<10080,2485,3>,<10088,2263980,2>,<10200,10100,2>,<10240,72,3>,<10240,216,3>,<10368,36,3>,<10368,56,3>,<10368,180,3>,<10368,560,1>,<10368,570,4>,<10368,756,1>,<10368,2701,2>,<10404,10712,2>,<10404,851004,2>,<10488,261060,2>,<10500,376500,2>,<10512,2664,1>,<10560,120,3>,<10560,360,1>,<10560,600,1>,<10560,318120,2>,<10584,24384,2>,<10584,1944270,2>,<10608,10506,2>,<10656,2628,3>,<10680,95586,2>,<10740,1542264,2>,<10752,288,1>,<10752,1170,2>,<10752,1196013,2>,<10800,98826,2>,<10836,308,3>,<10944,540,1>,<10952,44700,2>,<10976,136521,2>,<11016,803726,2>,<11024,702,1>,<11132,24,3>,<11132,144,1>,<11160,480,1>,<11200,554694,2>,<11232,112,3>,<11232,224,3>,<11236,11556,2>,<11264,1374582,2>,<11368,60,3>,<11368,360,1>,<11400,45300,2>,<11424,284410,2>,<11440,25545,2>,<11448,11342,2>,<11520,12,3>,<11520,84,3>,<11520,110,3>,<11520,162,3>,<11520,192,3>,<11520,330,1>,<11520,504,1>,<11520,513,3>,<11520,550,1>,<11520,1092,2>,<11520,291610,2>,<11528,413436,2>,<11616,1104,1>,<11640,1962116,2>,<11664,672,3>,<11664,2187,2>,<11664,11990,2>,<11664,177147,1>,<11712,1544703,2>,<11880,11772,2>,<12000,150,1>,<12064,243252,2>,<12096,16,3>,<12096,48,3>,<12096,80,3>,<12096,256,1>,<12096,480,1>,<12096,648,1>,<12100,15972,2>,<12144,1056,1>,<12160,108870,2>,<12168,3160,3>,<12168,49612,2>,<12168,61516,1>,<12224,1755672,2>,<12264,598892,2>,<12288,6,3>,<12288,32,3>,<12288,60,3>,<12288,96,3>,<12288,180,3>,<12288,252,4>,<12288,306,4>,<12288,486,1>,<12288,612,1>,<12288,8192,2>,<12288,112326,2>,<12288,131072,2>,<12312,60,3>,<12312,480,1>,<12312,1303210,2>,<12324,3120,1>,<12348,392,1>,<12348,941192,2>,<12432,198024,2>,<12480,1008,1>,<12480,3081,3>,<12500,316260,2>,<12512,27948,2>,<12544,12882,2>,<12576,378983,2>,<12600,156562,2>,<12648,1526316,2>,<12672,1012,1>,<12696,29190,2>,<12696,462036,2>,<12768,12656,2>,<12816,79655,2>,<12888,1285220,1>,<12936,115836,2>,<12960,144,3>,<12960,82355,2>,<12996,1234620,1>,<13056,36,3>,<13056,288,1>,<13056,576,1>,<13068,119400,2>,<13120,210,3>,<13200,6,4>,<13200,48,3>,<13200,96,3>,<13200,288,1>,<13284,52812,2>,<13440,432,1>,<13440,936,2>,<13448,3486,2>,<13456,218088,2>,<13464,657594,2>,<13608,576,1>,<13608,1512210,2>,<13612,3444,1>,<13680,1172889,2>,<13776,3403,3>,<13824,10,3>,<13824,42,3>,<13824,135,3>,<13824,160,3>,<13824,182,3>,<13824,224,1>,<13824,272,3>,<13824,420,1>,<13824,432,1>,<13824,544,1>,<13824,567,3>,<13824,910,2>,<13944,55444,2>,<14000,282375,2>,<14112,911248,2>,<14208,173271,2>,<14256,1738066,2>,<14280,227528,2>,<14320,1156698,2>,<14364,1432620,2>,<14400,264,4>,<14400,233288,2>,<14440,91680,2>,<14472,360460,2>,<14520,13310,2>,<14520,824190,1>,<14580,368560,2>,<14640,930,1>,<14700,134196,2>,<14792,60204,2>,<14800,33078,2>,<14880,626665,2>,<14976,84,3>,<14976,168,3>,<14976,840,1>,<14976,638833,2>,<15000,120,3>,<15000,12500,1>,<15000,34428,2>,<15120,384,1>,<15120,1360989,2>,<15360,48,3>,<15360,144,3>,<15360,378,3>,<15488,828,1>,<15488,4005,2>,<15488,999696,2>,<15552,24,3>,<15552,120,3>,<15552,380,1>,<15552,384,1>,<15552,504,1>,<15664,3960,1>,<15680,396210,2>,<15840,3916,3>,<15840,98505,2>,<15876,16256,2>,<15876,1296180,2>,<15984,114,4>,<16000,396,3>,<16020,63724,2>,<16080,324414,2>,<16120,578460,2>,<16128,6,4>,<16128,12,3>,<16128,36,3>,<16128,60,4>,<16128,156,3>,<16128,192,3>,<16128,360,4>,<16128,780,2>,<16128,16002,2>,<16128,797342,2>,<16184,200760,2>,<16192,792,1>,<16200,65884,2>,<16200,331704,2>,<16224,37209,2>,<16224,46137,2>,<16224,589692,2>,<16368,1179426,2>,<16384,72,3>,<16384,384,1>,<16384,6144,1>,<16384,98304,1>,<16384,265224,2>,<16400,168,3>,<16416,360,1>,<16428,149856,2>,<16464,294,1>,<16464,705894,2>,<16740,320,1>,<16836,1074576,1>,<16896,759,1>,<16900,17292,2>,<17136,516681,2>,<17160,17030,2>,<17176,153906,2>,<17184,963915,2>,<17280,8,3>,<17280,56,3>,<17280,108,3>,<17280,220,3>,<17280,336,4>,<17280,342,4>,<17292,275624,1>,<17328,158010,2>,<17400,850164,2>,<17408,216,3>,<17408,432,1>,<17424,1422054,2>,<17472,736008,1>,<17496,108,3>,<17496,1458,1>,<17496,40098,2>,<17496,118098,2>,<17600,36,3>,<17600,72,3>,<17600,216,1>,<17600,360,1>,<17640,111830,2>,<18000,100,3>,<18000,219625,2>,<18096,162168,2>,<18144,320,3>,<18144,432,1>,<18240,72580,2>,<18336,1170448,2>,<18360,292680,2>,<18432,40,3>,<18432,64,3>,<18432,120,3>,<18432,168,3>,<18432,315,3>,<18432,324,1>,<18432,504,1>,<18432,4753,3>,<18432,74884,2>,<18468,40,3>,<18496,18906,2>,<18496,353736,1>,<18592,41583,2>,<18600,288,1>,<18624,4704,1>,<18720,672,1>,<18768,18632,2>,<18816,4656,3>,<18816,683436,2>,<19040,170646,2>,<19044,19460,2>,<19200,330,3>,<19200,174966,2>,<19208,78012,2>,<19220,485160,2>,<19320,19182,2>,<19600,316968,2>,<19800,192,1>,<19800,78804,2>,<19800,604406,2>,<19952,44634,2>,<19968,378,1>,<19968,630,1>,<20000,90,3>,<20000,5151,3>,<20000,9375,1>,<20068,720372,2>,<20160,48,3>,<20160,288,1>,<20176,1131990,2>,<20184,732900,2>,<20200,5100,1>,<20400,5050,2>,<20412,1008140,2>,<20480,36,3>,<20480,108,3>,<20736,18,3>,<20736,90,3>,<20736,280,1>,<20736,288,3>,<20736,364,4>,<20736,378,3>,<20736,448,1>,<20808,5356,2>,<20808,425502,2>,<20976,130530,2>,<21000,188250,2>,<21012,5304,1>,<21024,1332,1>,<21120,300,1>,<21216,5253,2>,<21360,47793,2>,<21480,771132,2>,<21504,144,3>,<21600,49413,2>,<21780,549460,2>,<21904,22350,2>,<21960,620,4>,<22000,288,1>,<22016,197376,2>,<22200,22052,2>,<22260,88620,2>,<22264,72,3>,<22264,576,1>,<22400,277347,2>,<22464,56,3>,<22464,112,3>,<22464,336,1>,<22464,560,4>,<22472,5778,2>,<22500,22952,2>,<22528,687291,2>,<22684,5724,1>,<22736,30,3>,<22736,180,3>,<22800,22650,2>,<22848,142205,2>,<22896,5671,2>,<23040,2,3>,<23040,6,3>,<23040,32,3>,<23040,42,3>,<23040,96,3>,<23040,252,3>,<23040,275,3>,<23040,486,4>,<23040,546,4>,<23040,145805,2>,<23056,206718,2>,<23064,837012,2>,<23232,552,1>,<23280,981058,2>,<23328,336,3>,<23328,5995,2>,<23544,5940,1>,<23760,5886,2>,<23976,76,3>,<24120,216276,2>,<24180,385640,2>,<24192,8,3>,<24192,24,3>,<24192,40,3>,<24192,128,3>,<24192,240,1>,<24192,312,3>,<24192,324,4>,<24192,384,1>,<24200,7986,2>,<24300,221136,2>,<24320,54435,2>,<24336,24806,2>,<24336,30758,1>,<24336,393128,2>,<24360,607260,2>,<24448,877836,2>,<24528,299446,2>,<24576,30,3>,<24576,48,3>,<24576,90,3>,<24576,126,3>,<24576,256,1>,<24576,306,3>,<24576,378,4>,<24576,4096,2>,<24576,56163,2>,<24576,65536,1>,<24624,240,3>,<24648,24492,2>,<24696,196,1>,<24696,470596,1>,<24864,99012,2>,<24960,504,1>,<25000,7500,1>,<25000,158130,2>,<25088,6441,3>,<25284,132,3>,<25296,763158,2>,<25312,6384,1>,<25344,506,4>,<25392,231018,2>,<25536,6328,3>,<25764,102604,2>,<25776,642610,2>,<25872,57918,2>,<25920,72,3>,<25920,432,1>,<25992,105340,2>,<25992,617310,2>,<26112,144,3>,<26112,288,1>,<26136,59700,2>,<26136,948036,2>,<26208,6,4>,<26244,72,3>,<26244,972,1>,<26244,26732,2>,<26244,78732,1>,<26320,236040,2>,<26400,48,3>,<26400,144,3>,<26400,240,3>,<26508,241116,2>,<26532,748,1>,<26568,26406,2>,<26620,7260,1>,<26880,468,3>,<26912,109044,2>,<26928,328797,2>,<27216,288,1>,<27556,28056,2>,<27648,80,3>,<27648,112,3>,<27648,210,3>,<27648,216,3>,<27648,272,3>,<27648,336,1>,<27648,455,3>,<27744,235824,2>,<27888,27722,2>,<27900,32,3>,<27900,192,3>,<28224,455624,2>,<28392,26364,2>,<28512,869033,2>,<28560,113764,2>,<28616,256668,2>,<28640,578349,2>,<28728,716310,2>,<28800,132,3>,<28800,220,4>,<28800,116644,2>,<28812,168,3>,<28812,403368,1>,<28944,180230,2>,<29040,6655,2>,<29160,184280,2>,<29400,67098,2>,<29584,30102,2>,<29928,29756,2>,<29952,42,3>,<29952,84,3>,<29952,252,1>,<29952,420,1>,<30000,60,3>,<30000,480,1>,<30000,6250,2>,<30240,192,1>,<30264,754660,2>,<30720,24,3>,<30720,72,3>,<30720,384,4>,<30976,499848,2>,<31104,60,3>,<31104,192,3>,<31104,252,3>,<31104,360,1>,<31104,380,3>,<31212,283668,2>,<31328,1980,1>,<31360,198105,2>,<31500,125500,2>,<31536,888,3>,<31680,120,3>,<31684,32220,2>,<31752,8128,2>,<31752,648090,2>,<31968,342,1>,<32000,450,1>,<32004,8064,1>,<32040,31862,2>,<32220,514088,2>,<32240,289230,2>,<32256,6,3>,<32256,18,3>,<32256,30,3>,<32256,96,3>,<32256,180,4>,<32256,288,3>,<32256,390,3>,<32256,8001,2>,<32256,398671,2>,<32400,32942,2>,<32448,294846,2>,<32760,32580,2>,<32768,192,3>,<32768,360,1>,<32768,3072,1>,<32768,49152,1>,<32768,132612,2>,<32800,84,3>,<32832,180,3>,<32832,360,1>,<32856,74928,2>,<32928,147,3>,<32928,352947,2>,<33396,48,3>,<33496,300516,2>,<33672,537288,2>,<33696,224,3>,<33800,8646,2>,<34060,8580,1>,<34104,120,3>,<34320,8515,2>,<34352,76953,2>,<34560,54,3>,<34560,64,4>,<34560,110,3>,<34560,168,4>,<34560,324,3>,<34560,342,3>,<34560,364,4>,<34584,137812,2>,<34656,79005,2>,<34800,425082,2>,<34816,108,3>,<34816,216,3>,<34848,711027,2>,<34992,729,1>,<34992,59049,2>,<35200,108,3>,<35200,180,3>,<35912,145260,2>,<36100,36672,2>,<36192,81084,2>,<36288,16,3>,<36288,160,3>,<36288,216,3>,<36288,256,1>,<36300,329676,2>,<36480,36290,2>,<36600,372,4>,<36672,585224,2>,<36720,146340,2>,<36864,2,3>,<36864,20,3>,<36864,60,3>,<36864,84,3>,<36864,162,3>,<36864,252,3>,<36864,320,1>,<36864,37442,2>,<36936,160,3>,<36936,320,3>,<36972,1040,1>,<36992,9453,2>,<36992,176868,1>,<37248,2352,1>,<37248,37056,2>,<37264,9384,1>,<37440,336,1>,<37536,9316,2>,<37632,341718,2>,<38080,85323,2>,<38088,9730,2>,<38088,154012,2>,<38364,9660,1>,<38400,87483,2>,<38416,39006,2>,<38440,242580,1>,<38640,9591,2>,<38808,38612,2>,<38880,288,1>,<38988,411540,1>,<39200,158484,2>,<39204,39800,2>,<39600,2,4>,<39600,96,3>,<39600,39402,2>,<40000,360,3>,<40044,159612,1>,<40136,360186,2>,<40320,144,3>,<40368,366450,2>,<40400,2550,1>,<40824,192,3>,<40824,504070,2>,<40960,288,3>,<41472,45,3>,<41472,144,3>,<41472,182,3>,<41472,189,3>,<41472,224,1>,<41472,270,1>,<41536,372768,2>,<42000,94125,2>,<42048,666,3>,<42632,172284,2>,<42960,385566,2>,<43560,274730,2>,<43808,11175,2>,<43920,310,3>,<44000,144,3>,<44032,98688,2>,<44100,44732,2>,<44104,11100,1>,<44400,11026,2>,<44520,44310,2>,<44528,288,3>,<44652,405168,2>,<44928,28,3>,<44928,56,3>,<44928,168,3>,<44928,280,3>,<45000,11476,2>,<45300,11400,1>,<45472,90,3>,<45600,11325,2>,<46080,48,3>,<46080,126,3>,<46080,256,4>,<46112,103359,2>,<46128,418506,2>,<46656,168,4>,<46656,240,3>,<47088,2970,1>,<47124,187884,2>,<47628,432060,2>,<47952,38,3>,<47952,228,3>,<48000,132,4>,<48000,300,1>,<48240,108138,2>,<48360,192820,2>,<48384,12,3>,<48384,20,3>,<48384,64,3>,<48384,120,4>,<48384,156,3>,<48384,162,4>,<48384,192,3>,<48600,110568,2>,<48672,12403,2>,<48672,15379,1>,<48672,196564,2>,<48720,303630,2>,<48896,438918,2>,<48984,12324,1>,<49152,24,3>,<49152,240,3>,<49152,384,3>,<49152,2048,1>,<49152,32768,2>,<49248,120,3>,<49248,240,3>,<49284,49952,2>,<49296,12246,2>,<49700,504,1>,<49728,49506,2>,<49920,252,3>,<49928,201612,2>,<50000,3750,1>,<50440,452796,2>,<50624,3192,1>,<50784,115509,2>,<51076,51756,2>,<51200,396,4>,<51528,51302,2>,<51552,321305,2>,<51840,36,3>,<51840,112,4>,<51840,216,3>,<51984,52670,2>,<51984,308655,2>,<52224,72,3>,<52224,144,3>,<52224,432,1>,<52272,474018,2>,<52440,52212,2>,<52488,13366,2>,<52488,39366,1>,<52640,118020,2>,<52728,14196,1>,<52800,12,3>,<52800,24,3>,<52800,72,3>,<52800,120,3>,<52812,13284,1>,<53016,120558,2>,<53136,13203,2>,<53240,3630,1>,<53824,54522,2>,<54288,54056,2>,<54432,144,3>,<54780,218460,2>,<55112,14028,2>,<55296,40,3>,<55296,56,3>,<55296,108,3>,<55296,168,3>,<55444,13944,1>,<55488,117912,2>,<55776,13861,2>,<55800,96,3>,<55872,1568,1>,<56320,360,1>,<56448,227812,2>,<56644,57360,2>,<56784,13182,2>,<57120,56882,2>,<57232,128334,2>,<57456,358155,2>,<57600,110,3>,<57600,58322,2>,<57624,504,1>,<57624,201684,1>,<58080,57840,2>,<59168,15051,2>,<59512,14964,1>,<59856,14878,2>,<59904,126,3>,<59904,210,3>,<60000,240,3>,<60204,240124,2>,<60480,96,3>,<60528,377330,2>,<60552,244300,2>,<61440,12,3>,<61440,36,3>,<61440,192,4>,<61440,330,4>,<61952,249924,2>,<62208,96,3>,<62208,180,3>,<62424,141834,2>,<62500,63252,2>,<62656,990,3>,<63000,62750,2>,<63036,1768,1>,<63072,444,3>,<63368,16110,2>,<63724,16020,1>,<64000,225,3>,<64000,450,1>,<64080,15931,2>,<64440,257044,2>,<64480,144615,2>,<64512,48,3>,<64512,90,3>,<64512,144,3>,<64800,16471,2>,<64896,147423,2>,<64980,246924,2>,<65160,16380,1>,<65520,16290,2>,<65536,96,3>,<65536,288,1>,<65536,1536,1>,<65536,24576,1>,<65536,66306,2>,<65600,42,3>,<65600,252,3>,<66048,65792,2>,<66792,192,3>,<66992,150258,2>,<67344,268644,2>,<67392,112,3>,<68208,60,3>,<68644,69432,2>,<69120,2,3>,<69120,32,3>,<69120,84,3>,<69120,162,4>,<69120,182,4>,<69168,68906,2>,<69192,279004,2>,<69580,360,3>,<69632,54,3>,<69632,108,3>,<69632,324,3>,<69984,432,3>,<70400,288,3>,<70632,1980,1>,<71656,108,3>,<71820,286524,2>,<71824,72630,2>,<71928,152,3>,<72000,200,3>,<72200,18336,2>,<72360,72092,2>,<72576,8,4>,<72576,80,3>,<72576,108,3>,<72576,128,3>,<72580,18240,1>,<72600,164838,2>,<72900,73712,2>,<72960,18145,2>,<73200,186,3>,<73344,292612,2>,<73440,73170,2>,<73728,10,3>,<73728,16,3>,<73728,30,3>,<73728,42,3>,<73728,126,3>,<73728,160,3>,<73728,306,3>,<73728,480,1>,<73728,546,4>,<73728,18721,2>,<73872,80,3>,<73872,160,3>,<73984,88434,1>,<74088,392,1>,<74112,18624,1>,<74496,1176,4>,<74496,18528,2>,<74528,4692,1>,<74880,168,3>,<75264,170859,2>,<75272,303420,2>,<75852,44,4>,<75852,264,1>,<76176,77006,2>,<76728,76452,2>,<76800,264,3>,<76832,19503,2>,<77224,19404,1>,<77616,19306,2>,<77760,144,3>,<77952,420,1>,<77976,205770,1>,<78336,6,3>,<78336,288,1>,<78400,79242,2>,<78408,19900,2>,<78408,316012,2>,<78624,2,3>,<78732,324,3>,<78732,26244,1>,<78804,19800,1>,<78960,78680,2>,<79200,19701,2>,<79524,80372,2>,<79860,2420,1>,<80000,180,3>,<80000,360,3>,<80088,79806,2>,<80272,180093,2>,<80640,12,3>,<80640,72,4>,<80640,156,4>,<80640,330,4>,<80736,183225,2>,<81648,96,3>,<81920,144,3>,<81920,432,1>,<82944,72,3>,<82944,112,3>,<82944,135,3>,<82944,272,3>,<83072,186384,2>,<83232,78608,2>,<83700,64,3>,<84480,240,1>,<85264,86142,2>,<85848,85556,2>,<85920,192783,2>,<86436,56,3>,<86436,336,3>,<86436,134456,1>,<88000,72,3>,<88200,22366,2>,<88208,5550,1>,<88620,22260,1>,<89040,22155,2>,<89056,144,3>,<89056,288,3>,<89304,202584,2>,<89856,28,3>,<89856,84,3>,<89856,140,3>,<92160,8,3>,<92160,24,3>,<92160,128,3>,<92160,220,3>,<92160,384,4>,<92256,209253,2>,<92400,288,1>,<93312,120,3>,<93312,324,1>,<93312,380,1>,<93312,504,1>,<93636,94556,2>,<94248,93942,2>,<94608,296,3>,<95256,216030,2>,<95904,114,3>,<96000,150,3>,<96000,300,1>,<96000,396,4>,<96012,2688,1>,<96100,97032,2>,<96720,96410,2>,<96768,2,3>,<96768,6,3>,<96768,32,3>,<96768,60,3>,<96768,96,3>,<96768,480,4>,<96768,486,4>,<96768,546,4>,<97284,204,3>,<97344,98282,2>,<97792,219459,2>,<97968,6162,1>,<97968,97656,2>,<98304,120,3>,<98304,192,3>,<98304,360,3>,<98304,16384,1>,<98400,168,3>,<98496,60,3>,<98496,120,3>,<98496,360,1>,<98568,24976,2>,<98784,294,1>,<99012,24864,1>,<99452,48,3>,<99452,288,3>,<99456,24753,2>,<99856,100806,2>,<100488,100172,2>,<100880,226398,2>,<101000,1020,1>,<101248,1596,1>,<102152,25878,2>,<102604,25764,1>,<103056,25651,2>,<103680,18,3>,<103680,56,3>,<103680,108,3>,<103680,342,3>,<103680,448,4>,<103968,26335,2>,<104424,26220,1>,<104448,36,3>,<104448,72,3>,<104448,216,3>,<104544,237009,2>,<104832,12,3>,<104832,24,3>,<104832,72,4>,<104880,26106,2>,<104976,288,3>,<104976,19683,1>,<105456,7098,1>,<105600,6,3>,<105600,12,4>,<105600,36,3>,<105600,60,3>,<105600,192,3>,<105600,252,3>,<105600,360,4>,<106480,1815,1>,<107648,27261,2>,<108112,27144,1>,<108576,27028,2>,<108864,72,3>,<108900,109892,2>,<109560,109230,2>,<109800,124,3>,<110592,20,3>,<110592,54,3>,<110592,84,3>,<110592,320,1>,<110592,364,4>,<110808,320,1>,<111744,784,3>,<112896,113906,2>,<113288,28680,2>,<113568,113232,2>,<113764,28560,1>,<114240,28441,2>,<115092,3220,1>,<115200,330,4>,<115200,29161,2>,<115248,100842,1>,<115680,29040,1>,<116160,28920,2>,<116964,137180,2>,<119024,7482,1>,<119716,120756,2>,<119808,336,3>,<120000,120,3>,<120000,240,3>,<120408,120062,2>,<120960,48,3>,<120960,220,4>,<121104,122150,2>,<121800,121452,2>,<122472,384,1>,<122880,6,3>,<122880,18,3>,<122880,96,4>,<122880,288,3>,<122880,306,4>,<122880,378,3>,<123120,6,4>,<123904,124962,2>,<124416,48,3>,<124416,90,3>,<124416,378,1>,<124608,124256,2>,<125000,1500,1>,<125000,31626,2>,<125500,31500,1>,<126000,31375,2>,<126144,222,3>,<126720,480,1>,<128164,129240,2>,<128880,128522,2>,<129024,24,3>,<129024,72,3>,<129024,312,3>,<129024,360,4>,<129024,384,3>,<129960,123462,2>,<130320,8190,1>,<131072,144,3>,<131072,270,1>,<131072,768,1>,<131072,12288,1>,<131072,33153,2>,<131200,126,3>,<131584,33024,1>,<132000,288,1>,<132096,32896,2>,<133100,1452,1>,<133584,96,3>,<133584,192,3>,<133956,135056,2>,<134688,134322,2>,<134784,56,3>,<135900,3800,1>,<136416,240,3>,<137288,34716,2>,<137812,34584,1>,<138240,16,3>,<138240,42,3>,<138240,256,4>,<138240,272,4>,<138240,336,4>,<138336,34453,2>,<138384,139502,2>,<138600,192,3>,<139128,138756,2>,<139264,162,3>,<139264,270,3>,<139968,216,3>,<139968,336,1>,<140800,144,3>,<141264,990,3>,<142884,144020,2>,<143312,54,3>,<143312,324,1>,<143640,143262,2>,<143648,36315,2>,<143856,76,3>,<144000,100,3>,<144000,200,3>,<144000,264,4>,<144184,36180,1>,<144720,36046,2>,<145152,40,3>,<145152,54,3>,<145152,64,3>,<145152,320,1>,<145152,324,4>,<145152,364,4>,<145800,36856,2>,<145924,147072,2>,<146340,36720,1>,<146688,146306,2>,<146880,36585,2>,<146952,4108,1>,<147456,80,3>,<147456,128,3>,<147456,240,3>,<147456,315,3>,<147744,80,3>,<147744,240,3>,<147968,44217,2>,<148224,9312,1>,<148800,288,3>,<148992,588,3>,<149056,2346,1>,<149760,84,3>,<150544,151710,2>,<151320,150932,2>,<151704,132,3>,<152352,38503,2>,<152904,38364,1>,<153456,38226,2>,<153600,132,3>,<153600,396,4>,<154448,9702,1>,<155520,72,3>,<155520,330,4>,<155520,380,4>,<155904,420,1>,<156672,144,3>,<156800,39621,2>,<156816,158006,2>,<157216,41616,1>,<157248,336,3>,<157360,39480,1>,<157464,13122,1>,<157608,157212,2>,<157920,39340,2>,<158184,4732,1>,<158400,8,3>,<158400,24,3>,<158400,168,4>,<158400,240,3>,<158400,324,4>,<158436,4428,1>,<159048,40186,2>,<159612,40044,1>,<159720,1210,1>,<159744,252,3>,<160000,90,3>,<160000,180,3>,<160176,39903,2>,<160212,240,3>,<161280,36,3>,<161280,288,3>,<163296,288,1>,<163840,216,3>,<165888,36,3>,<165888,56,3>,<165888,280,1>,<166464,39304,2>,<167400,256,3>,<168960,120,3>,<168960,360,1>,<170300,1716,1>,<170528,43071,2>,<171112,42924,1>,<171696,42778,2>,<172304,360,3>,<172800,220,4>,<172800,342,4>,<172872,168,3>,<172872,67228,1>,<174080,216,4>,<176000,216,3>,<177184,912,4>,<178112,72,3>,<178112,144,3>,<178200,288,3>,<179712,70,3>,<179712,224,3>,<179712,294,3>,<181888,180,3>,<184320,12,3>,<184320,64,3>,<184320,110,3>,<184320,192,3>,<184320,252,4>,<184320,330,3>,<184320,504,3>,<186624,60,3>,<186624,252,4>,<186624,546,4>,<187272,47278,2>,<187884,47124,1>,<188496,46971,2>,<189216,148,4>,<192000,150,3>,<192000,450,1>,<192200,48516,2>,<192820,48360,1>,<193440,48205,2>,<193536,16,3>,<193536,30,3>,<193536,48,3>,<193536,240,4>,<193536,256,4>,<194688,49141,2>,<195312,48984,1>,<195480,5460,1>,<195936,48828,2>,<196608,96,3>,<196608,180,3>,<196608,512,1>,<196800,84,3>,<196992,180,3>,<196992,300,3>,<198476,60,3>,<198904,144,3>,<199712,50403,2>,<200344,50244,1>,<200976,50086,2>,<201600,132,4>,<201684,57624,1>,<202000,510,4>,<202496,798,3>,<207360,54,3>,<207360,224,4>,<207360,364,4>,<208848,13110,1>,<208896,36,3>,<208896,108,3>,<208896,180,3>,<209664,6,3>,<209664,12,3>,<209664,36,3>,<209664,60,4>,<209664,192,4>,<209664,360,4>,<209952,144,3>,<210912,3549,1>,<211200,6,3>,<211200,18,3>,<211200,30,3>,<211200,96,3>,<211200,180,4>,<211200,288,3>,<211896,660,4>,<214968,216,3>,<216224,13572,1>,<217728,36,3>,<217728,216,3>,<217800,54946,2>,<218460,54780,1>,<219120,54615,2>,<219600,62,3>,<221184,10,3>,<221184,42,3>,<221184,160,3>,<221184,182,3>,<221184,210,3>,<221184,432,1>,<221184,546,4>,<221616,160,3>,<222336,6208,1>,<223200,192,3>,<223488,392,4>,<224028,1152,3>,<224640,336,3>,<225792,56953,2>,<226464,56784,1>,<226500,2280,1>,<227136,56616,2>,<227556,88,3>,<230400,264,4>,<230496,50421,1>,<231360,14520,1>,<233928,68590,2>,<235008,2,3>,<235872,224,3>,<236196,108,3>,<236196,8748,1>,<236412,6600,1>,<237600,216,3>,<239432,60378,2>,<239616,168,3>,<240000,60,3>,<240000,120,3>,<240000,360,1>,<240124,60204,1>,<240816,60031,2>,<241920,24,3>,<241920,110,3>,<241920,192,3>,<241920,312,4>,<241920,384,4>,<242208,61075,2>,<242904,60900,1>,<243600,60726,2>,<244944,192,3>,<245760,48,3>,<245760,144,3>,<246240,240,3>,<246924,64980,1>,<247808,62481,2>,<248512,62304,1>,<248832,24,3>,<248832,384,4>,<249216,62128,2>,<250000,750,1>,<253440,240,1>,<255744,342,3>,<256328,64620,2>,<257044,64440,1>,<257760,64261,2>,<258048,12,3>,<258048,36,3>,<258048,156,3>,<258048,180,4>,<258048,192,3>,<258048,360,4>,<259308,112,3>,<259920,61731,2>,<261120,144,4>,<262144,384,3>,<262144,6144,1>,<263168,16512,1>,<264000,144,3>,<265860,7420,1>,<266200,726,1>,<267168,6,3>,<267168,96,3>,<267168,288,3>,<267840,320,1>,<267912,67528,2>,<268644,67344,1>,<269376,67161,2>,<269568,28,3>,<269568,280,3>,<269568,378,1>,<272832,120,3>,<272832,240,3>,<276480,8,3>,<276480,128,3>,<276480,168,3>,<276480,220,3>,<276480,336,4>,<276768,69751,2>,<277200,96,3>,<277512,69564,1>,<278256,69378,2>,<278528,432,1>,<279936,168,4>,<281600,72,3>,<281600,216,3>,<285768,72010,2>,<286524,71820,1>,<286624,162,3>,<287280,71631,2>,<287712,304,3>,<288000,100,3>,<288000,132,3>,<288000,300,1>,<288036,896,3>,<288368,18090,1>,<290304,2,3>,<290304,20,3>,<290304,32,3>,<290304,160,3>,<290304,162,3>,<290304,182,4>,<290304,320,3>,<291848,73536,2>,<291852,68,3>,<292612,73344,1>,<292820,660,1>,<293376,73153,2>,<293904,2054,1>,<294912,120,3>,<294912,504,4>,<295488,40,3>,<295488,120,3>,<295488,200,3>,<296448,4656,1>,<297036,8288,1>,<297984,294,3>,<298356,96,3>,<299520,252,4>,<301088,75855,2>,<301864,75660,1>,<302640,75466,2>,<303264,336,3>,<305808,19182,1>,<311040,36,3>,<313272,8740,1>,<313344,12,3>,<313344,24,3>,<313344,72,3>,<313632,79003,2>,<314424,78804,1>,<314432,20808,1>,<314496,8,3>,<314496,24,3>,<314496,168,4>,<314496,324,4>,<314720,19740,1>,<314880,420,1>,<315216,78606,2>,<316368,2366,1>,<316800,12,3>,<316800,20,3>,<316800,84,4>,<316800,120,3>,<316800,162,4>,<316800,192,3>,<316800,504,4>,<319440,605,1>,<320000,270,3>,<322560,144,3>,<322560,288,3>,<325800,3276,1>,<326592,24,3>,<326592,144,1>,<327680,108,3>,<329400,248,3>,<331776,18,3>,<331776,280,1>,<331776,288,3>,<331776,364,4>,<331776,448,4>,<334800,128,3>,<334800,256,3>,<338688,156,4>,<342224,21462,1>,<344608,180,3>,<345600,110,3>,<347040,9680,1>,<347900,72,4>,<348160,108,3>,<349920,432,3>,<354368,456,4>,<356224,216,3>,<356400,144,3>,<357204,312,3>,<359424,112,3>,<359424,210,3>,<359424,336,1>,<360000,240,3>,<362880,16,3>,<362900,3648,1>,<363776,90,3>,<363776,180,3>,<368640,2,3>,<368640,6,3>,<368640,96,3>,<368640,126,3>,<368640,252,3>,<368640,486,4>,<369096,2028,1>,<369360,2,4>,<373248,30,3>,<373248,126,3>,<378432,74,3>,<383616,228,3>,<387072,8,3>,<387072,24,3>,<387072,120,3>,<387072,128,3>,<387072,240,4>,<387072,312,3>,<387072,384,4>,<390624,24492,1>,<390960,2730,1>,<393216,48,3>,<393216,90,3>,<393216,306,3>,<393216,378,3>,<393216,4096,1>,<396952,180,3>,<400688,25122,1>,<400752,192,3>,<403200,396,4>,<403368,28812,1>,<404352,252,3>,<414720,182,3>,<414720,224,4>,<414720,432,4>,<417792,90,3>,<417792,288,1>,<419328,6,3>,<419328,18,3>,<419328,30,3>,<419328,96,4>,<419328,180,4>,<419328,288,4>,<419904,72,3>,<419904,360,3>,<422400,48,3>,<422400,90,3>,<422400,144,3>,<423792,330,3>,<429936,108,3>,<432000,200,3>,<432448,6786,1>,<435456,18,3>,<435456,108,3>,<439020,12240,1>,<439200,186,3>,<442368,80,3>,<442368,210,3>,<442368,216,3>,<442368,272,3>,<442368,336,1>,<442780,660,4>,<443100,4452,1>,<443520,360,4>,<444672,3104,1>,<445280,288,3>,<446400,96,3>,<446400,192,3>,<446976,196,3>,<449280,28,3>,<449280,168,3>,<452928,28392,1>,<458712,12788,1>,<460800,132,3>,<462720,7260,1>,<466560,24,3>,<466560,324,4>,<467712,420,1>,<471648,13872,1>,<471744,112,3>,<472392,324,4>,<475200,8,3>,<475200,56,3>,<475200,108,3>,<475200,336,4>,<475308,1476,3>,<478836,13348,1>,<479232,84,3>,<479232,252,3>,<480000,60,3>,<480000,180,3>,<480636,80,4>,<483840,12,3>,<483840,96,3>,<483840,156,3>,<483840,192,3>,<483840,330,4>,<485808,30450,1>,<491520,24,3>,<491520,72,3>,<491520,384,4>,<492480,12,3>,<492480,24,4>,<492480,72,4>,<492480,120,3>,<493848,32490,1>,<497024,31152,1>,<497664,192,3>,<497664,360,1>,<497664,380,4>,<505000,204,3>,<506880,120,3>,<516096,6,3>,<516096,18,3>,<516096,90,3>,<516096,96,3>,<516096,180,3>,<516096,288,4>,<516096,306,4>,<518616,448,4>,<522240,72,3>,<522240,432,1>,<524288,192,3>,<524288,3072,1>,<524800,252,3>,<525312,360,1>,<526336,8256,1>,<528000,12,3>,<528000,72,3>,<534336,48,3>,<534336,144,3>,<534336,240,3>,<539136,140,3>,<539136,224,3>,<540568,2772,1>,<545664,60,3>,<545664,120,3>,<548352,288,3>,<552960,64,3>,<552960,84,3>,<552960,110,3>,<552960,168,3>,<552960,324,3>,<552960,342,3>,<552960,504,4>,<554400,288,3>,<555024,34782,1>,<557056,216,3>,<558092,84,4>,<563652,15708,1>,<567648,296,3>,<575424,152,3>,<575424,304,3>,<576000,150,3>,<578400,5808,1>,<580608,10,3>,<580608,16,3>,<580608,80,3>,<580608,160,3>,<580608,256,3>,<580608,272,4>,<583704,204,3>,<585936,16328,1>,<586440,1820,3>,<589824,32,3>,<589824,60,3>,<589824,252,3>,<589824,320,3>,<590976,100,3>,<590976,320,3>,<592704,392,1>,<592896,2328,3>,<595428,120,3>,<603728,37830,1>,<604800,264,4>,<605052,19208,1>,<606528,168,3>,<606816,264,3>,<620340,3180,1>,<622080,18,3>,<622080,288,3>,<625000,300,3>,<626544,4370,1>,<626688,6,3>,<626688,12,3>,<626688,36,3>,<626688,60,4>,<626688,192,4>,<626688,360,4>,<627500,6300,1>,<628848,39402,1>,<628864,10404,1>,<628992,12,3>,<628992,20,3>,<628992,84,3>,<628992,120,4>,<628992,162,4>,<628992,192,4>,<628992,504,4>,<629440,9870,1>,<629760,420,1>,<632736,1183,1>,<633488,552,3>,<633600,2,4>,<633600,6,3>,<633600,32,3>,<633600,42,3>,<633600,60,3>,<633600,96,3>,<633600,252,4>,<633600,480,4>,<633600,486,4>,<633600,546,4>,<635688,220,3>,<636792,948,3>,<645120,72,3>,<645120,144,3>,<645120,432,3>,<651600,1638,3>,<653184,72,3>,<653184,380,4>,<655360,288,3>,<655380,18260,1>,<658800,124,3>,<663552,144,3>,<663552,182,3>,<663552,224,4>,<663552,270,3>,<669600,128,3>,<672084,384,4>,<679392,18928,1>,<679500,760,3>,<682080,6,3>,<685464,1092,1>,<689216,90,3>,<691488,336,3>,<694080,4840,1>,<695800,216,3>,<696320,324,4>,<699840,216,3>,<708588,216,3>,<708588,2916,1>,<708736,228,3>,<709236,2200,4>,<718848,56,3>,<718848,168,3>,<720000,120,3>,<725760,64,3>,<725760,128,3>,<725760,220,4>,<725760,342,4>,<725760,384,4>,<727552,270,3>,<728712,20300,1>,<731700,7344,1>,<737280,16,3>,<737280,48,3>,<737280,126,3>,<737280,306,4>,<737280,378,4>,<738192,1014,1>,<740772,21660,1>,<746496,240,3>,<756864,222,3>,<767232,114,3>,<767232,228,3>,<768000,396,4>,<774144,12,3>,<774144,60,3>,<774144,64,3>,<774144,120,3>,<774144,156,3>,<774144,192,3>,<774144,360,4>,<775656,320,3>,<779520,420,4>,<781248,12246,1>,<783360,288,3>,<786432,240,3>,<786432,384,3>,<786800,7896,1>,<787200,168,3>,<787968,240,3>,<790272,294,3>,<795616,288,3>,<796348,4080,1>,<801504,2,4>,<803520,320,1>,<805932,22448,1>,<808704,126,3>,<818496,240,3>,<829440,56,3>,<829440,112,3>,<829440,216,3>,<829440,272,3>,<829440,336,4>,<831600,192,3>,<832536,23188,1>,<835584,144,3>,<835584,270,4>,<835584,432,1>,<838656,48,3>,<838656,90,3>,<838656,144,4>,<839808,180,3>,<844800,24,3>,<844800,72,3>,<844800,360,4>,<844800,384,4>,<855360,360,1>,<859572,23940,1>,<864000,100,3>,<866844,1800,3>,<870912,54,3>,<870912,320,3>,<870912,364,4>,<875556,136,3>,<882372,420,3>,<884736,40,3>,<884736,168,3>,<886464,40,3>,<889344,1552,3>,<890560,144,3>,<892800,6,3>,<892800,288,3>,<893952,98,4>,<898560,84,3>,<905856,14196,1>,<910224,176,3>,<917424,6394,1>,<921600,330,3>,<925440,3630,1>,<933120,192,3>,<933120,330,4>,<933120,380,3>,<940032,8,3>,<940032,24,3>,<940032,168,4>,<940032,324,3>,<943272,26268,1>,<943296,6936,1>,<943488,8,3>,<943488,56,4>,<943488,108,3>,<943488,336,4>,<950400,40,3>,<950400,54,4>,<950400,64,3>,<950400,168,3>,<950400,324,4>,<950400,364,4>,<961272,240,3>,<964100,9672,1>,<967680,6,3>,<967680,48,3>,<967680,96,3>,<967680,288,3>,<977400,1092,4>,<979776,48,3>,<983040,36,3>,<983040,192,4>,<984960,6,3>,<984960,12,3>,<984960,36,3>,<984960,60,4>,<984960,192,4>,<984960,360,4>,<987696,16245,1>,<994048,15576,1>,<995328,180,3>,<995328,280,1>,<1004400,256,3>,<1010000,102,3>,<1016064,312,4>,<1024000,450,3>,<1032192,48,3>,<1032192,90,3>,<1032192,144,3>,<1032192,270,3>,<1036800,342,3>,<1037232,224,4>,<1043700,144,3>,<1044480,36,3>,<1044480,216,3>,<1048320,12,4>,<1048320,72,4>,<1048320,330,4>,<1048576,288,3>,<1048576,1536,1>,<1049600,126,3>,<1049600,252,3>,<1052672,4128,3>,<1056000,36,3>,<1056000,288,3>,<1068672,12,3>,<1068672,24,3>,<1068672,72,3>,<1068672,120,3>,<1069200,288,3>,<1071612,104,3>,<1078272,112,3>,<1081136,1386,3>,<1091328,60,3>,<1091328,180,3>,<1091328,300,3>,<1092300,10956,1>,<1096704,144,3>,<1101520,5640,1>,<1105920,2,3>,<1105920,32,3>,<1105920,42,3>,<1105920,84,3>,<1105920,162,3>,<1105920,252,3>,<1105920,546,4>,<1108800,144,3>,<1114112,108,3>,<1114112,324,3>,<1116184,252,3>,<1119744,432,3>,<1126400,288,3>,<1132500,456,3>,<1135296,148,3>,<1146496,324,3>,<1150848,76,3>,<1150848,152,3>,<1156800,2904,3>,<1161216,8,3>,<1161216,80,3>,<1161216,128,3>,<1161216,240,3>,<1171872,8164,1>,<1172880,910,4>,<1179648,30,3>,<1179648,126,3>,<1179648,160,3>,<1179648,256,1>,<1179648,306,3>,<1179648,480,4>,<1181952,160,3>,<1181952,300,3>,<1185408,392,1>,<1185792,1164,3>,<1193424,192,3>,<1202252,108,3>,<1209600,132,3>,<1213056,84,3>,<1213632,132,3>,<1213632,264,3>,<1234620,12996,1>,<1244160,144,3>,<1244160,224,3>,<1250000,150,3>,<1253376,6,3>,<1253376,18,3>,<1253376,30,3>,<1253376,96,4>,<1253376,180,3>,<1253376,288,3>,<1257728,5202,1>,<1257984,2,3>,<1257984,6,3>,<1257984,32,3>,<1257984,42,3>,<1257984,60,3>,<1257984,96,3>,<1257984,252,4>,<1257984,480,4>,<1257984,486,4>,<1266976,276,3>,<1267200,30,3>,<1267200,48,3>,<1267200,126,4>,<1267200,240,4>,<1267200,256,4>,<1271376,110,4>,<1273584,474,4>,<1280000,360,3>,<1290240,36,3>,<1290240,72,3>,<1290240,216,3>,<1306368,36,3>,<1310720,432,3>,<1317060,4080,1>,<1327104,112,3>,<1327104,210,3>,<1327104,272,3>,<1329300,1484,3>,<1330560,120,3>,<1339200,64,3>,<1339200,192,3>,<1347840,56,3>,<1358784,9464,1>,<1370928,546,1>,<1378432,270,3>,<1378944,180,3>,<1379020,960,3>,<1382400,220,4>,<1382976,168,4>,<1382976,336,3>,<1388160,2420,3>,<1408000,216,3>,<1410048,216,3>,<1411788,8232,1>,<1414944,4624,1>,<1415232,224,3>,<1417472,114,3>,<1424896,288,3>,<1425600,36,3>,<1425600,112,3>,<1425600,216,4>,<1425924,492,3>,<1437696,28,3>,<1437696,84,3>,<1440000,60,3>,<1441908,160,3>,<1451520,64,3>,<1451520,110,3>,<1451520,192,3>,<1457424,10150,1>,<1464100,132,3>,<1474560,24,3>,<1474560,128,3>,<1474560,384,4>,<1477440,8,3>,<1477440,24,3>,<1477440,168,4>,<1477440,240,3>,<1477440,324,4>,<1481544,10830,1>,<1492992,120,3>,<1492992,324,3>,<1492992,380,4>,<1536000,300,1>,<1536000,396,4>,<1548288,2,3>,<1548288,6,3>,<1548288,30,3>,<1548288,60,3>,<1548288,96,3>,<1548288,180,3>,<1548288,486,4>,<1551312,160,3>,<1566720,144,3>,<1572480,220,4>,<1572864,192,3>,<1572864,360,3>,<1573600,3948,4>,<1574400,84,3>,<1574400,168,3>,<1575936,120,3>,<1575936,360,1>,<1580544,294,3>,<1584000,24,3>,<1585248,8112,1>,<1591232,144,3>,<1591232,288,3>,<1603008,48,3>,<1617408,378,1>,<1631848,300,4>,<1636992,120,3>,<1658880,56,3>,<1658880,108,3>,<1658880,168,3>,<1658880,342,3>,<1658880,364,4>,<1665072,11594,1>,<1671168,72,3>,<1671168,216,3>,<1674276,168,3>,<1677312,24,3>,<1677312,72,3>,<1677312,360,4>,<1677312,384,4>,<1679616,288,3>,<1689600,12,3>,<1689600,36,3>,<1689600,180,4>,<1689600,192,4>,<1689600,360,4>,<1690956,5236,1>,<1719744,216,3>,<1726272,304,3>,<1735200,1936,3>,<1741824,160,3>,<1741824,182,3>,<1741824,432,4>,<1769472,20,3>,<1769472,84,3>,<1769472,320,3>,<1772928,200,3>,<1772928,320,3>,<1778688,776,4>,<1787904,294,3>,<1797120,336,3>,<1811712,7098,1>,<1818880,180,3>,<1819584,336,3>,<1820448,176,3>,<1822176,6,4>,<1843200,330,4>,<1861020,1060,3>,<1866240,96,3>,<1880064,12,3>,<1880064,20,3>,<1880064,84,4>,<1880064,120,4>,<1880064,162,3>,<1880064,192,4>,<1880064,504,4>,<1886544,13134,1>,<1886976,28,3>,<1886976,40,3>,<1886976,54,3>,<1886976,64,3>,<1886976,168,3>,<1886976,324,4>,<1900800,2,3>,<1900800,20,3>,<1900800,32,3>,<1900800,84,3>,<1900800,162,3>,<1900800,182,4>,<1910376,316,3>,<1916928,336,3>,<1920000,240,3>,<1933988,1680,3>,<1935360,48,3>,<1935360,144,3>,<1954800,546,3>,<1959552,24,3>,<1959552,324,3>,<1959552,384,1>,<1966080,18,3>,<1966080,96,3>,<1966080,288,3>,<1969920,6,3>,<1969920,18,3>,<1969920,30,3>,<1969920,96,4>,<1969920,180,4>,<1969920,288,4>,<1984056,1380,4>,<1988096,7788,1>,<1990656,90,3>,<1990656,378,3>,<1994544,240,3>,<2005668,10260,1>,<2016000,300,4>,<2016252,128,3>,<2020000,306,3>,<2027520,480,4>,<2032128,156,3>,<2046240,2,3>,<2056392,364,3>,<2059200,168,3>,<2064384,24,3>,<2064384,72,3>,<2064384,384,4>,<2067648,180,3>,<2074464,224,3>,<2088960,108,3>,<2096640,36,3>,<2096640,288,4>,<2097152,768,3>,<2105344,2064,3>,<2112000,144,3>,<2112000,288,4>,<2125764,972,3>,<2137344,6,4>,<2137344,12,4>,<2137344,36,3>,<2137344,60,3>,<2137344,192,4>,<2137344,360,4>,<2156544,56,3>,<2156544,280,3>,<2177280,128,3>,<2182656,150,3>,<2193408,72,3>,<2193408,432,4>,<2195100,2448,3>,<2201472,24,3>,<2201472,144,3>,<2203040,2820,4>,<2204496,288,3>,<2211840,16,3>,<2211840,42,3>,<2211840,126,3>,<2211840,256,4>,<2211840,546,4>,<2213900,132,3>,<2217600,72,3>,<2217600,156,4>,<2222316,7220,1>,<2232000,192,3>,<2239488,216,3>,<2239488,336,1>,<2292992,162,3>,<2292992,324,3>,<2301696,76,3>,<2301696,228,3>,<2304000,132,3>,<2304000,200,3>,<2304000,264,4>,<2313600,1452,3>,<2322432,20,3>,<2322432,40,3>,<2322432,64,3>,<2322432,120,3>,<2322432,324,4>,<2343744,4082,4>,<2359296,240,3>,<2363904,80,3>,<2363904,240,3>,<2371584,582,4>,<2381712,240,3>,<2386848,192,3>,<2396160,252,3>,<2403060,4980,1>,<2426112,42,3>,<2426112,252,3>,<2457600,396,3>,<2469240,6498,1>,<2488320,72,3>,<2488320,112,3>,<2494464,420,1>,<2506752,48,3>,<2506752,90,3>,<2506752,144,3>,<2515456,2601,1>,<2515968,30,3>,<2515968,48,3>,<2515968,126,3>,<2515968,240,4>,<2515968,256,4>,<2519424,360,3>,<2520000,240,3>,<2533952,138,3>,<2534400,8,3>,<2534400,24,3>,<2534400,120,3>,<2534400,128,4>,<2534400,240,4>,<2534400,384,3>,<2539056,3768,3>,<2559016,348,4>,<2560000,180,3>,<2578716,7980,1>,<2580480,36,3>,<2580480,108,3>,<2600532,600,3>,<2612736,18,3>,<2612736,288,3>,<2620800,132,4>,<2635200,248,3>,<2647116,140,3>,<2654208,56,3>,<2659392,180,3>,<2661120,480,4>,<2671680,288,3>,<2672672,2448,1>,<2678400,2,3>,<2678400,160,3>,<2681856,196,3>,<2695680,28,3>,<2695680,224,3>,<2703360,360,1>,<2717568,4732,4>,<2728320,12,4>,<2728320,24,3>,<2728320,72,4>,<2733632,5664,1>,<2755200,6,3>,<2764800,110,3>,<2764800,220,3>,<2776320,1210,4>,<2799360,324,3>,<2805264,192,3>,<2820096,8,3>,<2820096,56,3>,<2820096,108,4>,<2820096,336,4>,<2829816,8756,1>,<2829888,2312,1>,<2830464,36,3>,<2830464,112,3>,<2830464,216,4>,<2849792,144,3>,<2851200,18,3>,<2851200,56,3>,<2851200,108,3>,<2851200,448,4>,<2875392,210,3>,<2875392,224,3>,<2880000,480,3>,<2903040,2,3>,<2903040,32,3>,<2903040,96,3>,<2928200,396,1>,<2932200,364,3>,<2949120,12,3>,<2949120,192,4>,<2949120,330,3>,<2949120,504,4>,<2954880,12,3>,<2954880,20,4>,<2954880,84,3>,<2954880,120,4>,<2954880,162,4>,<2954880,192,4>,<2954880,504,4>,<2985984,252,4>,<3030000,204,3>,<3072000,150,3>,<3072000,450,1>,<3096576,16,3>,<3096576,30,3>,<3096576,48,3>,<3096576,90,3>,<3096576,256,3>,<3096576,306,4>,<3101700,636,3>,<3133440,12,3>,<3133440,72,3>,<3133440,330,4>,<3135248,936,3>,<3137500,1260,3>,<3144960,24,3>,<3144960,110,4>,<3145728,96,3>,<3147200,1974,3>,<3148800,84,3>,<3148800,252,3>,<3148800,420,4>,<3168000,12,3>,<3168000,96,3>,<3168000,192,3>,<3170496,4056,3>,<3175616,180,3>,<3194028,2772,3>,<3206016,8,3>,<3206016,24,3>,<3206016,168,4>,<3206016,240,3>,<3206016,324,4>,<3214836,208,3>,<3225600,396,4>,<3240000,360,3>,<3263696,150,4>,<3273984,60,3>,<3273984,420,4>,<3276900,3652,4>,<3290112,288,3>,<3317760,54,3>,<3317760,84,3>,<3317760,182,4>,<3317760,364,4>,<3326400,48,3>,<3337488,6,3>,<3342336,36,3>,<3342336,108,3>,<3354624,12,3>,<3354624,36,3>,<3354624,180,4>,<3354624,192,4>,<3354624,360,3>,<3359232,144,3>,<3379200,6,3>,<3379200,18,3>,<3379200,90,3>,<3379200,96,3>,<3379200,180,3>,<3379200,288,4>,<3379200,306,4>,<3397500,152,3>,<3439488,108,3>,<3439488,216,3>,<3452544,152,3>,<3458664,7164,1>,<3470400,968,3>,<3483648,80,3>,<3483648,216,4>,<3483648,272,3>,<3502224,272,3>,<3513600,186,3>,<3516792,1668,3>,<3538944,10,3>,<3538944,42,3>,<3538944,160,3>,<3538944,546,4>,<3545856,160,3>,<3548160,360,4>,<3556224,392,1>,<3557376,388,4>,<3571200,12,3>,<3571200,24,3>,<3571200,72,4>,<3594240,168,3>,<3594240,336,3>,<3606756,216,3>,<3606768,288,3>,<3639168,168,1>,<3640896,88,3>,<3640896,264,3>,<3663444,672,3>,<3686400,264,4>,<3732480,48,3>,<3750000,300,3>,<3760128,2,3>,<3760128,6,3>,<3760128,32,3>,<3760128,42,3>,<3760128,60,3>,<3760128,96,4>,<3760128,252,4>,<3760128,480,4>,<3760128,486,4>,<3760128,546,4>,<3773952,2,3>,<3773952,20,3>,<3773952,32,3>,<3773952,84,3>,<3773952,162,4>,<3783976,396,3>,<3801600,10,3>,<3801600,16,3>,<3801600,42,3>,<3801600,80,3>,<3801600,160,3>,<3801600,256,4>,<3801600,272,4>,<3801600,336,4>,<3814128,220,3>,<3820752,158,3>,<3836160,228,3>,<3840000,120,3>,<3840000,360,3>,<3870720,12,3>,<3870720,24,3>,<3870720,72,3>,<3870720,156,3>,<3870720,312,3>,<3870720,330,3>,<3870720,384,4>,<3888000,300,1>,<3919104,192,3>,<3919104,380,4>,<3932160,48,3>,<3932160,144,3>,<3939840,48,3>,<3939840,90,3>,<3939840,144,4>,<3951180,1360,4>,<3968112,690,3>,<3976192,3894,3>,<3981312,384,3>,<4017600,64,3>,<4032000,150,4>,<4055040,240,3>,<4112784,182,3>,<4118400,84,3>,<4128768,36,3>,<4128768,192,3>,<4128768,360,3>,<4136832,60,3>,<4136832,360,4>,<4148928,112,3>,<4148928,336,3>,<4174800,288,3>,<4177920,432,4>,<4193280,144,4>,<4193280,288,4>,<4194304,384,3>,<4199040,216,3>,<4210688,1032,4>,<4224000,72,3>,<4224000,144,3>,<4224000,432,3>,<4235364,2744,1>,<4252416,228,3>,<4274688,6,3>,<4274688,18,3>,<4274688,30,4>,<4274688,96,4>,<4274688,180,4>,<4274688,288,3>,<4276800,72,3>,<4276800,380,4>,<4277772,164,3>,<4285440,320,1>,<4313088,28,3>,<4313088,140,3>,<4313088,280,3>,<4320000,270,3>,<4354560,64,3>,<4354560,342,3>,<4365312,240,3>,<4386816,36,3>,<4386816,216,3>,<4392300,264,3>,<4402944,72,4>,<4406080,1410,3>,<4423680,8,3>,<4423680,128,3>,<4423680,220,3>,<4423680,336,4>,<4432320,8,3>,<4432320,56,4>,<4432320,108,4>,<4432320,336,4>,<4435200,288,3>,<4444632,3610,1>,<4456448,432,3>,<4505600,216,3>,<4541184,296,3>,<4601852,168,3>,<4603392,190,3>,<4608000,100,3>,<4608000,132,3>,<4608000,300,3>,<4608000,396,3>,<4627200,726,3>,<4644864,2,3>,<4644864,20,3>,<4644864,32,3>,<4644864,60,3>,<4644864,162,3>,<4644864,320,3>,<4644864,546,4>,<4653936,320,3>,<4669632,204,3>,<4677120,420,3>,<4691556,3420,1>,<4700160,220,4>,<4718592,120,3>,<4723200,168,3>,<4727808,40,3>,<4727808,120,3>,<4741632,294,3>,<4752000,342,4>,<4755744,2704,3>,<4763424,240,3>,<4773696,6,3>,<4773696,96,3>,<4773696,288,3>,<4787200,216,4>,<4792320,252,3>,<4809024,216,3>,<4852224,126,3>,<4924800,12,3>,<4924800,72,3>,<4924800,330,4>,<4938480,3249,1>,<4976640,36,3>,<4976640,56,3>,<5013504,24,3>,<5013504,72,3>,<5013504,360,4>,<5013504,384,4>,<5031936,8,3>,<5031936,24,3>,<5031936,120,4>,<5031936,128,3>,<5031936,240,4>,<5031936,384,4>,<5068800,12,3>,<5068800,60,3>,<5068800,64,3>,<5068800,120,4>,<5068800,192,3>,<5068800,252,4>,<5068800,360,4>,<5068800,504,4>,<5078112,1884,3>,<5118032,174,4>,<5160960,288,3>,<5225472,144,3>,<5241600,396,3>,<5248000,252,3>,<5270400,124,3>,<5270400,248,3>,<5308416,280,3>,<5308416,288,3>,<5308416,364,4>,<5343360,144,3>,<5345344,1224,1>,<5356800,256,3>,<5391360,112,3>,<5391360,224,3>,<5435136,2366,3>,<5456640,6,4>,<5456640,12,3>,<5456640,36,3>,<5456640,60,3>,<5456640,192,4>,<5456640,360,4>,<5466528,2,3>,<5467264,2832,4>,<5507600,1128,3>,<5529600,110,3>,<5529600,330,3>,<5566400,216,3>,<5570560,324,4>,<5640192,40,3>,<5640192,54,4>,<5640192,64,4>,<5640192,168,4>,<5640192,324,4>,<5640192,364,4>,<5659632,4378,3>,<5660928,18,3>,<5660928,56,3>,<5660928,108,3>,<5660928,448,4>,<5671436,180,4>,<5702400,54,3>,<5702400,224,4>,<5702400,364,4>,<5729472,240,3>,<5750784,112,3>,<5750784,336,3>,<5760000,240,3>,<5765760,360,4>,<5806080,16,3>,<5806080,48,3>,<5806080,220,4>,<5806080,256,3>,<5820416,180,3>,<5864400,182,4>,<5878656,108,3>,<5898240,6,3>,<5898240,32,3>,<5898240,96,4>,<5898240,252,3>,<5898240,306,4>,<5898240,486,4>,<5909760,2,3>,<5909760,6,3>,<5909760,32,3>,<5909760,42,4>,<5909760,60,3>,<5909760,96,4>,<5909760,252,4>,<5909760,480,4>,<5909760,486,4>,<5909760,546,4>,<5927040,392,4>,<5952168,460,3>,<5977420,1560,4>,<6017004,3420,4>,<6048000,100,3>,<6048756,256,3>,<6054912,222,3>,<6068160,264,3>,<6193152,24,3>,<6193152,128,3>,<6193152,240,3>,<6193152,312,3>,<6193152,384,3>,<6266880,36,3>,<6266880,288,4>,<6270496,468,4>,<6289920,12,3>,<6289920,96,3>,<6289920,192,4>,<6289920,330,4>,<6297600,210,3>,<6336000,6,3>,<6336000,48,3>,<6336000,96,3>,<6336000,288,3>,<6340992,2028,3>,<6377292,324,3>,<6412032,12,3>,<6412032,20,3>,<6412032,84,4>,<6412032,120,4>,<6412032,162,4>,<6412032,192,3>,<6412032,504,4>,<6451200,396,4>,<6547968,300,3>,<6580224,144,3>,<6585300,816,4>,<6604416,48,3>,<6635520,42,3>,<6635520,182,3>,<6635520,224,3>,<6635520,272,4>,<6635520,432,4>,<6641700,264,3>,<6652800,24,3>,<6652800,192,3>,<6652800,312,4>,<6652800,384,4>,<6684672,270,4>,<6684672,288,1>,<6709248,6,3>,<6709248,18,3>,<6709248,90,3>,<6709248,96,4>,<6709248,180,3>,<6709248,288,4>,<6709248,306,4>,<6718464,72,3>,<6758400,48,3>,<6758400,90,3>,<6758400,144,3>,<6758400,270,3>,<6771600,240,3>,<6878976,108,3>,<6878976,324,3>,<6895100,192,4>,<6905088,76,3>,<6912000,200,3>,<6912000,264,4>,<6914880,336,4>,<6917328,3582,4>,<6940800,484,3>,<6967296,40,3>,<6967296,108,3>,<6967296,364,4>,<7004448,272,3>,<7030800,256,3>,<7033584,834,3>,<7044216,2100,3>,<7077888,80,3>,<7077888,210,3>,<7091712,80,3>,<7096320,360,3>,<7114752,194,4>,<7142400,6,3>,<7142400,12,3>,<7142400,36,3>,<7142400,60,4>,<7142400,192,3>,<7142400,360,4>,<7180800,144,3>,<7188480,84,3>,<7188480,168,3>,<7209180,1660,4>,<7278336,84,3>,<7281792,220,3>,<7288704,12,4>,<7288704,24,3>,<7288704,72,4>,<7372800,132,3>,<7387200,220,4>,<7464960,24,3>,<7464960,380,4>,<7483392,420,1>,<7501764,852,3>,<7520256,30,3>,<7520256,48,3>,<7520256,126,4>,<7520256,240,4>,<7520256,256,4>,<7547904,10,3>,<7547904,16,3>,<7547904,42,3>,<7547904,80,3>,<7547904,160,3>,<7547904,256,4>,<7547904,272,4>,<7547904,336,4>,<7567952,198,3>,<7601856,276,3>,<7603200,8,3>,<7603200,80,3>,<7603200,128,3>,<7603200,168,4>,<7603200,240,4>,<7603200,336,4>,<7617168,1256,4>,<7667712,252,3>,<7680000,60,3>,<7680000,180,3>,<7690176,240,3>,<7736148,2660,3>,<7738848,6,4>,<7741440,6,3>,<7741440,12,3>,<7741440,36,3>,<7741440,156,3>,<7741440,192,3>,<7741440,330,4>,<7801596,200,4>,<7833600,132,4>,<7838208,6,3>,<7838208,96,3>,<7862400,264,3>,<7864320,72,3>,<7864320,384,4>,<7872000,168,3>,<7879680,24,3>,<7879680,72,3>,<7879680,360,4>,<7879680,384,4>,<7902720,294,3>,<7941348,280,3>,<7956160,288,3>,<7962624,360,3>,<7978176,60,3>,<7978176,360,1>,<8035200,320,3>,<8064000,450,3>,<8110080,120,3>,<8146944,252,3>,<8184960,8,3>,<8184960,24,3>,<8184960,168,4>,<8184960,324,4>,<8236800,252,4>,<8257536,18,3>,<8257536,96,3>,<8257536,180,3>,<8257536,288,3>,<8265600,2,3>,<8273664,180,3>,<8294400,220,3>,<8294400,342,4>,<8297856,280,3>,<8349600,288,3>,<8355840,216,4>,<8355840,432,4>,<8386560,72,3>,<8386560,144,4>,<8386560,432,3>,<8421376,516,4>,<8448000,36,3>,<8448000,72,3>,<8448000,216,3>,<8460288,36,4>,<8460288,112,3>,<8460288,216,4>,<8491392,72,4>,<8491392,380,4>,<8549376,48,3>,<8549376,90,3>,<8549376,144,3>,<8553600,36,3>,<8602872,2244,4>,<8626176,140,3>,<8626176,224,3>,<8709120,432,4>,<8730624,120,3>,<8773632,108,3>,<8805888,288,4>,<8847360,64,3>,<8847360,110,3>,<8847360,168,4>,<8847360,324,4>,<8864640,40,3>,<8864640,54,3>,<8864640,64,4>,<8864640,168,4>,<8864640,324,4>,<8864640,364,4>,<8870400,144,3>,<8870400,288,3>,<8912896,216,3>,<8929472,252,3>,<9082368,148,3>,<9082368,296,3>,<9206784,304,3>,<9216000,150,4>,<9289728,10,3>,<9289728,16,3>,<9289728,30,3>,<9289728,160,3>,<9289728,256,4>,<9289728,546,4>,<9305100,212,3>,<9400320,24,3>,<9400320,110,4>,<9434880,220,4>,<9434880,342,4>,<9446400,84,3>,<9455616,320,3>,<9504000,192,3>,<9511488,1352,3>,<9526848,120,3>,<9547392,240,3>,<9582084,924,4>,<9618048,8,3>,<9618048,56,4>,<9618048,108,4>,<9618048,336,4>,<9660328,540,3>,<9676800,132,4>,<9676800,264,4>,<9791088,300,3>,<9821952,270,3>,<9849600,36,3>,<9849600,288,4>,<9882516,1176,4>,<9953280,18,3>,<9953280,288,3>,<9953280,364,4>,<9953280,378,3>,<9979200,16,3>,<10012464,2,3>,<10027008,12,3>,<10027008,36,3>,<10027008,180,4>,<10027008,192,4>,<10027008,360,4>,<10063872,12,3>,<10063872,60,3>,<10063872,64,3>,<10063872,120,3>,<10063872,192,4>,<10063872,252,4>,<10063872,360,4>,<10063872,504,4>,<10076160,420,3>,<10080000,60,3>,<10080000,360,4>,<10137600,2,3>,<10137600,6,3>,<10137600,30,3>,<10137600,60,3>,<10137600,96,3>,<10137600,126,3>,<10137600,180,3>,<10137600,252,4>,<10137600,486,4>,<10156224,942,3>,<10192500,304,3>,<10318464,216,3>,<10321920,144,3>,<10342080,24,3>,<10342080,144,4>,<10375992,2388,4>,<10450944,72,3>,<10450944,360,4>,<10540800,124,3>,<10550376,556,4>,<10616832,182,3>,<10616832,270,3>,<10644480,240,3>,<10686720,12,3>,<10686720,72,3>,<10686720,330,4>,<10690688,612,1>,<10713600,8,4>,<10713600,24,3>,<10713600,128,3>,<10713600,168,4>,<10713600,324,4>,<10741248,342,4>,<10782720,112,3>,<10782720,336,3>,<10913280,6,4>,<10913280,18,3>,<10913280,30,4>,<10913280,96,4>,<10913280,180,3>,<10913280,288,4>,<10922688,88,3>,<10934528,1416,4>,<10990332,224,3>,<11000000,360,1>,<11015200,564,3>,<11020800,12,3>,<11020800,24,4>,<11020800,72,3>,<11027456,270,3>,<11280384,2,3>,<11280384,20,3>,<11280384,32,3>,<11280384,84,4>,<11280384,162,4>,<11280384,182,4>,<11321856,28,3>,<11321856,54,3>,<11321856,224,3>,<11337408,216,3>,<11404800,160,3>,<11404800,182,4>,<11404800,224,3>,<11404800,432,4>,<11462256,316,3>,<11501568,168,3>,<11508480,76,3>,<11520000,120,3>,<11524032,280,3>,<11535264,320,3>,<11594252,228,3>,<11612160,8,4>,<11612160,24,3>,<11612160,110,3>,<11612160,128,3>,<11612160,220,3>,<11612160,312,4>,<11612160,324,4>,<11757312,324,3>,<11796480,48,3>,<11796480,126,3>,<11796480,256,4>,<11796480,306,4>,<11819520,30,3>,<11819520,48,3>,<11819520,126,4>,<11819520,240,3>,<11819520,256,4>,<11904336,230,3>,<11908560,6,3>,<11943936,240,3>,<12015300,996,4>,<12052800,288,3>,<12083904,304,3>,<12096000,300,3>,<12245200,288,3>,<12275712,228,3>,<12312000,132,4>,<12338352,364,3>,<12355200,28,3>,<12355200,168,3>,<12386304,12,3>,<12386304,120,3>,<12386304,156,3>,<12386304,192,4>,<12410496,120,3>,<12446784,112,4>,<12491176,588,3>,<12533760,144,3>,<12533760,288,3>,<12540992,234,3>,<12579840,6,3>,<12579840,48,3>,<12579840,96,4>,<12579840,288,3>,<12582912,384,3>,<12597120,72,3>,<12672000,48,3>,<12672000,144,3>,<12681984,1014,4>,<12824064,2,3>,<12824064,6,3>,<12824064,32,3>,<12824064,42,4>,<12824064,60,3>,<12824064,96,3>,<12824064,252,4>,<12824064,480,4>,<12824064,546,4>,<12830400,24,3>,<12830400,324,4>,<12856320,320,1>,<12939264,280,3>,<13063680,288,4>,<13095936,240,3>,<13160448,72,3>,<13160448,156,4>,<13200000,300,4>,<13208832,192,4>,<13208832,384,4>,<13224960,420,4>,<13271040,112,4>,<13271040,216,3>,<13271040,272,4>,<13296960,36,3>,<13296960,112,4>,<13296960,216,4>,<13305600,96,3>,<13305600,156,3>,<13305600,192,3>,<13349952,12,4>,<13349952,24,3>,<13349952,72,4>,<13369344,144,3>,<13392000,192,3>,<13418496,48,3>,<13418496,90,3>,<13418496,144,3>,<13418496,270,3>,<13516800,24,3>,<13516800,72,3>,<13516800,384,4>,<13537916,240,3>,<13615200,6,3>,<13757952,270,3>,<13824000,100,3>,<13824000,132,3>,<13881600,242,3>,<13934592,20,3>,<13934592,54,3>,<13934592,182,4>,<13934592,270,3>,<13934592,364,4>,<14008896,136,3>,<14074668,1140,1>,<14088432,1050,4>,<14183424,40,3>,<14257152,144,4>,<14284800,6,3>,<14284800,18,3>,<14284800,30,3>,<14284800,96,4>,<14284800,180,4>,<14284800,288,4>,<14303232,294,3>,<14321088,2,4>,<14321088,96,3>,<14361600,72,3>,<14361600,432,4>,<14376960,84,3>,<14376960,252,3>,<14577408,6,3>,<14577408,12,4>,<14577408,36,3>,<14577408,60,4>,<14577408,192,4>,<14577408,360,4>,<14774400,24,3>,<14774400,110,4>,<14929920,192,3>,<14929920,380,3>,<15040512,8,3>,<15040512,24,3>,<15040512,120,3>,<15040512,128,4>,<15040512,240,4>,<15095808,8,3>,<15095808,80,3>,<15095808,128,3>,<15095808,168,4>,<15095808,240,4>,<15095808,336,3>,<15206400,20,3>,<15206400,40,3>,<15206400,64,3>,<15206400,84,4>,<15206400,120,3>,<15206400,168,4>,<15206400,324,4>,<15234336,628,3>,<15482880,6,3>,<15482880,18,3>,<15482880,96,4>,<15667200,396,4>,<15676416,48,3>,<15676416,240,4>,<15687500,252,4>,<15724800,132,3>,<15728640,192,4>,<15744000,84,3>,<15759360,12,3>,<15759360,36,3>,<15759360,180,4>,<15759360,192,4>,<15759360,360,3>,<15811200,248,3>,<15827176,636,3>,<15925248,180,3>,<15956352,180,3>,<16030080,48,3>,<16030080,220,4>,<16070400,256,3>,<16111872,228,3>,<16160000,306,3>,<16174080,224,3>,<16257024,156,3>,<16257024,312,4>,<16369920,12,3>,<16369920,20,4>,<16369920,84,4>,<16369920,120,3>,<16369920,162,4>,<16369920,192,4>,<16387284,1104,4>,<16515072,48,3>,<16515072,90,3>,<16515072,144,3>,<16541184,180,3>,<16588800,110,3>,<16588800,342,4>,<16699200,144,3>,<16711680,108,3>,<16711680,216,3>,<16773120,36,3>,<16773120,72,4>,<16773120,216,3>,<16793600,252,3>,<16842752,258,3>,<16896000,36,3>,<16896000,108,3>,<16920576,18,3>,<16920576,56,3>,<16920576,108,3>,<16920576,448,4>,<16982784,36,3>,<17098752,24,3>,<17098752,72,3>,<17098752,360,4>,<17098752,384,4>,<17107200,18,3>,<17107200,288,4>,<17205744,1122,3>,<17233920,360,4>,<17252352,112,3>,<17297280,120,3>,<17418240,16,3>,<17418240,216,4>,<17461248,60,3>,<17461248,180,3>,<17547264,432,3>,<17611776,144,3>,<17611776,288,4>,<17635968,216,3>,<17694720,2,3>,<17694720,84,3>,<17694720,162,3>,<17729280,2,3>,<17729280,20,3>,<17729280,32,3>,<17729280,84,3>,<17729280,160,3>,<17729280,162,4>,<17729280,182,4>,<17729280,320,3>,<17740800,72,3>,<17740800,144,3>,<17926272,180,4>,<18051012,1140,4>,<18053372,264,3>,<18144000,200,3>,<18164736,148,3>,<18413568,152,3>,<18579456,8,3>,<18579456,80,3>,<18579456,128,3>,<18748800,96,3>,<18800640,12,3>,<18800640,96,3>,<18800640,192,4>,<18800640,330,4>,<18869760,110,3>,<18869760,192,3>,<18966528,392,1>,<19008000,2,3>,<19008000,96,3>,<19022976,676,4>,<19094784,12,3>,<19094784,24,3>,<19094784,72,3>,<19236096,40,3>,<19236096,54,4>,<19236096,64,3>,<19236096,168,4>,<19236096,364,4>,<19320656,270,4>,<19353600,132,3>,<19418112,264,3>,<19595520,192,3>,<19699200,144,4>,<19699200,288,4>,<19740672,48,3>,<19755900,272,3>,<19813248,16,3>,<19845936,6,3>,<19906560,144,3>,<19906560,182,4>,<19958400,64,3>,<19958400,128,3>,<20054016,6,3>,<20054016,18,3>,<20054016,90,3>,<20054016,96,4>,<20054016,180,3>,<20127744,2,3>,<20127744,6,3>,<20127744,30,3>,<20127744,60,3>,<20127744,96,3>,<20127744,126,3>,<20127744,180,3>,<20127744,252,3>,<20160000,180,3>,<20275200,16,3>,<20275200,30,3>,<20275200,48,3>,<20275200,90,3>,<20275200,126,3>,<20275200,306,4>,<20636928,108,3>,<20643840,72,3>,<20684160,72,3>,<20684160,156,4>,<20715264,342,1>,<20751984,1194,3>,<20901888,36,3>,<20901888,180,3>,<21081600,310,3>,<21100752,278,3>,<21132648,700,3>,<21288960,120,3>,<21373440,36,3>,<21373440,288,3>,<21381376,306,3>,<21427200,12,3>,<21427200,20,4>,<21427200,64,3>,<21427200,84,4>,<21427200,120,4>,<21427200,162,4>,<21427200,192,3>,<21436800,420,4>,<21454848,196,3>,<21542400,288,4>,<21565440,28,3>,<21565440,56,3>,<21565440,168,3>,<21826560,48,3>,<21826560,90,3>,<21826560,144,4>,<21866112,8,3>,<21866112,24,3>,<21866112,168,4>,<21866112,324,4>,<21869056,708,3>,<22030400,282,3>,<22041600,6,3>,<22041600,12,3>,<22041600,36,3>,<22041600,60,4>,<22041600,192,4>,<22127616,336,3>,<22442112,144,3>,<22505292,284,3>,<22560768,10,3>,<22560768,16,3>,<22560768,42,3>,<22560768,80,3>,<22560768,160,4>,<22560768,336,4>,<22643712,112,4>,<22643712,160,3>,<22643712,224,3>,<22809600,56,3>,<22809600,80,3>,<22809600,112,4>,<22809600,216,3>,<22809600,272,4>,<22917888,60,3>,<23003136,84,3>,<23016960,228,3>,<23040000,60,3>,<23070528,160,3>,<23216544,2,3>,<23224320,12,3>,<23224320,64,3>,<23224320,110,3>,<23224320,156,3>,<23224320,162,4>,<23500800,264,4>,<23592960,24,3>,<23639040,8,3>,<23639040,24,3>,<23639040,120,4>,<23639040,128,3>,<23639040,240,3>,<23887872,120,3>,<23934528,120,3>,<24192000,150,3>,<24240000,204,3>,<24440832,84,3>,<24554880,8,3>,<24554880,56,4>,<24554880,108,4>,<24710400,84,3>,<24772608,6,3>,<24772608,32,3>,<24772608,60,3>,<24772608,96,3>,<24772608,306,4>,<24982352,294,4>,<25048800,6,3>,<25067520,72,3>,<25067520,144,3>,<25159680,48,3>,<25159680,144,3>,<25165824,192,3>,<25190400,168,3>,<25288704,294,3>,<25344000,12,3>,<25344000,24,3>,<25344000,72,3>,<25380864,72,4>,<25380864,380,4>,<25459712,288,3>,<25474176,24,3>,<25474176,324,4>,<25648128,30,3>,<25648128,48,3>,<25648128,126,4>,<25648128,240,4>,<25648128,256,4>,<25660800,192,4>,<25808616,748,3>,<25878528,140,3>,<26127360,144,3>,<26191872,120,3>,<26208000,300,4>,<26320896,36,3>,<26320896,288,3>,<26400000,150,3>,<26417664,96,3>,<26417664,192,4>,<26542080,56,3>,<26542080,108,3>,<26593920,18,3>,<26593920,56,3>,<26593920,108,3>,<26593920,448,4>,<26611200,6,4>,<26611200,48,3>,<26611200,96,3>,<26699904,6,3>,<26699904,12,3>,<26699904,36,3>,<26699904,60,4>,<26699904,192,4>,<26716800,132,4>,<26738688,72,3>,<26788416,168,3>,<26836992,24,3>,<26836992,72,3>,<27033600,36,3>,<27033600,192,3>,<27283200,12,4>,<27283200,72,4>,<27283200,330,4>,<27869184,10,3>,<27869184,182,3>,<27869184,272,4>,<28003968,6,3>,<28200960,220,4>,<28200960,342,4>,<28366848,200,3>,<28514304,72,3>,<28569600,48,3>,<28569600,90,3>,<28569600,144,4>,<28580544,120,3>,<28723200,36,3>,<28723200,216,4>,<28746252,308,4>,<28828800,72,3>,<28854144,36,3>,<28854144,112,4>,<29127168,176,3>,<29154816,6,3>,<29154816,18,3>,<29154816,30,4>,<29154816,96,3>,<29154816,180,4>,<29280808,780,3>,<29548800,12,3>,<29548800,96,4>,<29548800,192,4>,<29647548,392,4>,<29859840,96,3>,<29887100,312,3>,<30000000,300,3>,<30081024,12,3>,<30081024,60,3>,<30081024,64,4>,<30081024,120,3>,<30081024,252,4>,<30191616,20,3>,<30191616,40,3>,<30191616,64,3>,<30191616,84,3>,<30191616,120,3>,<30191616,168,3>,<30240000,120,3>,<30412800,2,3>,<30412800,20,3>,<30412800,32,3>,<30412800,42,3>,<30412800,60,3>,<30412800,84,3>,<30412800,162,3>,<30468672,314,4>,<30513024,220,4>,<30720000,240,4>,<30955392,12,3>,<30955392,24,3>,<30955392,72,4>,<30965760,48,4>,<31026240,48,3>,<31072896,228,1>,<31127976,796,3>,<31352832,24,3>,<31352832,120,3>,<31352832,380,3>,<31457280,96,3>,<31518720,6,3>,<31518720,18,3>,<31518720,90,3>,<31518720,96,3>,<31518720,180,3>,<31518720,306,4>,<31622400,124,3>,<31654352,318,3>,<31850496,90,3>,<32060160,24,3>,<32060160,110,4>,<32060160,192,4>,<32140800,8,3>,<32140800,56,3>,<32140800,108,4>,<32140800,128,3>,<32223744,114,3>,<32348160,112,3>,<32514048,156,3>,<32739840,2,3>,<32739840,6,3>,<32739840,32,3>,<32739840,42,3>,<32739840,60,3>,<32739840,96,4>,<32739840,546,4>,<33030144,72,3>,<33062400,8,3>,<33062400,24,3>,<33062400,168,3>,<33062400,324,4>,<33082368,180,3>,<33191424,224,3>,<33423360,108,3>,<33546240,36,3>,<33546240,108,3>,<33841152,54,3>,<33841152,224,3>,<33965568,18,3>,<34019328,228,3>,<34197504,12,3>,<34197504,36,3>,<34197504,180,4>,<34197504,192,4>,<34214400,144,3>,<34394880,108,3>,<34504704,56,3>,<34525440,152,3>,<34836480,8,3>,<34836480,108,4>,<34836480,342,4>,<35094528,216,3>,<35223552,72,3>,<35223552,144,4>,<35389440,16,3>,<35389440,42,3>,<35458560,10,3>,<35458560,16,3>,<35458560,42,3>,<35458560,80,3>,<35458560,160,4>,<35458560,272,4>,<35458560,336,4>,<35481600,72,3>,<35712000,12,3>,<35712000,72,4>,<35712000,330,4>,<35725680,2,3>,<36045900,332,3>,<36158400,96,3>,<36288000,100,3>,<36827136,76,3>,<37065600,56,3>,<37158912,40,3>,<37158912,64,3>,<37231488,40,3>,<37231488,320,3>,<37601280,6,4>,<37601280,48,3>,<37601280,96,3>,<37739520,2,3>,<37739520,96,3>,<38016000,48,3>,<38016000,336,4>,<38045952,338,3>,<38189568,6,3>,<38189568,12,3>,<38189568,36,3>,<38189568,60,4>,<38189568,192,3>,<38413440,84,3>,<38450880,6,4>,<38472192,2,3>,<38472192,20,3>,<38472192,32,3>,<38472192,84,4>,<38472192,182,4>,<38707200,330,4>,<39398400,72,3>,<39398400,144,4>,<39481344,192,3>,<39600000,100,4>,<39626496,64,4>,<39626496,128,3>,<39813120,72,3>,<39890880,72,3>,<39916800,64,3>,<40049856,8,3>,<40049856,24,3>,<40049856,168,4>,<40049856,324,4>,<40108032,48,4>,<40108032,90,3>,<40176000,64,3>,<40255488,16,3>,<40255488,30,3>,<40255488,48,4>,<40255488,90,3>,<40255488,126,3>,<40550400,24,3>,<40550400,128,3>,<40845600,2,3>,<40924800,220,4>,<41287680,36,3>,<41368320,288,4>,<41541452,348,4>,<41803776,18,3>,<41803776,90,3>,<42224004,380,3>,<42265296,350,4>,<42561792,420,4>,<42746880,144,4>,<42854400,2,3>,<42854400,6,3>,<42854400,32,3>,<42854400,42,3>,<42854400,60,3>,<42854400,96,4>,<42909696,196,3>,<43084800,144,4>,<43130880,28,3>,<43130880,84,3>,<43653120,24,3>,<43653120,72,3>,<43732224,12,3>,<43732224,20,3>,<43732224,84,4>,<43732224,120,4>,<43732224,162,4>,<43738112,354,4>,<44083200,6,3>,<44083200,18,3>,<44083200,30,4>,<44083200,96,4>,<44352000,288,4>,<44884224,156,4>,<45121536,8,3>,<45121536,80,3>,<45121536,168,4>,<45287424,56,3>,<45287424,80,3>,<45287424,112,3>,<45411840,296,3>,<45619200,40,3>,<45619200,56,3>,<45619200,108,3>,<45619200,280,4>,<46010876,360,3>,<46448640,2,3>,<46448640,6,3>,<46448640,32,3>,<46879728,6,3>,<47001600,132,4>,<47278080,12,3>,<47278080,60,3>,<47278080,64,3>,<47278080,120,3>,<47278080,252,4>,<47634240,12,3>,<47634240,24,3>,<47634240,72,3>,<48335616,76,3>,<49109760,40,3>,<49109760,54,3>,<49109760,64,3>,<49109760,364,4>,<49161852,368,3>,<49545216,30,3>,<49545216,48,3>,<49641984,240,3>,<50135040,36,3>,<50135040,72,3>,<50319360,12,3>,<50319360,24,3>,<50319360,72,3>,<50380800,84,3>,<50688000,6,3>,<50688000,12,3>,<50688000,36,3>,<50688000,252,4>,<50761728,36,3>,<50972544,132,3>,<51296256,8,4>,<51296256,24,3>,<51296256,120,4>,<51296256,128,4>,<51321600,96,4>,<51617232,374,3>,<51701760,120,3>,<52383744,60,3>,<52416000,150,3>,<52641792,144,3>,<52704000,124,3>,<52835328,6,3>,<52835328,48,3>,<52835328,96,3>,<52907904,72,3>,<53084160,54,3>,<53187840,54,3>,<53187840,224,4>,<53222400,48,3>,<53222400,240,3>,<53399808,6,3>,<53399808,18,3>,<53399808,30,3>,<53399808,96,3>,<53568000,220,4>,<53673984,36,3>,<53778816,60,3>,<54067200,18,3>,<54067200,96,3>,<54153036,380,3>,<54460800,12,3>,<54460800,24,3>,<54460800,72,4>,<54566400,36,3>,<55888892,384,3>,<56401920,110,3>,<57028608,36,3>,<57139200,24,3>,<57139200,72,3>,<57284352,8,4>,<57284352,24,3>,<57284352,168,4>,<57446400,108,4>,<57708288,18,3>,<57708288,56,3>,<58060800,220,4>,<58254336,88,3>,<58309632,48,4>,<58309632,90,3>,<58561616,390,3>,<59097600,6,4>,<59097600,48,3>,<59097600,96,3>,<59222016,16,3>,<59537808,2,4>,<59719680,48,3>,<60162048,2,3>,<60162048,6,3>,<60162048,30,3>,<60162048,60,3>,<60162048,126,3>,<60383232,2,3>,<60383232,20,3>,<60383232,32,3>,<60383232,42,3>,<60383232,60,3>,<60383232,84,3>,<60480000,60,3>,<60825600,10,3>,<60825600,16,3>,<60825600,30,3>,<60825600,42,3>,<60825600,210,3>,<61910784,6,3>,<61910784,12,3>,<61910784,36,3>,<61910784,60,4>,<61931520,24,3>,<62029440,6,4>,<62052480,192,4>,<62145792,114,3>,<62255952,398,3>,<62705664,60,4>,<63037440,48,3>,<63037440,90,3>,<64120320,12,3>,<64120320,96,4>,<64281600,40,4>,<64281600,54,4>,<64281600,64,3>,<64696320,56,3>,<65479680,30,3>,<65479680,48,3>,<65598336,8,3>,<65598336,56,4>,<65598336,108,4>,<66000000,60,3>,<66124800,12,3>,<66124800,20,4>,<66124800,84,3>,<66124800,162,4>,<66189312,180,3>,<66382848,112,3>,<66528000,192,3>,<66977280,144,4>,<67326336,48,3>,<68208000,132,4>,<68395008,6,3>,<68395008,18,3>,<68395008,90,3>,<68395008,96,3>,<68395008,306,4>,<68428800,72,3>,<69009408,28,3>,<69050880,76,3>,<69672960,54,3>,<70189056,108,3>,<70917120,8,3>,<70917120,80,3>,<70917120,168,4>,<71424000,36,3>,<72887040,12,4>,<72887040,72,4>,<73322496,28,3>,<73656000,160,3>,<73664640,36,4>,<74131200,28,3>,<74317824,2,3>,<74317824,20,3>,<74462976,160,3>,<74995200,24,3>,<75146400,2,4>,<75202560,48,3>,<75479040,48,3>,<76032000,8,3>,<76032000,24,3>,<76032000,168,4>,<76142592,24,3>,<76379136,6,3>,<76379136,18,3>,<76379136,30,3>,<76379136,96,3>,<76422528,108,3>,<76826880,42,3>,<76944384,10,3>,<76944384,16,3>,<76944384,42,3>,<76944384,80,4>,<76944384,272,4>,<78624000,100,3>,<78796800,36,3>,<78796800,72,3>,<78962688,96,3>,<79252992,64,3>,<79383744,12,3>,<79383744,24,4>,<79626240,36,3>,<79781760,36,3>,<79833600,2,3>,<79833600,32,3>,<79833600,160,3>,<80099712,12,3>,<80099712,20,3>,<80099712,84,4>,<80099712,162,4>,<80216064,24,3>,<80510976,24,3>,<81100800,12,3>,<81849600,24,4>,<81849600,110,4>,<82736640,144,4>,<83356416,84,4>,<84011904,2,3>,<85493760,72,3>,<85708800,30,3>,<85708800,48,3>,<86169600,72,3>,<86486400,24,3>,<87306240,12,3>,<87306240,36,3>,<87464448,2,3>,<87464448,6,3>,<87464448,32,3>,<87464448,42,4>,<87464448,60,4>,<87607296,6,3>,<88166400,48,3>,<88704000,144,3>,<89280000,132,4>,<90243072,20,3>,<90243072,40,3>,<90243072,84,4>,<90574848,28,3>,<90574848,40,3>,<90574848,56,3>,<90823680,148,3>,<91238400,20,3>,<91238400,54,3>,<92866176,8,3>,<92866176,24,3>,<92866176,168,4>,<92897280,16,3>,<93078720,16,3>,<94556160,2,3>,<94556160,6,3>,<94556160,30,3>,<94556160,60,3>,<94556160,126,3>,<95268480,6,4>,<95268480,12,3>,<95268480,36,3>,<95268480,60,4>,<96422400,36,3>,<96768000,132,3>,<98219520,2,3>,<98219520,20,3>,<98219520,32,3>,<98219520,182,4>,<98304192,132,3>,<99090432,24,3>,<99187200,8,3>,<99187200,56,4>,<99187200,108,4>,<99283968,120,3>,<100195200,12,3>,<100195200,24,3>,<100270080,36,3>,<100638720,6,3>,<100638720,12,3>,<100638720,36,3>,<101376000,6,3>,<101376000,18,3>,<101523456,18,3>,<101896704,6,3>,<102592512,12,3>,<102592512,60,3>,<102592512,64,4>,<102643200,48,3>,<103020000,6,3>,<104509440,36,4>,<105283584,72,3>,<105670656,48,3>,<106444800,12,3>,<106444800,24,3>,<106799616,48,3>,<107136000,24,4>,<107136000,110,4>,<107347968,18,3>,<108134400,48,3>,<108921600,6,3>,<108921600,12,4>,<108921600,36,4>,<108921600,60,4>,<110208000,12,4>,<111447648,6,3>,<112015872,12,3>,<112015872,24,3>,<112803840,2,3>,<114278400,12,3>,<114278400,36,3>,<114568704,12,3>,<114568704,20,3>,<114568704,84,4>,<114589440,156,4>,<115240320,28,3>,<115352640,2,3>,<116121600,110,4>,<116619264,24,4>,<118195200,48,3>,<118444032,64,3>,<119439360,24,3>,<119672640,24,3>,<120149568,8,3>,<120149568,56,3>,<120149568,108,4>,<120324096,16,3>,<120324096,30,3>,<120766464,10,3>,<120766464,16,3>,<120766464,30,3>,<120766464,42,3>,<121651200,8,3>,<123821568,6,3>,<123821568,18,3>,<123821568,30,4>,<123863040,12,3>,<124104960,96,4>,<126074880,24,3>,<128240640,6,3>,<128240640,48,3>,<128563200,2,3>,<128563200,20,3>,<128563200,32,3>,<129392640,28,3>,<129843216,6,3>,<130959360,8,3>,<130959360,24,3>,<131040000,60,3>,<131196672,40,4>,<131196672,54,4>,<132249600,2,3>,<132249600,6,3>,<132249600,32,4>,<132249600,42,4>,<133056000,96,3>,<133499520,12,3>,<133954560,72,3>,<135364608,56,4>,<136790016,48,3>,<136857600,36,3>,<139345920,2,3>,<139851360,6,4>,<140639184,2,3>,<141834240,20,3>,<141834240,40,3>,<141834240,84,4>,<142902720,8,4>,<142902720,24,3>,<144458496,108,3>,<145339392,144,4>,<145774080,36,4>,<147329280,18,3>,<148635648,10,3>,<148635648,16,3>,<150057600,60,3>,<150405120,12,3>,<150405120,24,3>,<150958080,8,3>,<150958080,24,3>,<152064000,12,3>,<152064000,84,4>,<152758272,48,3>,<153062784,24,3>,<153803520,12,3>,<153803520,24,4>,<153888768,8,3>,<157593600,36,3>,<157925376,6,3>,<157925376,48,3>,<158505984,2,3>,<158505984,32,3>,<158767488,6,3>,<158767488,12,3>,<158767488,60,4>,<159252480,18,3>,<159563520,18,3>,<159667200,16,3>,<160199424,2,4>,<160199424,6,3>,<160199424,32,3>,<160199424,42,4>,<161021952,12,3>,<161591808,6,3>,<162201600,6,3>,<162201600,32,3>,<163382400,8,3>,<163382400,24,3>,<163699200,12,4>,<165473280,72,4>,<170987520,36,3>,<171417600,8,3>,<171417600,24,3>,<171853056,8,3>,<171853056,56,4>,<172339200,36,3>,<174612480,6,3>,<174612480,18,3>,<174928896,30,3>,<176332800,24,3>,<177292800,2,3>,<180486144,2,3>,<180486144,20,3>,<180486144,42,3>,<181149696,20,3>,<181149696,28,3>,<182476800,10,3>,<185732352,12,3>,<185732352,20,4>,<185732352,84,4>,<185794560,8,3>,<186088320,2,3>,<186157440,64,4>,<187518912,12,3>,<187518912,24,3>,<189112320,16,3>,<189112320,30,3>,<190536960,6,4>,<190536960,18,3>,<190536960,30,4>,<190947840,12,3>,<192844800,18,3>,<196416000,60,4>,<196439040,10,3>,<196439040,16,3>,<196795008,36,3>,<198374400,54,4>,<200390400,6,3>,<200390400,12,3>,<200390400,60,4>,<201277440,6,3>,<201277440,18,3>,<201979008,16,3>,<205185024,2,3>,<205185024,6,3>,<205185024,30,3>,<205286400,24,3>,<209018880,18,3>,<210567168,36,3>,<211341312,12,3>,<211341312,24,4>,<212751360,56,3>,<212808960,84,4>,<212889600,6,3>,<212889600,12,3>,<212889600,60,4>,<213599232,24,3>,<214272000,12,3>,<217843200,6,3>,<217843200,18,3>,<217843200,30,4>,<218661120,24,3>,<224031744,6,3>,<224031744,12,4>,<224031744,60,4>,<228096000,8,3>,<228096000,56,4>,<228556800,6,3>,<228556800,18,3>,<229137408,2,3>,<229137408,6,3>,<229137408,32,3>,<229137408,42,4>,<233238528,12,3>,<236390400,12,3>,<236390400,24,3>,<238151232,8,3>,<240299136,54,4>,<241532928,8,3>,<247726080,6,3>,<248117760,12,3>,<248117760,24,4>,<248209920,6,3>,<248209920,48,3>,<250069248,28,3>,<257126400,10,3>,<257126400,16,3>,<258080256,6,4>,<258508800,24,3>,<261918720,12,3>,<262393344,2,3>,<262393344,20,3>,<262821888,2,4>,<267909120,36,3>,<273580032,24,3>,<273715200,18,3>,<278598528,8,3>,<278598528,56,4>,<280348992,24,3>,<283668480,2,3>,<283668480,20,3>,<283668480,42,3>,<285805440,12,3>,<285805440,20,4>,<290678784,72,3>,<292234800,6,3>,<297561600,36,4>,<297932544,60,3>,<300585600,8,3>,<300810240,6,3>,<300810240,12,3>,<301916160,12,3>,<304128000,2,3>,<304128000,6,3>,<304128000,42,4>,<305516544,24,3>,<307607040,6,3>,<307607040,12,3>,<307607040,60,4>,<307777536,20,3>,<309060000,2,3>,<309553920,12,4>,<317011968,16,3>,<317534976,6,3>,<317534976,30,4>,<319334400,8,3>,<322043904,6,3>,<326764800,12,3>,<326764800,20,3>,<327398400,6,3>,<334342944,2,3>,<336047616,8,3>,<342835200,12,3>,<345945600,6,3>,<349685376,6,3>,<349857792,8,3>,<350429184,12,3>,<350429184,24,4>,<352665600,12,3>,<360448704,36,3>,<360972288,10,3>,<362299392,10,3>,<370596240,6,3>,<371464704,2,3>,<371464704,6,3>,<371464704,42,4>,<375037824,6,3>,<375037824,12,3>,<384721920,2,3>,<389529648,2,3>,<392878080,8,3>,<393590016,18,3>,<396748800,2,3>,<400780800,6,3>,<400780800,30,4>,<410370048,16,3>,<412080000,12,4>,<419554080,2,3>,<422682624,6,3>,<422682624,12,3>,<425779200,6,3>,<425779200,30,4>,<427198464,12,3>,<428544000,6,3>,<428708160,8,3>,<437322240,12,3>,<445790592,12,3>,<448063488,6,3>,<448063488,30,4>,<451215360,8,3>,<452874240,8,3>,<461410560,8,3>,<466477056,6,3>,<472780800,6,3>,<472780800,12,3>,<473776128,2,3>,<476302464,20,3>,<476342400,12,3>,<478690560,6,3>,<480598272,2,3>,<484775424,2,3>,<486604800,2,3>,<489554400,6,3>,<490147200,8,3>,<496235520,6,3>,<496235520,12,3>,<512962560,12,3>,<514252800,8,3>,<516420000,6,4>,<519372864,12,3>,<523837440,2,3>,<523837440,6,3>,<524786688,10,3>,<528998400,8,3>,<538610688,6,3>,<544608000,12,4>,<559405440,12,3>,<562556736,8,3>,<567336960,10,3>,<571610880,2,3>,<571610880,6,3>,<581357568,36,3>,<595123200,18,3>,<601171200,20,3>,<601620480,6,3>,<603678816,6,4>,<603832320,2,3>,<603832320,6,3>,<611033088,12,3>,<615214080,6,3>,<615214080,30,4>,<615555072,2,3>,<631701504,12,4>,<634023936,8,3>,<638426880,28,3>,<638668800,20,3>,<640797696,8,3>,<646367232,12,3>,<653529600,2,3>,<653529600,6,3>,<672095232,20,3>,<685670400,2,3>,<685670400,6,3>,<687412224,2,3>,<700858368,6,3>,<700858368,12,4>,<701554608,6,4>,<705331200,6,3>,<709171200,8,3>,<720897408,18,3>,<743178240,2,3>,<744353280,8,3>,<744629760,2,3>,<750075648,6,3>,<773111136,6,3>,<774240768,2,3>,<793837440,12,3>,<824160000,6,3>,<845365248,6,3>,<854396928,6,3>,<874644480,6,3>,<876704400,2,3>,<890537568,6,3>,<891581184,6,3>,<912384000,2,3>,<916549632,8,3>,<922821120,20,3>,<945561600,6,3>,<952604928,2,3>,<966131712,2,3>,<982195200,2,3>,<992471040,6,3>,<992839680,12,3>,<1001952000,12,4>,<1020858480,6,4>,<1025925120,6,3>,<1032321024,12,4>,<1034035200,6,3>,<1037836800,2,3>,<1038745728,6,3>,<1049056128,2,3>,<1051287552,8,3>,<1064448000,12,3>,<1067320800,6,4>,<1111788720,2,3>,<1114394112,2,3>,<1118810880,6,3>,<1120158720,12,3>,<1168939200,12,3>,<1202342400,2,3>,<1222066176,6,3>,<1263403008,6,3>,<1277337600,2,3>,<1285632000,2,3>,<1292734464,6,3>,<1323859200,6,3>,<1344190464,2,3>,<1380261888,6,3>,<1399431168,2,3>,<1401716736,6,4>,<1468663200,2,3>,<1498454496,6,4>,<1538035200,12,4>,<1549260000,2,3>,<1560319200,6,4>,<1571512320,2,3>,<1615832064,2,3>,<1714832640,2,3>,<1804861440,2,3>,<1811036448,2,3>,<1811496960,2,3>,<1845642240,2,3>,<1960588800,2,3>,<1985679360,6,3>,<2057011200,2,3>,<2064642048,6,3>,<2104663824,2,3>,<2115993600,2,3>,<2250226944,2,3>,<2319333408,2,3>,<2337878400,6,3>,<2536095744,2,3>,<2563190784,2,3>,<2623933440,2,4>,<2671612704,2,3>,<2836684800,2,3>,<2977413120,2,3>,<3062575440,2,3>,<3102105600,2,3>,<3201962400,2,3>,<3666198528,2,3>,<3971577600,2,3>,<4140785664,2,3>,<4205150208,2,3>,<4495363488,2,4>,<4680957600,2,3>];
gl2permreptab := AssociativeArray(); for r in gl2permrepdat do gl2permreptab[[r[1],r[2]]] := r[3]; end for;

/* Heuristic cutoffs, YMMV */
gl2enumcuts := [0,0,0,0,0,0,0,8,9,11, 13,14,15,16,17,18,19,20,21,22, 23,24,25,26,27,28,29,30,31,32];
gl2cccuts :=  [0,0,0,0,0,6,6,8,14,19, 20,23,25,26,27,28,29,30,31,32, 32,32,32,32,32,32,32,32,32,32];
gl2actcuts := [32,32,32,32,32,32,27,23,18,18, 17,17,16,16,15,15,14,13,12,11, 10,9,8,7,6,5,4,3,2,1];

function gl2permrepalg(H)
    if not assigned H`Order or not assigned H`Index then H`Index := GL2Index(H); end if;
    b,i := IsDefined(gl2permreptab,[H`Order,H`Index]); if b then return gl2permrepalgs[i]; end if;
    n := Max(1,Floor(Log(2,H`Index))); m := Max(1,Floor(Log(2,H`Order)));
    assert n le 32;
    if m le gl2enumcuts[n] then return "enum"; end if;
    if m le gl2cccuts[n] then return "cc"; end if;
    if m le gl2actcuts[n] then return "action"; end if;
    return "gl2action";
end function;

// We never use the action algorithm by default for SL2 subgroups (the user can specify it in contexts where it is konwn to work, e.g. intersections of full determinant groups with SL2).
function sl2permrepalg(H)
    assert H`SL; return "enum";
    if not assigned H`Order or not assigned H`Index then H`Index := SL2Index(H); end if;
    return H`Order le 2^18 select "enum" else "cc";
end function;

intrinsic GL2PermutationRepresentation(H::GrpMat:noCosetAction:=false) -> Map
{ Given a subgroup H of G:=GL(2,Z/NZ), returns the group homomoprhism from G to the symmetric group of degree [G:H] given by the action of G on the right cosets of H. }
    require not assigned H`SL: "H should be a subgroup of GL(2,Z/NZ) that is not marked as a subgroup of SL(2,Z/NZ).";
    N := #BaseRing(H); if not IsFinite(N) then assert H eq gl2N1; return map<H->Sym(1)|>; end if;
    if (not noCosetAction and IsPrime(N)) or GL2DeterminantIndex(H) gt 1 then return CosetAction(GL2Ambient(N),H); end if;
    M,SH := SL2Level(H);
    if (not noCosetAction and M eq N) then return CosetAction(GL2Ambient(N),H); end if;
    /*
        Proof that this algorithm works when H has full determinant (warning, it does not work in general, hence the check above!):

        (1) Any set of unique SL2-coset reps for (H cap SL2) is also a set of unique GL2-coset reps for H
        (2) For any h in H and a in GL2 we have Ha = Hha; in particular, by choosing a suitable h we can change the determinant of any coset rep without changing the coset
        (3) For any g,a,b in G and h in H, if Hag = Hb then Hhag = Hb; if we choose h with det(h) = det(g)^-1 then det(hag) = 1
            We can thus compute the action of g on the coset Ha using the SL2-coset map for (H cap SL2) to compute the unique SL2-coset rep b for (H cap SL2) for which Hb = Hhag.

        This seems blindingly obvious once it is spelled out, but I occasionally have to remind myself why it works.
        The reason it might not be obvious is that it implies that we can use the permutation given by [H\G] to efficiently compute the cardinality of the intersecion
        of (H cap SL2) with any GL2-conjugacy class in SL2 by computing #(g^G cap H) = #Fix(pi(g))*g^G / [G:H], where g is any GL2-conjugacy class rep in SL2
        (in other words, any similarity class rep with determinant one -- note that it is *much* easier to compute similarity class reps than it is to compute
        SL2-conjugacy class reps, and it is also easier to compute the perm rep [(H cap SL2)\SL2] than the perm rep [H\GL2], which is why this function is useful).

        But this is not true if we replace (H cap SL2) with an arbitrary subgroup K of SL2, it will only work when the cardinality of the intersection of K
        with any SL2-conjugacy class is invariant under GL2-conjugacy.  This is not true in general but it is (necessarily) true for K that arise as H cap SL2
        for some H with full determinant.  In general if we want to compute the cardinality of the intersection fo K < SL2 with some GL2-conjugacy class c
        we need to know SL2-conjugacy class reps for every SL2-conjugacy class contained in c and plug each of them into the perm rep.
    */
    T, rho := RightTransversal(SL2Ambient(M),SH); X := GL2DeterminantReps(H); G := GL2Ambient(N);
    f := GL2ElementLifter(M,N); _,pi := ChangeRing(G,Integers(M));
    return hom<G->S|[<g,perm(g)>:g in Generators(G)]> where perm := func<g|S![Index(T,rho(pi(X[Determinant(g)^-1]*f(t)*g))):t in T]> where S:=Sym(#T);
end intrinsic;

intrinsic SL2PermutationRepresentation(H::GrpMat) -> Map
{ Given a subgroup H of G:=GL(2,Z/NZ), returns the group homomoprhism from G to the symmetric group of degree [G:H] given by the action of G on the right cosets of H. }
    require assigned H`SL: "H should be a subgroup of SL(2,Z/NZ) that is marked as such (not just a subgroup of GL2 that happens to lie in SL2).";
    N := #BaseRing(H); if not IsFinite(N) then assert H eq gl2N1; return map<H->Sym(1)|>; end if;
    return rho where rho := CosetAction(SL2Ambient(N),H);
end intrinsic;

intrinsic SL2PermutationCharacter(H::GrpMat) -> Map
{ The permutation character of the subgroup H of SL2. }
    rho := SL2PermutationRepresentation(H);
    return func<g|#Fix(rho(g))>;
end intrinsic;

intrinsic GL2RightTransversal(H::GrpMat) -> SeqEnum[GrpMatElt]
{ Returns a list of right-coset reps of H in its ambient. }
    N := #BaseRing(H); if not IsFinite(N) then assert H eq gl2N1; return [Identity(H)]; end if;
    if N le 12 then return RightTransversal(GL2Ambient(N),H); end if;
    dindex := GL2DeterminantIndex(H);
    K := SL2Intersection(H);
    M,K := SL2Level(H);
    S := RightTransversal(SL2Ambient(M),K);
    S := [lift(h):h in S] where lift:=SL2ElementLifter(M,N);
    if dindex gt 1 then
        G := GL2Ambient(N);
        T := RightTransversal(GL1Ambient(N),GL2DeterminantImage(H));
        S := &cat[[h*G![t[1][1],0,0,1]:h in S]:t in T];
    end if;
    assert #S eq GL2Index(H);
    return S;
end intrinsic;

intrinsic SL2RightTransversal(H::GrpMat) -> SeqEnum[GrpMatElt]
{ Returns a list of right-coset repf of SL2-subgroup H inside its ambient; often faster than RightTransversal when level is large and index is small. }
    require assigned H`SL: "H should be a subgroup of SL(2,Z/NZ) that is marked as such (not just a subgroup of GL2 that happens to lie in SL2).";
    N := #BaseRing(H); if not IsFinite(N) then assert H eq gl2N1; return [Identity(H)]; end if;
    S := [SL(2,Integers(N))|Identity(H)];
    gens := Generators(SL2Ambient(N));
    n := SL2Index(H);
    V := {sub<RSpace(H)|[i,j]>:i in D,j in [0..N-1]} where D:=Divisors(N) where N := #BaseRing(H); X :={};
    while #V gt 0 do v := Random(V); W := v^H; Include(~X,W); V diff:= W; end while;
    M := {@ X @}; T := AssociativeArray(); T[1] := [S[1]]; I := [1];
    next := 1;
    while next le n do
        last := #S;
        for i:=next to last do
            h := S[i]; hm := M[I[i]];
            for g in gens do
                gm := hm^g;
                j := Index(M,gm);
                if j eq 0 then
                    Append(~S,h*g); Include(~M,gm); assert M[#M] eq gm; I[#S] := #M; T[#M] := [S[#S]];
                else
                    a := (h*g)^-1;
                    found  := false; for k in T[j] do if k*a in H then found := true; break; end if; end for;
                    if found then continue; end if;
                    Append(~S,h*g); I[#S] := j; Append(~T[j],S[#S]);
                end if;
                if #S eq n then break; end if;
            end for;
            if #S eq n then break; end if;
        end for;
        next := last+1;
    end while;
    return S;
end intrinsic;

intrinsic GL2PermutationCharacter(H::GrpMat:Algorithm:="default") -> UserProgram
{ The permutation character given by the GL2-action on the right coset space [H\\GL2].  The optional parameter Algorithm my be "action", "cc", or "default" (which will choose action or cc based on the index of H). }
    N := #BaseRing(H); if not IsFinite(N) then assert H eq gl2N1; return func<A|1>; end if;
    require Algorithm in gl2permrepalgs: "Invalid value for Algorithm use one of " cat sprint(gl2permrepalgs);
    if Algorithm eq "default" then Algorithm := gl2permrepalg(H); end if;
    if Algorithm eq "gl2action" then
            return func<g|#Fix(pi(g))> where pi := GL2PermutationRepresentation(H);
    elif Algorithm eq "action" then
            return func<g|#Fix(pi(g))> where pi := CosetAction(GL2Ambient(N),H);
    end if;
    if not assigned H`Index then H`Index := GL2Index(H); end if;
    /* By (2.1) in https://doi.org/10.19086/da.29452 we have chi_H(g) = #stab(g)/#H * #(orbit(g) cap H) = [G:H]*#(orbit(g) cap H)/#orbit(g) */
    C := GL2SimilarityCounts(N); CH := GL2SimilarityCounts(H:Algorithm:=Algorithm);
    Z := [(H`Index * CH[i]) div C[i]:i in [1..#C]];
    return func<g|Z[ind(g)]> where ind := GL2SimilarityClassIndexMap(N);
end intrinsic;

/*** GL2/SL2 invariants ***/

intrinsic GL2DeterminantImage(H::GrpMat) -> GrpMat
{ det(H) as a subgroup of GL1. }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    R := BaseRing(H);  if not IsFinite(R) then assert H eq gl2N1; return gl1N1; end if;
    return sub<GL(1,R)|[[Determinant(h)]:h in Generators(H)]>;
end intrinsic;

intrinsic GL2DeterminantReps(H::GrpMat) -> Assoc
{ Elements of H representing each element of det(H), indexed by determinant }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    R := BaseRing(H); if not IsFinite(R) then assert H eq gl2N1; return 1; end if;
    M,pi := MultiplicativeGroup(R); phi:=map<H->M|x:->Inverse(pi)(Determinant(x))>;
    n := #M div GL2DeterminantIndex(H);
    K := sub<M|>; S:=[Identity(H)]; m := 1;
    while #S lt n do
        x := Random(H); u := x; y:=phi(x); v := y;
        while not v in K do S cat:= [S[i]*u:i in [1..m]]; u *:= x; v +:= y; end while;
        m := #S; K := sub<M|K,y>;
    end while;
    assert #S eq n;
    assert #{Determinant(s):s in S} eq n;
    X := AssociativeArray(); for s in S do X[Determinant(s)] := s; end for;
    return X;
end intrinsic;

intrinsic GL2Scalars(H::GrpMat) -> GrpMat
{ For H a subgroup of GL2 returns the scalar subgroup of H, for H a subgroup of GL1 returns the corresponding scalar subgroup of GL2 }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    R := BaseRing(H);  if not IsFinite(R) then return gl2N1; end if;
    if Degree(H) eq 1 then return sub<GL(2,R)|[[g[1][1],0,0,g[1][1]]:g in Generators(H)]>; end if;
    return H meet sub<GL(2,R)|[[g[1][1],0,0,g[1][1]]:g in Generators(Z1)]> where Z1 := GL(1,R);
end intrinsic;

intrinsic GL2ScalarSubgroupGL1(H::GrpMat) -> GrpMat
{ Returns the subgroup of GL1 isomorphic to the scalar subgroup of H. }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    R := BaseRing(H);  if not IsFinite(R) then assert H eq gl2N1; return gl1N1; end if;
    Z1 := GL(1,R);
    Z := H meet sub<GL(2,R)|[[g[1][1],0,0,g[1][1]]:g in Generators(Z1)]>;
    return sub<Z1|[[g[1][1]]:g in Generators(Z)]>;
end intrinsic;

intrinsic GL2ScalarIndex(H::GrpMat) -> RngIntElt
{ The index of (H meet scalars) in H, where H is a subgroup of GL(2,R). }
    if not IsFinite(BaseRing(H)) then assert H eq gl2N1; return 1; end if;
    return GL1Index(GL2ScalarSubgroupGL1(H));
end intrinsic;

intrinsic GL2ContainsComplexConjugation(H::GrpMat:CH:=[]) -> BoolElt, GrpMatElt
{ True if H contains an element corresponding to complex conjugation (any GL2-conjugate of [1,0,0,-1] or [1,1,0,-1]). }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    R := BaseRing(H);  if not IsFinite(R) then assert H eq gl2N1; return true,Identity(gl2N1); end if;
    G := GL(2,R); N := #R;
    if #CH gt 0 then return CH[ind(G![1,1,0,-1])] gt 0 or CH[ind(G![1,0,0,-1])] gt 0 where ind := GL2SimilarityClassIndexMap(N); end if;
    if GL2Index(H) le 1024 then pi := GL2PermutationRepresentation(H); return #Fix(pi(G![1,0,0,-1])) gt 0 or #Fix(pi(G![1,1,0,-1])) gt 0; end if;
    cc := [[1,0,0,-1],[-1,0,0,1],[1,-1,0,-1],[1,1,0,-1],[-1,0,1,1],[-1,1,0,1],[-1,0,-1,1],[1,0,1,-1],[-1,-1,0,1],[1,0,-1,-1],[0,-1,-1,0],[0,1,1,0]];
    cc := [c:c in cc|G!c in H];
    if #cc gt 0 then return true,cc[1]; end if;
    if N ne 2 and not IsEven(#GL(1,R) div GL2DeterminantIndex(H)) then return false,_; end if;
    Z := Conjugates(G,G![1,0,0,-1]);
    for z in Z do if z in H then return true,z; end if; end for;
    if IsOdd(N) then return false; end if;
    Z := Conjugates(G,G![1,1,0,-1]);
    for z in Z do if z in H then return true,z; end if; end for;
    return false,_;
end intrinsic;

intrinsic GL2ContainsCC(H::GrpMat) -> BoolElt
{ True if H contains an element corresponding to complex conjugation (any GL_2-conjugate of [1,0,0,-1] or [1,1,0,-1]). }
    return GL2ContainsComplexConjugation(H);
end intrinsic;

intrinsic GL2ContainsNegativeOne(H::GrpMat) -> BoolElt, GrpMat
{ True if -I is in H, second parameter is H with the NegOne attribute set }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    if assigned H`NegOne then return H`NegOne, H; end if;
    H`NegOne := -Identity(H) in H;
    return H`NegOne, H;
end intrinsic;

intrinsic GL2QAdmissible(H::GrpMat:MustContainNegativeOne:=false) -> BoolElt
{ True if the specified subgroup of GL2(Z/NZ) has determinant index one and contains an element corresponding to complex conjugation (these are preconditions to having Q-rational points). }
    if not IsFinite(BaseRing(H)) then assert H eq gl2N1; return true; end if;
    return (not MustContainNegativeOne or GL2ContainsNegativeOne(H)) and (GL2DeterminantIndex(H) eq 1) and GL2ContainsComplexConjugation(H);
end intrinsic;

intrinsic GL2IncludeNegativeOne(H::GrpMat) -> GrpMat
{ returns <H,-I>; (propogates Order if set) }
    // require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2.";
    if assigned H`SL then return SL2IncludeNegativeOne(H); end if;
    if not IsFinite(BaseRing(H)) then assert H eq gl2N1; H`NegOne:=true; return H; end if;
    if assigned H`NegOne and H`NegOne then return H; end if;
    nI := -Identity(H);
    if nI in H then H`NegOne := true; return H; end if;
    R := BaseRing(H); if #R eq 2 then HH := sub<GL(2,R)|H>; HH`NegOne := true; return HH; end if;
    HH := sub<GL(2,R)|H,nI>; HH`NegOne := true;
    if assigned H`Order then HH`Order := 2*H`Order; end if;
    return HH;
end intrinsic;

intrinsic SL2ContainsNegativeOne(H::GrpMat) -> BoolElt, GrpMat
{ True if -I is in H, second parameter is H with the NegOne attribute set }
    require assigned H`SL: "H should be a subgroup of SL2 that is marked as a subgroup of SL2.";
    if assigned H`NegOne then return H`NegOne, H; end if;
    H`NegOne := -Identity(H) in H;
    return H`NegOne, H;
end intrinsic;

intrinsic SL2IncludeNegativeOne(H::GrpMat) -> GrpMat
{ returns <H,-I>; (propogates Order if set) }
    require assigned H`SL: "H should be a subgroup of SL2 that is marked as a subgroup of SL2.";
    if not IsFinite(BaseRing(H)) then assert H eq sl2N1; H`NegOne:=true; return H; end if;
    if assigned H`NegOne and H`NegOne then return H; end if;
    nI := -Identity(H);
    if not assigned H`NegOne and nI in H then H`NegOne := true; return H; end if;
    R := BaseRing(H); if #R eq 2 then HH := sub<SL(2,R)|H>; HH`SL := true; HH`NegOne := true; return HH; end if;
    HH := sub<SL(2,R)|H,nI>; HH`SL := true; HH`NegOne := true;
    if assigned H`Order then HH`Order := 2*H`Order; end if;
    return HH;
end intrinsic;

intrinsic GL2CommutatorSubgroup(H::GrpMat) -> GrpMat
{ returns the commutator subgroup K = [H,H], where H is viewed as the open subgroup of GL2(Zhat) given by the inverse image of the input H in GL(2,Z/NZ).  The group K is a subgroup of SL(2,Z/MZ) where M is the level of [H,H] as an open subgroup of SL2(Zhat).  Note: K will typically not be equal to the commutator subgroup of H as a subgroup of GL(2,Z/NZ), and M may be divislbe by primes that do not divide N (in particular, M is always even). }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2";
    N,H := GL2Level(H);
    if N eq 1 then return K where _,K:=SL2Level(sub<SL(2,Integers(2))|[0,1,1,1]>); end if;
    if N mod 4 ne 0 then N *:= 2^(2-Valuation(N,2)); end if;
    A := Factorization(N);
    com := func<H|CommutatorSubgroup(H)>;
    for a in A do p := a[1]; e := a[2]; while SL2Index(com(GL2ProjectKernel(H,p^e))) lt SL2Index(com(GL2ProjectKernel(H,p^(e+1)))) do e +:= 1; N *:= p; end while; end for;
    _,K := SL2Level(com(GL2Lift(H,N)));
    return K;
end intrinsic;

intrinsic GL2IsAgreeable(H::GrpMat) -> BoolElt
{ Returns true if H is agreeable (determininant index 1, scalar index 1, GL2Level and SL2Level supported on the same odd primes). }
    return GL2DeterminantIndex(H) eq 1 and GL2ScalarIndex(H) eq 1 and Set(PrimeDivisors(GL2Level(H))) join {2} eq Set(PrimeDivisors(SL2Level(H))) join {2};
end intrinsic;

intrinsic GL2AgreeableClosure(H::GrpMat) -> GrpMat
{ Returns the agreeable closure of H (the smallest agreeable subgroup of GL(2,Zhat) that contains H). }
    NN,H := GL2Level(H);
    if NN eq 1 then return H; end if;
    M := &*[ZZ|p^Valuation(NN,p):p in PrimeDivisors(N)] where N:=SL2Level(GL2CommutatorSubgroup(H));
    H := ChangeRing(H,Integers(M));
    return GL2ScalarIndex(H) eq 1 select H else sub<GL2Ambient(M)|H,GL2Scalars(M)>;
end intrinsic;

intrinsic GL2AgreeableQuotient(H::GrpMat) -> GrpAb
{ Returns the quotient of the agreeable closure of H by H, as an abelian group. }
    N,H := GL2Level(H);
    return AbelianGroup(quo<GL2Lift(GL2AgreeableClosure(H),N)|H>);
end intrinsic;

intrinsic GL2AgreeableQuotientInvariants(H::GrpMat) -> SeqEnum[RngIntElt]
{ Returns the quotient of the agreeable closure of H by H, as an abelian group. }
    return Invariants(GL2AgreeableQuotient(H));
end intrinsic;

intrinsic GL2CuspOrbits(H::GrpMat:slow:=false,CH:=[]) -> RngIntElt
{ Returns a sorted list of pairs [n,m] where m is the number of Galois orbits of cusps of size n. }
    N,H := GL2Level(GL2IncludeNegativeOne(H));
    if N eq 1 then return [[1,1]]; end if;
    GL2 := GL2Ambient(N);
    if IsPrime(N) and GL2DeterminantIndex(H) eq 1 and not slow then
        // For prime N and n properly dividing phi(N), the matrices T^a*d^n are all conjugate, allowing us to apply the optimization used in GL2RationalCuspCount,
        // and we can handle d^n=1 but just counting cusps not in any of the orbits already counted (they must lie in cusp orbits of maximal size phi(N))
        d := GL2Ambient(N)![PrimitiveRoot(N),0,0,1]; m := EulerPhi(N); c:=AssociativeArray(); D := [e:e in Divisors(m)|e lt m];
        if #CH eq 0 then CH := GL2SimilarityCounts(H); end if; ind := GL2SimilarityClassIndexMap(N);
        for e in D do c[e] := ExactQuotient(CH[ind(d^e)]*GL2Index(H),n) where n:=GL2SimilarityClassSize(d^e); end for;
        C := [[e,ExactQuotient(&+[MoebiusMu(e div f)*c[f]:f in Divisors(e)],e)]:e in D]; C := [a:a in C|a[2] gt 0];
        n := GL2CuspCount(H) - &+[ZZ|a[1]*a[2]:a in C];  assert n ge 0;
        if n gt 0 then Append(~C,[m,ExactQuotient(n,m)]); end if;
        return C;
    end if;
    if PrimitiveRoot(N) gt 0 and not slow then
        d := GL2Ambient(N)![PrimitiveRoot(N),0,0,1]; m := EulerPhi(N); c:=AssociativeArray(); D := [e:e in Divisors(m)|e lt m];
        idx := GL2Index(H); C := GL2SimilarityCounts(N); if #CH eq 0 then CH := GL2SimilarityCounts(H); end if; ind := GL2SimilarityClassIndexMap(N);
        for e in D do c[e] := ExactQuotient(&+[ExactQuotient(idx*CH[i],C[i]) where i:=ind(dd*GL2![1,n,0,1]) : n in [1..N]],N) where dd:=d^e; end for;
        C := [[e,ExactQuotient(&+[MoebiusMu(e div f)*c[f]:f in Divisors(e)],e)]:e in D]; C := [a:a in C|a[2] gt 0];
        n := GL2CuspCount(H) - &+[ZZ|a[1]*a[2]:a in C];  assert n ge 0;
        if n gt 0 then Append(~C,[m,ExactQuotient(n,m)]); end if;
        return C;
    end if;
    pi := CosetAction(GL2,H); O := Orbits(pi(sub<GL2|[1,1,0,1]>));
    B := pi(sub<GL2|[[g[1][1],0,0,1]:g in Generators(GL1)]>) where GL1 := GL1Ambient(N);
    S := Set(O); M:={**};
    while not IsEmpty(S) do o := Random(S); oo := o^B; Include(~M,#oo); S diff:= Set(oo); end while;
    return [[a[1],a[2]]:a in Sort(Eltseq(M))];
end intrinsic;

intrinsic GL2CuspCountSlow(H::GrpMat) -> RngIntElt
{ The number of cusps of X_H over C = GL2DeterminantIndex(H) * #PSL2-orbits of H under the action of [1,1,0,1]. }
    di := GL2DeterminantIndex(H);
    N,H := SL2Level(GL2IncludeNegativeOne(H));
    if N eq 1 then return di; end if;
    SL2 := SL2Ambient(N);
    pi := CosetAction(SL2,H);
    T:=sub<SL2|[1,1,0,1]>;
    return di*#Orbits(pi(T));
end intrinsic;

intrinsic GL2CuspCount(H::GrpMat) -> RngIntElt
{ The number of cusps of X_H over C = GL2DeterminantIndex(H) * #PSL2-orbits of H under the action of [1,1,0,1]. }
    di := GL2DeterminantIndex(H);
    N,H := SL2Level(GL2IncludeNegativeOne(H));
    if N eq 1 then return di; end if;
    SL2 := SL2Ambient(N);
    CH := SL2SimilarityCounts(H); C:=SL2SimilarityCounts(N); ind := SL2SimilarityClassIndexMap(N);
    D := Divisors(N); g := SL2![1,1,0,1]; fix := [];
    for d in D do fix[d] := (H`Index*CH[i]) div C[i] where i:=ind(g^d); end for;        // fix[d] = [SL2/H]^(g^d) = # fix points of any h in <g> of order N/d
    return di*ExactQuotient(&+[EulerPhi(d)*fix[N div d]:d in D],N); // Apply Burnside to the phi(d) elements have order d|N
end intrinsic;

intrinsic GL2RationalCuspCount(H::GrpMat:slow:=false,CH:=[]) -> RngIntElt
{ The number of Q-rational cusps of X_H. }
    N,H := GL2Level(GL2IncludeNegativeOne(H));
    if N eq 1 then return 1; end if;
    GL2 := GL2Ambient(N);
    if IsOdd(N) and IsPrimePower(N) and not slow then
        /*
            In this situation (Z/NZ)* is cyclic, generated by a primitive root r, and if we put d:=[r,0,0,1] and T:=[1,1,0,1], a coset orbit Hg,HgT,...,HgT^k
            is d-stable if and only if the g-conjugate of T^a*d*T^b lies in H.  But the matrices T^a*d*T^b are all GL2-conjugate to d (here we need (d-1)
            to be coprime to N, which works for N odd and d a primitive root but not in general),  The problem then reduces to counting cosets fixed by d,
            which we compute using chi_H(d) = #(d^G meet H)*[G:H]/#d^G
        */
        return ExactQuotient(GL2SimilarityCount(H,d)*GL2Index(H),n) where n:=GL2SimilarityClassSize(d) where d:=GL2Ambient(N)![PrimitiveRoot(N),0,0,1];
    end if;
    if PrimitiveRoot(N) gt 0 and not slow then
        idx := GL2Index(H); C := GL2SimilarityCounts(N); if #CH eq 0 then CH := GL2SimilarityCounts(H); end if; ind := GL2SimilarityClassIndexMap(N); d:=GL2![PrimitiveRoot(N),0,0,1];
        return ExactQuotient(&+[ExactQuotient(idx*CH[i],C[i]) where i:=ind(d*GL2![1,n,0,1]) : n in [1..N]],N);
    end if;
    pi := CosetAction(GL2,H); O := Orbits(pi(sub<GL2|[1,1,0,1]>));
    gg := [pi(GL2![g[1][1],0,0,1]):g in Generators(GL1)] where GL1:=GL1Ambient(N);
    return #[o:o in O|&and[o^g eq o:g in gg]];
end intrinsic;

intrinsic GL2RationalCuspCount(H::GrpMat, q::RngIntElt:slow:=false,CH:=[]) -> RngIntElt
{ The number of Fq-rational cusps of the reduction of X_H to the finite field F_q (where q is coprime to the level of H). }
    N,H := GL2Level(GL2IncludeNegativeOne(H));
    if N eq 1 then return 1; end if;
    require GCD(q,N) eq 1: "q must be coprime to the level of H.";
    if q mod N eq 1 and GL2DeterminantIndex(H) eq 1 then return GL2CuspCount(H); end if;
    GL2 := GL2Ambient(N);  d := GL2![q,0,0,1];
    if slow then return #[o:o in O|o^s eq o] where s:=pi(d) where O:=Orbits(pi(K)) where K:=sub<GL2|[1,1,0,1]> where pi:=CosetAction(GL2,H); end if;
    if IsPrime(N) then return ExactQuotient(GL2SimilarityCount(H,d)*GL2Index(H),GL2SimilarityClassSize(d)); end if;
    if IsOdd(N) and IsPrimePower(N) then
        b,p,a := IsPrimePower(Order(d));
        if not b or N mod p ne 0 then return ExactQuotient(GL2SimilarityCount(H,d)*GL2Index(H),GL2SimilarityClassSize(d)); end if;
        idx := GL2Index(H); m := EulerPhi(N); e := Valuation(N,p)-a;
        C := GL2SimilarityCounts(N); if #CH eq 0 then CH := GL2SimilarityCounts(H); end if; ind := GL2SimilarityClassIndexMap(N);
        return &+[ExactQuotient(idx*CH[i]*(m div (p^j - (j eq e select p^(j-1) else 0))),C[i]*N) where i:=ind(d*GL2![1,p^j,0,1]) : j in [0..e]];
    end if;
    idx := GL2Index(H); C := GL2SimilarityCounts(N); CH := GL2SimilarityCounts(H); ind := GL2SimilarityClassIndexMap(N);
    return ExactQuotient(&+[ExactQuotient(idx*CH[i],C[i]) where i:=ind(d*GL2![1,n,0,1]) : n in [1..N]],N);
end intrinsic;

intrinsic GL2RationalCuspCounts(H::GrpMat:slow:=false, CH:=[]) -> SeqEnum[RngIntElt]
{ Returns an array integers whose (q mod N)th entry is the number of rational cusps of X_H mod q for q coprime to N=level(H) and -1 otherwise. }
    N,H := GL2Level(GL2IncludeNegativeOne(H));
    if N eq 1 then return [1]; end if;
    GL2 := GL2Ambient(N);
    c := [-1:q in [1..N]]; R:=Integers(N);
    for q in [2..N-1] do
        if c[q] eq -1 and GCD(q,N) eq 1 then c[q]:=q; a:=R!q; m:=Order(a); b:=a; for i in [2..m-1] do b*:=a; if GCD(i,m) eq 1 then c[ZZ!b]:=q; end if; end for; end if;
    end for;
    S := IndexFibers([q:q in [2..N-1]|c[q] gt 0],func<q|c[q]>);
    if slow then
        pi := CosetAction(GL2,H);
        O := Orbits(pi(sub<GL2|[1,1,0,1]>));  c[1] := #O;
        for k in Keys(S) do c[k] := #[o:o in O|o^a eq o] where a := pi(GL2![k,0,0,1]); end for;
    else
        idx := GL2Index(H); C := GL2SimilarityCounts(N); if #CH eq 0 then CH := GL2SimilarityCounts(H); end if; ind := GL2SimilarityClassIndexMap(N); c[1] := GL2CuspCount(H);
        if IsPrime(N) then
            for k in Keys(S) do c[k] := ExactQuotient(idx*CH[i],C[i]) where i:=ind(GL2![k,0,0,1]); end for;
        elif IsOdd(N) and IsPrimePower(N) then
            m := EulerPhi(N);
            for k in Keys(S) do d := GL2![k,0,0,1]; b,p,a := IsPrimePower(Order(d));
                if not b or N mod p ne 0 then c[k] := ExactQuotient(idx*CH[ind(d)],C[ind(d)]); continue; end if;
                c[k] := &+[ZZ|ExactQuotient(idx*CH[i]*(m div (p^j - (j eq e select p^(j-1) else 0))),C[i]*N) where i:=ind(d*GL2![1,p^j,0,1]) : j in [0..e]] where e := Valuation(N,p)-a;
            end for;
        else
            for k in Keys(S) do d := GL2![k,0,0,1]; c[k] :=  ExactQuotient(&+[ExactQuotient(idx*CH[i],C[i]) where i:=ind(d*GL2![1,n,0,1]) : n in [1..N]],N); end for;
        end if;
    end if;
    for k in Keys(S) do for q in S[k] do c[q] := c[k]; end for; end for;
    return c;
end intrinsic;

intrinsic GL2CuspWidths(H::GrpMat:slow:=false) -> SeqEnum[SeqEnum[RngIntElt]]
{ Returns a list of pairs of integers [w,n] where n is the number of cusps of width w. }
    N,H := SL2Level(GL2IncludeNegativeOne(H));
    if N eq 1 then return 1; end if;
    SL2 := SL2Ambient(N);
    if slow then return [[r[1],r[2]]:r in Eltseq({*#o:o in oo*})] where oo := Orbits(pi(sub<SL2|[1,1,0,1]>)) where pi := CosetAction(SL2,H); end if;
    CH := SL2SimilarityCounts(H); C:=SL2SimilarityCounts(N); ind := SL2SimilarityClassIndexMap(N);
    D := Divisors(N); fix := []; g := SL2![1,1,0,1];
    for d in D do fix[d] := (H`Index*CH[i]) div C[i] where i:=ind(g^d); end for;  // fix[d] = [SL2/H]^(g^d) = # fix points of any h in <g> of order N/d
    F := [&+[MoebiusMu(e)*fix[d div e]:e in Divisors(d)] div d : d in D];         // F[d] = # g-orbits of size d = (# points fixed by g^d but not g^e for any e|d) / d
    return [[D[i],F[i]]:i in [1..#D]|F[i] gt 0];
end intrinsic;

intrinsic GL2EllipticPoints(H::GrpMat:slow:=false) -> RngIntElt, RngIntElt
{ Returns the number of elliptic points of order 2 and 3 for the congruence subgroup corresponding to H. }
    N,H := SL2Level(GL2IncludeNegativeOne(H));
    if N eq 1 then return 1,1; end if;
    SL2 := SL2Ambient(N);
    if slow then return #Fix(pi(SL2![0,1,-1,0])), #Fix(pi(SL2![0,1,-1,-1])) where pi:=CosetAction(SL2,H); end if;
    CH := SL2SimilarityCounts(H); C:=SL2SimilarityCounts(N); ind := SL2SimilarityClassIndexMap(N);
    n2 := (H`Index*CH[i]) div C[i] where i:=ind(SL2![0,1,-1,0]);
    n3 := (H`Index*CH[i]) div C[i] where i:=ind(SL2![0,1,-1,-1]);
    return n2,n3;
end intrinsic;

intrinsic GL2Genus(H::GrpMat:NoGenusData:=false,slow:=false) -> RngIntElt, SeqEnum[RngIntElt], SeqEnum[SeqEnum[RngIntElt]], GrpMat
{ The genus of the modular curve X_H along with the data used to computed it, unless NoGenusData is set, then only the genus is returned. The second return value is the sequence of integers [i,n2,n3,c,N], where i is the index in PSL(2,Z), n2, and n3 count elliptic points of order 2 and 3, c is the number of cusps,
  and N is the PSL2level of H (we then g = 1 + i/12 - n2/4 - n3/3 - c/2).  The third return value is the multiset of cusp widths w encoded as a list of pairs [w,n_w] where n_w is the number of cusps of width w.
  The fourth return values is the intersection of <H,-I> with SL2 reduced to level N.  This function will set H`Genus on return.  If H`Genus is already set on input it will be recomputed if GenusData is true. }
    if NoGenusData and assigned H`Genus then return H`Genus; end if;
    N,SH := SL2Level(GL2IncludeNegativeOne(H));
    if N eq 1 then return 0, [1,1,1,1,1], [[1,1]], SH; end if;
    SL2 := SL2Ambient(N);
    if slow then
        pi := CosetAction(SL2,SH); n2 := #Fix(pi(SL2![0,1,-1,0])); n3 := #Fix(pi(SL2![0,1,-1,-1]));
        oo := Orbits(pi(sub<SL2|[1,1,0,1]>)); c := #oo; w := [[r[1],r[2]]:r in Eltseq({*#o:o in oo*})];
    else
        CH := SL2SimilarityCounts(SH); C:=SL2SimilarityCounts(N); ind := SL2SimilarityClassIndexMap(N);
        n2 := (SH`Index*CH[i]) div C[i] where i:=ind(SL2![0,1,-1,0]);  
        n3 := (SH`Index*CH[i]) div C[i] where i:=ind(SL2![0,1,-1,-1]);
        D := Divisors(N); I := AssociativeArray(D); g := SL2![1,1,0,1];
        for d in D do I[d] := (SH`Index*CH[i]) div C[i] where i:=ind(g^d); end for;
        F := [&+[MoebiusMu(e)*I[d div e]:e in Divisors(d)] div d : d in D];
        c := &+F; w := [[D[i],F[i]]:i in [1..#D]|F[i] gt 0];
    end if;
    g := Integers()!(1 + SH`Index/12 - n2/4  - n3/3 - c/2);
    SH`Genus := g; H`Genus := g;
    if NoGenusData then return g; end if;
    return g, [SH`Index,n2,n3,c,N], w, SH;
end intrinsic;

intrinsic SL2Genus(H::GrpMat) -> RngIntElt, SeqEnum[RngIntElt], SeqEnum[SeqEnum[RngIntElt]], GrpMat
{ The genus of the modular curve X_H along with the data used to computed it [i,n2,n3,c,N] where i is the index in PSL(2,Z), n2, and n3 count elliptic points of order 2 and 3, c is the number of cusps, so g = 1 + i/12 - n2/4 - n3/3 - c/2, M is the SL2-level of H, N is its PSL2-level, followed by the multiset of cusp widths and the intersection of <H,-I> with SL2 at level N. }
    return GL2Genus(H);
end intrinsic;

/*** GL2 standard subgroups ***/

intrinsic GL2CartanSize(D::RngIntElt, N::RngIntElt) -> RngIntElt
{ The cardinality of (O/NO)* where O is the imaginary quadratic order of discriminant D. }
    return (N div &*P)^2 * &*[(p-1)*(p-KroneckerSymbol(D,p)):p in P] where P := PrimeDivisors(N);
end intrinsic;

// Based on Theorem 1.1 in Lozano-Robledo https://arxiv.org/abs/1809.02584
// TODO: speed this up, it takes 40 seconds for N ~ 1000
intrinsic GL2Cartan(D::RngIntElt,N::RngIntElt) -> GrpMat
{ The Cartan subgroup of GL(2,Z/NZ) isomorphic to (O/NO)* where O is the imaginary quadratic order of discriminant D. }
    require N gt 0: "N must be a positive integer";
    if N eq 1 then return gl2N1; end if;
    require D lt 0 and IsDiscriminant(D): "D must be the discriminant of an imaginary quadartic order";
    R := Integers(N); G := GL(2,R);
    DK := FundamentalDiscriminant(D); _,f := IsSquare(D div DK);
    if D mod 4 eq 0 then
        delta := D mod 4 eq 0 select R!ExactQuotient(D,4) else R!D/4; phi := R!0;
    else
        delta := R!((D-f^2) div 4);  phi := R!f;
    end if;
    m := GL2CartanSize(D,N); gens := []; H := sub<G|>;
    repeat
        repeat a := Random(R); b := Random(R); until GCD(a^2+a*b*phi-delta*b^2,N) eq 1;
        g := G![a+b*phi,b,delta*b,a];
        if not g in H then Append(~gens,G![a+b*phi,b,delta*b,a]); H := sub<G|gens>; end if;
    until #H eq m;
    C := sub<G|[Inverse(pi)(h):h in B]> where B:=AbelianBasis(A) where A,pi := AbelianGroup(H);
    C`Order := m; C`Index := GL2Size(N) div C`Order; C`Level := N; C`NegOne := true;
    return C;
end intrinsic;

intrinsic GL2CartanNormalizer(D::RngIntElt,N::RngIntElt) -> GrpMat
{ The projection of the Cartan normalizer for D to  GL(2,Z/NZ), contains an index-2 subgroup isomorphic to (OK/N*OK)* where OK is the imaginary quadratic order of discriminant D. }
    if N eq 1 then return gl2N1; end if;
    C := GL2Cartan(D,N);  G := GL2Ambient(N);
    if D mod 4 eq 0 then phi:=0; else _,phi := IsSquare(D div FundamentalDiscriminant(D)); end if;
    CN := sub<G|C,G![-1,0,phi,1]>; assert #CN eq (N eq 2 and phi eq 0 select C`Order else 2*C`Order); CN`Order := N eq 2 and phi eq 0 select C`Order else 2*C`Order; CN`Index := G`Order div CN`Order; CN`Level := N; CN`NegOne := true;
    return CN;
end intrinsic;

intrinsic GL2Scalars(R::RngIntRes) -> GrpMat
{ The subgroup of scalar matrices in GL(2,R). }
    m,pi := MultiplicativeGroup(R); gm := [pi(g):g in Generators(m)];
    Z := sub<GL(2,R) | [[g,0,0,g] : g in gm]>;
    N := #R; Z`Order := EulerPhi(N); Z`Index := GL2Size(N) div Z`Order; Z`Level := N; Z`NegOne := true;
    return Z;
end intrinsic;

intrinsic GL2Scalars(N::RngIntElt) -> GrpMat
{ The subgroup of scalar matrices in GL(2,Z/NZ). }
    return N eq 1 select gl2N1 else GL2Scalars(Integers(N));
end intrinsic;

intrinsic GL2SplitCartan1(R::Rng) -> GrpMat
{ The subgroup of diagonal matrices in GL(2,R) with a 1 in the upper left. }
    M,pi := MultiplicativeGroup(R);
    gens := [Integers()!pi(g):g in Generators(M)];
    return sub<GL(2,R) | [[1,0,0,g] : g in gens]>;
end intrinsic;

intrinsic GL2SplitCartan1(N::RngIntElt) -> GrpMat
{ The subgroup of diagonal matrices in GL(2,R) with a 1 in the upper left. }
    require N gt 0: "N must be positive";
    return N gt 1 select GL2SplitCartan1(Integers(N)) else sub<GL(2,Integers())|>;
end intrinsic;

intrinsic GL2SplitCartan(R::RngIntRes) -> GrpMat
{ The standard split Cartan subgroup of GL(2,R) consisting of diagonal matrices. }
    m,pi := MultiplicativeGroup(R); gm := [pi(g):g in Generators(m)];
    C := sub<GL(2,R) | [[g,0,0,1] : g in gm], [[1,0,0,g] : g in gm]>;
    N := #R; C`Order := EulerPhi(N)^2; C`Index := GL2Size(N) div C`Order; C`Level := N; C`NegOne := true;
    return C;
end intrinsic;

intrinsic GL2SplitCartan(N::RngIntElt) -> GrpMat
{ The standard split Cartan subgroup of GL(2,Z/NZ) consisting of diagonal matrices. }
    return N eq 1 select gl2N1 else GL2SplitCartan(Integers(N));
end intrinsic;

intrinsic GL2SplitCartan1(R::RngIntRes) -> GrpMat
{ The subgroup of the standard split Cartan subgroup of GL(2,R) consisting of diagonal matrices with a 1 in the upper left. }
    m,pi := MultiplicativeGroup(R); gm := [pi(g):g in Generators(m)];
    C := sub<GL(2,R) | [[1,0,0,g] : g in gm]>;
    N := #R; C`Order := EulerPhi(N); C`Index := GL2Size(N) div C`Order; C`Level := N; C`NegOne := false;
    return C;
end intrinsic;

intrinsic GL2SplitCartan1(N::RngIntElt) -> GrpMat
{ The standard split Cartan subgroup of GL(2,Z/NZ) consisting of diagonal matrices. }
    return N eq 1 select gl2N1 else GL2SplitCartan1(Integers(N));
end intrinsic;

intrinsic GL2SplitCartanNormalizer(R::RngIntRes) -> GrpMat
{ The normalizer of the (algebraic) split Cartan reduced modulo N (this group contains the split Cartan with index 2 and is equal to the normalizer in GL(2,Z/NZ) only when N is a prime power). }
    C := GL2SplitCartan(R);
    NC := sub<GL(2,R)|C,[0,1,1,0]>; NC`Level := C`Level; NC`Order := 2*C`Order; NC`Index := C`Index div 2; NC`NegOne := true;
    return NC;
end intrinsic;

intrinsic GL2SplitCartanNormalizer(N::RngIntElt) -> GrpMat
{ The normalizer of the (algebraic) split Cartan reduced modulo N (this group contains the split Cartan with index 2 and is equal to the normalizer in GL(2,Z/NZ) only when N is a prime power). }
    return N eq 1 select gl2N1 else GL2SplitCartanNormalizer(Integers(N));
end intrinsic;

intrinsic GL2SplitCartanFullNormalizer(N::RngIntElt) -> GrpMat
{ The normalizer in GL2(Z/NZ) of the reduction of the split Cartan, properly contains GL2SplitCartanNormalizer when #R is not prime. }
    if N le 2 then return gl2N1; end if;
    return H where _,H := GL2Level(Normalizer(GL2Ambient(N),GL2SplitCartan(N)));
end intrinsic;

// Non-split Cartan -- isomorphic to (OK/N*OK)* where OK is a quadratic order of discriminant prime to N with every p|N inert in OK
// See Baran https://core.ac.uk/download/pdf/82651427.pdf for details
intrinsic GL2NonsplitCartan(N::RngIntElt) -> GrpMat
{ A non-split Cartan subgroup of GL(2,Z/NZ) (isomorphic to OK/N*OK where OK is a quadratic order of discriminant prime to N with every p|N inert in OK). }
    if N eq 1 then return gl2N1; end if;
    G := GL2Ambient(N);
    if IsOdd(N) and IsPrime(N) then // optimization for prime level
        r:=PrimitiveRoot(N);
        while true do x := Random(1,N-1); y := Random(1,N-1); if Order(G![x,r*y,y,x]) eq N^2-1 then break; end if; end while;
        C := sub<G|[x,r*y,y,x]>; C`Level := N; C`Order := N^2-1; C`Index := N*(N-1); C`NegOne:= true;
        return C;
    end if;
    P := PrimeDivisors(N);
    D := -3;  while not (IsFundamentalDiscriminant(D) and &and[KroneckerSymbol(D,p) eq -1 : p in P]) do D -:= 4; end while;
    return GL2Cartan(D,N);
end intrinsic;

intrinsic GL2NonsplitCartanNormalizer(N::RngIntElt) -> GrpMat
{ The normalizer of the (algebraic) non-split Cartan reduced modulo N (this group contains the non-split Cartan with index 2 and is equal to the normalizer in GL(2,Z/NZ) only when N is a prime power). }
    if N le 2 then return gl2N1; end if;
    if IsOdd(N) and IsPrime(N) then
        C := GL2SplitCartan(N);
        NC := sub<GL(2,Integers(N))|C,[1,0,0,-1]>; NC`Order := 2*C`Order; NC`Index := C`Index div 2; NC`NegOne := true;
        NC`Level := N gt 2 select N else 1;
    end if;
    P := PrimeDivisors(N);
    D := -3;  while not (IsFundamentalDiscriminant(D) and &and[KroneckerSymbol(D,p) eq -1 : p in P]) do D -:= 4; end while;
    return GL2CartanNormalizer(D,N);
end intrinsic;

intrinsic GL2NonsplitCartanFullNormalizer(N::RngIntElt) -> GrpMat
{ The normalizer in GL2(Z/NZ) of the reduction of the Nonsplit Cartan, properly contains GL2NonplitCartanNormalizer when N is not prime. }
    if N le 2 then return gl2N1; end if;
    return H where _,H := GL2Level(Normalizer(GL2Ambient(N),GL2NonsplitCartan(N)));
end intrinsic;

intrinsic GL2Borel(R::Rng) -> GrpMat
{ The standard Borel subgroup of GL(2,R) consisting of upper triangular matrices. }
    m,pi := MultiplicativeGroup(R); gm := [pi(g): g in Generators(m)];
    B := sub<GL(2,R) | [[g,0,0,1] : g in gm], [[1,0,0,g] : g in gm], [1,1,0,1]>;
    N := #R; B`Level := N; B`Order := GL2BorelSize(N); B`Index := GL2Size(N) div B`Order; B`NegOne := true;
    return B;
end intrinsic;

intrinsic GL2Borel(N::RngIntElt) -> GrpMat
{ The standard Borel subgroup of GL(2,Z/NZ) consisting of upper triangular matrices. }
    return N eq 1 select gl2N1 else GL2Borel(Integers(N));
end intrinsic;

intrinsic GL2BorelPC(R::Rng) -> GrpMat, GrpPC, HomGrp
{ The standard Borel subgroup B of GL(2,R) consisting of upper triangular matrices along with a polycyclic presentation P of B and an isomorphism B -> P. }
    N := Characteristic(R);
    require N gt 0 and IsCommutative(R): "R must be a commutative ring of positive characteristic.";
    m,pi :=MultiplicativeGroup(R);
    gg := [g:g in Generators(m)]; n := 2*#gg+1;
    F := FreeGroup(n);
    rels1 := [F.i^Order(gg[i]):i in [1..#gg]];
    rels2 := [F.(#gg+i)^Order(gg[i]):i in [1..#gg]];
    rels3 := [F.n^N];
    rels4 := [F.n^F.i=F.n^(Integers()!pi(-gg[i])):i in [1..#gg]];
    rels5 := [F.n^F.(#gg+i)=F.n^(Integers()!pi(gg[i])):i in [1..#gg]];
    G := sub<GL(2,R)|[[pi(g),0,0,1]:g in gg] cat [[1,0,0,pi(g)]:g in gg] cat [[1,1,0,1]]>;
    GPC := quo<GrpGPC: F | rels1, rels2, rels3, rels4, rels5>;
    P,GPCpi := PCGroup(GPC);
    // help Magma compute the iso G->P by manually handling the non-abelian part
    D := sub<GL(2,R)|[[pi(g),0,0,1]:g in gg] cat [[1,0,0,pi(g)]:g in gg]>;
    Dpi := hom<D->P|[GPCpi(GPC.i):i in [1..n-1]]>;
    return G,P,func<g|Dpi(D![g[1][1],0,0,g[2][2]])*GPCpi(GPC.n)^(Integers()!(g[1][2]/g[1][1]))>;
end intrinsic;

intrinsic GL2BorelPC(N::RngIntElt) -> GrpMat, GrpPC, HomGrp
{ The standard Borel subgroup B of GL(2,Z/NZ) consisting of upper triangular matrices along with a polycyclic presentation P of B and an isomorphism B -> P. }
    require N gt 0: "N must be positive";
    if N eq 1 then B := gl2N1; P,pi := PCGroup(B); return B,P,pi; end if;
    return GL2BorelPC(Integers(N));
end intrinsic;

intrinsic GL2Borel1PC(R::Rng) -> GrpMat, GrpPC, HomGrp
{ The Borel1 subgroup B1 of GL(2,R) consisting of upper triangular matrices with a 1 in the bottom right (not the top left!), along with a polycyclic presentation P of B and an isomorphism B1 -> P. }
    N := Characteristic(R);
    require N gt 0 and IsCommutative(R): "R must be a commutative ring of positive characteristic.";
    m,pi :=MultiplicativeGroup(R);
    gg := [g:g in Generators(m)]; n := #gg+1;
    F := FreeGroup(n);
    rels1 := [F.i^Order(gg[i]):i in [1..#gg]];
    rels2 := [F.n^N];
    rels3 := [F.n^F.i=F.n^(Integers()!pi(-gg[i])):i in [1..#gg]];
    G := sub<GL(2,R)|[[1,0,0,pi(g)]:g in gg] cat [[1,1,0,1]]>;
    GPC := quo<GrpGPC: F | rels1, rels2, rels3>;
    P,GPCpi := PCGroup(GPC);
    // help Magma compute the iso G->P by manually handling the non-abelian part
    D := sub<GL(2,R)|[[pi(g),0,0,1]:g in gg]>;
    Dpi := hom<D->P|[GPCpi(GPC.i):i in [1..n-1]]>;
    return G,P,func<g|Dpi(D![g[1][1],0,0,1])*GPCpi(GPC.n)^(Integers()!(g[1][2]))>;
end intrinsic;

intrinsic GL2Borel1PC(N::RngIntElt) -> GrpMat, GrpPC, HomGrp
{ The standard Borel1 subgroup B1 of GL(2,R) consisting of upper triangular matrices with a 1 in the upper left, along with a polycyclic presentation P of B and an isomorphism B1 -> P. }
    require N gt 0: "N must be positive";
    if N eq 1 then B := gl2N1; P,pi := PCGroup(B); return B,P,pi; end if;
    return GL2Borel1PC(Integers(N));
end intrinsic;

intrinsic SL2Borel(R::Rng) -> GrpMat
{ The standard Borel subgroup of SL(2,R) consisting of upper triangular matrices. }
    m,pi := MultiplicativeGroup(R); gm := Generators(m);
    B := sub<SL(2,R)|[[pi(g),0,0,pi(-g)] : g in gm], [1,1,0,1]>;
    N := #R; B`Level := N; B`Order := SL2BorelSize(#R); B`Index := SL2Size(N) div B`Order; B`SL := true; B`NegOne := true;
    return B;
end intrinsic;

intrinsic SL2Borel(N::RngIntElt) -> GrpMat
{ The standard Borel subgroup of SL(2,Z/NZ), equivalently, the subgroup of upper triangular matrices in SL(2,Z/NZ). }
    return N eq 1 select sl2N1 else SL2Borel(Integers(N));
end intrinsic;

intrinsic SL2BorelPC(R::Rng) -> GrpMat, GrpPC, HomGrp
{ The standard Borel subgroup B of SL(2,R) consisting of upper triangular matrices along with a polycyclic presentation P of B and an isomorphism B -> P. }
    N := Characteristic(R);
    require N gt 0 and IsCommutative(R): "R must be a commutative ring of positive characteristic.";
    m,pi :=MultiplicativeGroup(R);
    gg := [g:g in Generators(m)]; n := #gg+1;
    F := FreeGroup(n);
    rels1 := [F.i^Order(gg[i]):i in [1..#gg]];
    rels2 := [F.n^N];
    rels3 := [F.n^F.i=F.n^(Integers()!pi(2*gg[i])):i in [1..#gg]];
    G := sub<SL(2,R)|[[pi(-g),0,0,pi(g)]:g in gg] cat [[1,1,0,1]]>;
    GPC := quo<GrpGPC: F | rels1, rels2, rels3>;
    P,GPCpi := PCGroup(GPC);
    // help Magma compute the iso G->P by manually handling the non-abelian part
    D := sub<GL(2,R)|[[pi(-g),0,0,pi(g)]:g in gg]>;
    Dpi := hom<D->P|[GPCpi(GPC.i):i in [1..n-1]]>;
    return G,P,func<g|Dpi(D![g[1][1],0,0,g[2][2]])*GPCpi(GPC.n)^(Integers()!(g[1][2]/g[1][1]))>;
end intrinsic;

intrinsic SL2BorelPC(N::RngIntElt) -> GrpMat, GrpPC, HomGrp
{ The standard Borel subgroup B of SL(2,Z/NZ) consisting of upper triangular matrices along with a polycyclic presentation P of B and an isomorphism B -> P. }
    if N eq 1 then B := gl2N1; P,pi := PCGroup(B); return B,P,pi; end if;
    return SL2BorelPC(Integers(N));
end intrinsic;

intrinsic GL2Borel1(R::Rng) -> GrpMat
{ The subgroup of the standard Borel subgroup of GL(2,R) that fixes a basis vector (under the left action of GL2 on column vectors), equivalently, the subgroup of upper triangular matrices in GL(2,R) with a 1 in the upper left. }
    m,pi := MultiplicativeGroup(R); gm := Generators(m);
    B1 := sub<GL(2,R) | [[1,0,0,pi(g)] : g in gm], [1,1,0,1]>;
    N := #R; B1`Level := N; B1`Order := GL2Borel1Size(N); B1`Index := GL2Size(N) div B1`Order; B1`NegOne := false;
    return B1;
end intrinsic;

intrinsic GL2Borel1(N::RngIntElt) -> GrpMat
{ The subgroup of the standard Borel subgroup of GL(2,Z/NZ) that fixes a basis vector (under the left action of GL2 on column vectors), equivalently, the subgroup of upper triangular matrices in GL(2,R) with a 1 in the upper left. }
    return N eq 1 select gl2N1 else GL2Borel1(Integers(N));
end intrinsic;

intrinsic GL2Borel12(R::Rng) -> GrpMat
{ The subgroup of the standard Borel subgroup of GL(2,R) that fixes a basis vector and vector of order 2, equivalently, the subgroup of upper triangular matrices in GL(2,R) with a 1 in the upper left and even entries in the upper right. }
    require IsEven(#R): "Base ring must have even cardinality";
    if #R eq 2 then return GL2FromGenerators(2,6,[]); end if;
    m,pi := MultiplicativeGroup(R); gm := Generators(m);
    B12 := sub<GL(2,R) | [[1,0,0,pi(g)] : g in gm], [1,2,0,1]>;
    N := #R; B12`Level := N; B12`Order := GL2Borel1Size(N) div 2; B12`Index := GL2Size(N) div B12`Order; B12`NegOne := false;
    return B12;
end intrinsic;

intrinsic GL2Borel12(N::RngIntElt) -> GrpMat
{ The subgroup of the standard Borel subgroup of GL(2,R) that fixes a basis vector and vector of order 2, equivalently, the subgroup of upper triangular matrices in GL(2,R) with a 1 in the upper left and even entries in the upper right. }
    return N eq 1 select gl2N1 else GL2Borel12(Integers(N));
end intrinsic;

intrinsic GL2BorelK1(R::Rng) -> GrpMat
{ The subgroup of the standard Borel subgroup of GL(2,R) that stabilizes +/-v for some basis vector v (under the left action of GL2 on column vectors), equivalently, the subgroup of upper triangular matrices in GL(2,R) with a 1 in the upper left. }
    if #R eq 2 then return GL2Borel1(R); end if;
    m,pi := MultiplicativeGroup(R); gm := Generators(m);
    BK1 := sub<GL(2,R) | [[1,0,0,pi(g)] : g in gm], [1,1,0,1], [-1,0,0,-1]>;
    N := #R; BK1`Level := N; BK1`Order := 2*GL2Borel1Size(N); BK1`Index := GL2Size(N) div BK1`Order; BK1`NegOne := true;
    return BK1;
end intrinsic;

intrinsic GL2BorelK1(N::RngIntElt) -> GrpMat
{ The subgroup of the standard Borel subgroup of GL(2,Z/NZ) that stablizes +/-v for soem basis vector v (under the left action of GL2 on column vectors), equivalently, the subgroup of upper triangular matrices in GL(2,R) with +/-1 in the upper left. }
    return N eq 1 select gl2N1 else GL2BorelK1(Integers(N));
end intrinsic;

intrinsic GL2BorelK12(R::Rng) -> GrpMat
{ The subgroup of the standard Borel subgroup of GL(2,R) that fixes a basis vector (under the left action of GL2 on column vectors), equivalently, the subgroup of upper triangular matrices in GL(2,R) with a 1 in the upper left. }
    require IsEven(#R): "Base ring must have even cardinality";
    if #R eq 2 then return GL2FromGenerators(2,6,[]); end if;
    m,pi := MultiplicativeGroup(R); gm := Generators(m);
    B12 := sub<GL(2,R) | [[1,0,0,pi(g)] : g in gm], [1,2,0,1], [-1,2,0,1]>;
    N := #R; B12`Level := N; B12`Order := GL2Borel1Size(N); B12`Index := GL2Size(N) div B12`Order; B12`NegOne := true;
    return B12;
end intrinsic;

intrinsic GL2BorelK12(N::RngIntElt) -> GrpMat
{ The subgroup of the standard Borel subgroup of GL(2,Z/NZ) that fixes a basis vector (under the left action of GL2 on column vectors), equivalently, the subgroup of upper triangular matrices in GL(2,R) with a 1 in the upper left. }
    return N eq 1 select gl2N1 else GL2BorelK12(Integers(N));
end intrinsic;

intrinsic GL2ProjectiveImage(H::GrpMat) -> GrpPerm
{ The image of the subgroup H of GL(2,Z/NZ) in PGL(2,Z/NZ). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return SymmetricGroup(1); end if;
    require Type(R) eq RngIntRes: "H must be a sugroup of GL(n,Z/NZ) for some positive integer N.";
    _,pi:=quo<GL(2,R)|GL2Scalars(R)>;
    return pi(H);
end intrinsic;

// Given a subgroup G of GL(2,p^2) that is conjugate to a subgroup H of GL(2,p), returns such an H, using the algorithm in Glasby and Howlett (Writing representations over minimal fields, Comm. Alg. 25 (1997), 1703-1711).
function ConjugateToRationalSubgroup(G)
    local F,p,r,x,C,mu,R,v,X,A,H;
    F:=BaseRing(G);  assert IsFinite(F) and IsField(F);
    if Degree(F) eq 1 then return G; end if;
    assert Degree(F) eq 2;
    p:=Characteristic(F);
    MatFrob := func<A|Parent(A)![A[1][1]^p,A[1][2]^p,A[2][1]^p,A[2][2]^p]>;
    r := [];
    for g in Generators(G) do
        r:=Append(r,[g[1][1]-g[1][1]^p,-g[2][1]^p,g[1][2],0]);
        r:=Append(r,[-g[1][2]^p,g[1][1]-g[2][2]^p,0,g[1][2]]);
        r:=Append(r,[g[2][1],0,g[2][2]-g[1][1]^p,-g[2][1]^p]);
        r:=Append(r,[0,g[2][1],-g[1][2]^p,g[2][2]-g[2][2]^p]);
    end for;
    while true do
        x:=Random(NullspaceOfTranspose(Matrix(r)));
        C:=MatrixRing(F,2)![x[i]:i in [1..Degree(x)]];
        if IsInvertible(C) then C:=GL(2,F)!C; break; end if;
    end while;
    for g in Generators(G) do if C^-1*g*C ne MatFrob(g) then print C, g; assert false; end if; end for;
    mu := C*MatFrob(C);
    assert mu[1][1] eq mu[2][2] and mu[1][2] eq 0 and mu[2][1] eq 0;
    mu := GF(p)!mu[1][1];
    b,v:=NormEquation(F,mu);
    C:=GL(2,F)![1/v,0,0,1/v]*C;
    assert C*MatFrob(C) eq Identity(G);
    while true do
        X:=Random(MatrixRing(F,2));
        A:=X+C*MatFrob(X);
        if not IsInvertible(A) then continue; end if;
        A:=GL(2,F)!A;
        H:=Conjugate(G,A);
        for h in Generators(H) do assert MatFrob(h) eq h; end for;
        return sub<GL(2,p)|Generators(H)>;
    end while;
end function;

// Based on Thm 5.5 of Flannery-O'Brien (Linear groups of small degree over finite fields, Internat. J. Algebra Comput.  15 (2005), 467--502),
intrinsic GL2MaximalA4(p::RngIntElt) -> GrpMat[RngIntRes]
{ The largest subgroup of GL(2,Z/pZ) with projective image A4 (it will necessarily have determinant index 2). }
    require IsPrime(p) and p ge 5: "p must be a prime greater than 3.";
    F := p mod 4 eq 1 select GF(p) else GF(p^2);  G := GL(2,F);
    w := RootOfUnity(4,F); z := F!PrimitiveRoot(p);
    H := ConjugateToRationalSubgroup(sub<G|[(w-1)/2,(w-1)/2,(w+1)/2,-(w+1)/2],[w,0,0,-w],[z,0,0,z]>);
    H := ChangeRing(H,Integers(p));
    H`Level := p; H`Order := 12*(p-1); H`Index := GL2Size(p) div H`Order; H`NegOne := true;
    return H;
end intrinsic;

// Based on Thm 5.8 of Flannery-O'Brien (Linear groups of small degree over finite fields, Internat. J. Algebra Comput.  15 (2005), 467--502),
intrinsic GL2MaximalS4(p::RngIntElt) -> GrpMat[RngIntRes]
{ The largest subgroup of GL(2,Z/pZ) with projective image S4 (it will necessarily have determinant index 2 for p=1,7 mod 8). }
    require IsPrime(p) and p ge 5: "p must be a prime greater than 3.";
    a := (p mod 8 in [1,7]) select 1 else 2;
    F := GF(p^2);  G := GL(2,F);
    w := RootOfUnity(4,F);  c := Sqrt(F!2); t := G![(1+w)/c,0,0,(1-w)/c];  z := F!PrimitiveRoot(p);
    if a eq 1 then
        H := ConjugateToRationalSubgroup(sub<G|[(w-1)/2,(w-1)/2,(w+1)/2,-(w+1)/2],[(1+w)/c,0,0,(1-w)/c],[z,0,0,z]>);
    elif p mod 8 eq 1 then
        H := ConjugateToRationalSubgroup(sub<G|[(w-1)/2,(w-1)/2,(w+1)/2,-(w+1)/2],[z*(1+w)/c,0,0,z*(1-w)/c],[z^2,0,0,z^2]>);
    else
        H := ConjugateToRationalSubgroup(sub<G|[(w-1)/2,(w-1)/2,(w+1)/2,-(w+1)/2],[u*(1+w)/c,0,0,u*(1-w)/c],[z,0,0,z]>) where u:=Sqrt(z);
    end if;
    H := ChangeRing(H,Integers(p));
    H`Level := p; H`Order := 24*(p-1); H`Index := GL2Size(p) div H`Order; H`NegOne := true;
    return H;
end intrinsic;

// Based on Thm 5.11 of Flannery-O'Brien (Linear groups of small degree over finite fields, Internat. J. Algebra Comput.  15 (2005), 467--502),
intrinsic GL2MaximalA5(p::RngIntElt) -> GrpMat[RngIntRes]
{ For a prime p = +/-1 mod 5, the largest subgroup of GL(2,Z/pZ) with projective image A5 (it will necessarily have determinant index 2). }
    require IsPrime(p) and p mod 5 in [1,4]: "p must be a prime congruent to +/-1 mod 5.";
    F:=GF(p^2);  G:=GL(2,F);
    w:=RootOfUnity(4,F); b := Sqrt(F!5); z:=F!PrimitiveRoot(p);
    H := ConjugateToRationalSubgroup(sub<G|[(w-1)/2,(w-1)/2,(w+1)/2,-(w+1)/2],[w,0,0,-w],[w/2,(1-b)/4-w*(1+b)/4,(-1+b)/4-w*(1+b)/4,-w/2],[z,0,0,z]>);
    H := ChangeRing(H,Integers(p));
    H`Level := p; H`Order := 60*(p-1); H`Index := GL2Size(p) div H`Order; H`NegOne := true;
    return H;
end intrinsic;

intrinsic GL2ConjugateSubgroup(H::GrpMat, K::GrpMat) -> GrpMatElt
{ Given subgroups H and K of GL(2,Zhat) represented by reductions to their levels (or compatible multiples of their levels) such that K is conjugate to a subgroup of H, returns g in GL(2,BaseRing(K)) such that (the inverse image of) K^g lies in (the inverse image of) H (the element g is guaranteed to be the identity if K lies in H but is otherwise chosen at random).
  If K is not a subgroup of H this will eventually be detected, but not efficiently (you should use GL2IsConjugateSubgroup in this situation). }
    N := #BaseRing(K); if not IsFinite(N) then assert K eq gl2N1; assert (not IsFinite(BaseRing(H))) or GL2Order(H) eq GL2Size(#BaseRing(H)); return Identity(gl2N1); end if;
    H := GL2Lift(H,N); if K subset H then return Identity(H); end if;
    G := GL(2,Integers(N));
    for i:=1 to N*N*N*N do g := Random(G); if K^g subset H then return g; end if; end for;
    b,g := IsConjugateSubgroup(G,H,K); assert b;
    return g;
end intrinsic;

intrinsic GL2IsConjugateSubgroup(H::GrpMat, K::GrpMat) -> BoolElt, GrpMatElt
{ Given subgroups H and K of GL(2,Zhat) represented by reductions to their levels (or compatible multiples of their levels) determines whether K is conjugate to a subgroup of H and if so returns g in GL(2,BaseRing(K)) such that (the inverse image of) K^g lies in (the inverse image of) H. }
    N := #BaseRing(K); if not IsFinite(N) then assert K eq gl2N1; assert (not IsFinite(BaseRing(H))) or GL2Order(H) eq GL2Size(#BaseRing(H)); return true,Identity(gl2N1); end if;
    H := GL2Lift(H,N); if K subset H then return true, Identity(H); end if;
    return IsConjugateSubgroup(GL(2,Integers(N)),H,K);
end intrinsic;

intrinsic GL2MinimizeGenerators(H::GrpMat : MaxAttempts:=30, CheckAbelian:=true) -> GrpMat
{ Attempts to minimize the number of generators of a subgroup H of GL(2,Z/NZ) by sampling random elements.  Result is not guaranteed to be optimal unless H is abelian (but it is likely to be close to optimal, c.f. doi.org/10.1016/S0021-8693(02)00528-8). }
    if not IsFinite(BaseRing(H)) then return H; end if;
    if CheckAbelian and IsAbelian(H) then  Hab,pi := AbelianGroup(H); B := AbelianBasis(Hab); return gl2copyattr(sub<H|[Inverse(pi)(b):b in B]>,H); end if;
    N := #BaseRing(H);
    r := 2;
    if N le 16 then
        while true do for i:=1 to MaxAttempts do HH := sub<H|[Random(H):j in [1..r]]>; if HH eq H then return gl2copyattr(HH,H); end if; end for; r +:= 1; end while;
    else
        if not assigned H`Order then H`Order := GL2Order(H); H`Index := GL2Size(N) div H`Order; end if;
        while true do for i:=1 to MaxAttempts do HH := sub<H|[Random(H):j in [1..r]]>; if GL2Order(HH) eq H`Order then return gl2copyattr(HH,H); end if; end for; r +:= 1; end while;
    end if;
end intrinsic;

intrinsic SL2MinimizeGenerators(H::GrpMat : MaxAttempts:=30, CheckAbelian:=true) -> GrpMat
{ Attempts to minimize the number of generators of a subgroup H of SL(2,Z/NZ) by sampling random elements.  Result is not guaranteed to be optimal unless H is abelian (but it likely to be close to optimal, c.f. doi.org/10.1016/S0021-8693(02)00528-8). }
    require H`SL: "H must be a subgroup of SL2 (and marked as such).";
    if not IsFinite(BaseRing(H)) then return H; end if;
    if CheckAbelian and IsAbelian(H) then  Hab,pi := AbelianGroup(H); B := AbelianBasis(Hab); return sl2copyattr(sub<H|[Inverse(pi)(b):b in B]>,H); end if;
    N := #BaseRing(H);
    r := 2;
    if N le 16 then
        while true do for i:=1 to MaxAttempts do HH := sub<H|[Random(H):j in [1..r]]>; if HH eq H then return sl2copyattr(HH,H); end if; end for; r +:= 1; end while;
    else
        if not assigned H`Order then H`Order := SL2Order(H); H`Index := SL2Size(N) div H`Order; end if;
        while true do for i:=1 to MaxAttempts do HH := sub<H|[Random(H):j in [1..r]]>; HH`SL:=true; if SL2Order(HH) eq H`Order then return sl2copyattr(HH,H); end if; end for; r +:= 1; end while;
    end if;
end intrinsic;

intrinsic GL2Standardize(H::GrpMat) -> GrpMat, GrpMatElt
{ Given a subgroup of GL(2,Z/NZ) attempts to conjugate to a nice form (e.g. diagonal or upper triangular).  Ths can be very slow, use with caution. }
    N := #BaseRing(H); if not IsFinite(N) then return H,Identity(H); end if;
    G := GL(2,Integers(N));
    b,a := IsConjugateSubgroup(G,GL2SplitCartan1(N),H); if b then return gl2copyattr(Conjugate(H,a),H),a; end if;
    b,a := IsConjugateSubgroup(G,GL2SplitCartan(N),H); if b then return gl2copyattr(Conjugate(H,a),H),a; end if;
    b,a := IsConjugateSubgroup(G,GL2Borel1(N),H); if b then return gl2copyattr(Conjugate(H,a),H),a; end if;
    b,a := IsConjugateSubgroup(G,GL2Borel(N),H); if b then return gl2copyattr(Conjugate(H,a),H),a; end if;
    b,a := IsConjugateSubgroup(G,GL2SplitCartanNormalizer(N),H); if b then return gl2copyattr(Conjugate(H,a),H),a; end if;
    b,a := IsConjugateSubgroup(G,GL2SplitCartanFullNormalizer(N),H); if b then return gl2copyattr(Conjugate(H,a),H),a; end if;
    b,a := IsConjugateSubgroup(G,GL2NonsplitCartan(N),H); if b then return gl2copyattr(Conjugate(H,a),H),a; end if;
    b,a := IsConjugateSubgroup(G,GL2NonsplitCartanNormalizer(N),H); if b then return gl2copyattr(Conjugate(H,a),H),a; end if;
    b,a := IsConjugateSubgroup(G,GL2NonsplitCartanFullNormalizer(N),H); if b then return gl2copyattr(Conjugate(H,a),H),a; end if;
    return H,Identity(H);
end intrinsic;

/*** GL2/SL2 similarity invariants/counts ***/

intrinsic GL2SimilarityClassMap(N::RngIntElt) -> UserProgram
{ Returns a function to compute the similarity invariant of an element of GL(2,Z/NZ) that is optimized to the shape of N. }
    Z := Integers(); if N eq 1 then return func<M|[Z|]>; end if;
    b := Factorization(N); b := [[a[1]^i:i in [1..a[2]]]:a in b]; n := #b; nn := [#a:a in b]; R := [[Integers(b[j][i]):i in [1..nn[j]]]:j in [1..n]];
    return func<M|[(j eq 0 select [Z|0,0,Determinant(A),Trace(A)] else // we could hardwire det(A)=1 for SL2 but the benefit is completely negligible
                       (j eq e select [Z|e,A[1][1],0,0] else
                           ([Z|j,z,(((B[1][1]-z)*(B[2][2]-z)-B[1][2]*B[2][1]) div (q*q)) mod r,((Trace(B)-2*z) div q) mod r]
                            where z := B[1][1] mod q where B:=ChangeRing(A,Z) where q := a[j] where r:= a[e-j])))
                   where j := Max([0] cat [j:j in [1..e] | isscalar(ChangeRing(A,R[k][j]))]) where A:=ChangeRing(M,R[k][e]) where e:=nn[k] where a:=b[k] : k in [1..n]]>;
end intrinsic;

intrinsic SL2SimilarityClassMap(N::RngIntElt) -> UserProgram
{ Returns a function to compute the similarity invariant of an element of SL(2,Z/NZ) that is optimized to the shape of N. }
    return GL2SimilarityClassMap(N);
end intrinsic;

intrinsic GL2SimilarityClassIndexMap(N::RngIntElt:S:=GL2SimilaritySet(N)) -> UserProgram
{ Returns a function to compute the index of the similarity invariant of an element of GL(2,Z/NZ) in the sorted list of similarity invariants for N, optimized to the shape of N. }
    Z := Integers(); if N eq 1 then return func<M|[Z|]>; end if;
    b := Factorization(N); b := [[a[1]^i:i in [1..a[2]]]:a in b]; n := #b; nn := [#a:a in b]; R := [[Integers(b[j][i]):i in [1..nn[j]]]:j in [1..n]];
    return func<M|Index(S,
                  [(j eq 0 select [Z|0,0,Determinant(A),Trace(A)] else
                       (j eq e select [Z|e,A[1][1],0,0] else
                           ([Z|j,z,(((B[1][1]-z)*(B[2][2]-z)-B[1][2]*B[2][1]) div (q*q)) mod r,((Trace(B)-2*z) div q) mod r]
                            where z := B[1][1] mod q where B:=ChangeRing(A,Z) where q := a[j] where r:= a[e-j])))
                   where j := Max([0] cat [j:j in [1..e] | isscalar(ChangeRing(A,R[k][j]))]) where A:=ChangeRing(M,R[k][e]) where e:=nn[k] where a:=b[k] : k in [1..n]])>;
end intrinsic;

intrinsic SL2SimilarityClassIndexMap(N::RngIntElt) -> UserProgram
{ Returns a function to compute the index of the similarity invariant of an element of SL(2,Z/NZ) in the sorted list of similarity invariants for N, optimized to the shape of N. }
    return GL2SimilarityClassIndexMap(N:S:=SL2SimilaritySet(N));
end intrinsic;

intrinsic GL2PrimitiveSimilarityClassIndexMap(N::RngIntElt) -> UserProgram
{ Returns a function to compute the index of the similarity invariant of an element of GL(2,Z/NZ) in the sorted list of primitive similarity invariants for N or 0 if the similarity class is not primitive), optimized to the shape of N. }
    return GL2SimilarityClassIndexMap(N:S:=GL2PrimitiveSimilaritySet(N));
end intrinsic;

intrinsic SL2PrimitiveSimilarityClassIndexMap(N::RngIntElt) -> UserProgram
{ Returns a function to compute the index of the similarity invariant of an element of SL(2,Z/NZ) in the sorted list of primitive similarity invariants for N or 0 if the similarity class is not primitive), optimized to the shape of N. }
    return GL2SimilarityClassIndexMap(N:S:=SL2PrimitiveSimilaritySet(N));
end intrinsic;

intrinsic GL2SimilarityClassRepMap(N::RngIntElt) -> UserProgram
{ Returns a function to construct an element of GL(2,Z/NZ) representing a given similarity class that is optimized to the shape of N. }
    ZZ := Integers(); M2 := MatrixRing(Integers(),2); I2 := Identity(M2); if N eq 1 then return func<M|I2>; end if;
    b := Factorization(N); p:=[a[1]:a in b]; b := [a[1]^a[2]:a in b];
    return func<inv|GL2!CRT([r[2]*I2+p[i]^r[1]*M2![0,1,-r[3],r[4]] where r:=inv[i]:i in [1..#inv]],b)> where GL2 := GL2Ambient(N);
end intrinsic;

intrinsic GL2SimilarityClassRepMap2(N::RngIntElt) -> UserProgram
{ Returns a function to construct an element of GL(2,Z/NZ) representing a given similarity class that is optimized to the shape of N. }
    ZZ := Integers(); M2 := MatrixRing(Integers(),2); I2 := Identity(M2); if N eq 1 then return func<M|Identity(M2)>; end if;
    b := Factorization(N); p:=[a[1]:a in b]; b := [a[1]^a[2]:a in b];
    return func<inv|GL2!CRT([r[2]*I2+p[i]^r[1]*M2![0,1,-r[3],r[4]] where r:=inv[i]:i in [1..#inv]],b)> where GL2 := GL2Ambient(N);
end intrinsic;

intrinsic SL2SimilarityClassRepMap(N::RngIntElt) -> UserProgram
{ Returns a function to construct an element of GL(2,Z/NZ) representing a given similarity class that is optimized to the shape of N. }
    ZZ := Integers(); M2 := MatrixRing(Integers(),2); I2 := Identity(M2); if N eq 1 then return func<M|I2>; end if;
    b := Factorization(N); p:=[a[1]:a in b]; b := [a[1]^a[2]:a in b];
    return func<inv|SL2!CRT([r[2]*I2+p[i]^r[1]*M2![0,1,-r[3],r[4]] where r:=inv[i]:i in [1..#inv]],b)> where SL2 := SL2Ambient(N);
end intrinsic;

// Theorem 4.3.8 in Williams' thesis (https://mountainscholar.org/bitstream/handle/10217/68201/Williams_colostate_0053A_11267.pdf)
// returns the number of elements of GL(2,Z/p^eZ) with similarity invariant r
function sslen(p,e,r)
    m := p^(4*e-3)*(p-1)^2*(p+1);
    if r[1] eq 0 then return ExactQuotient(m,p^(2*(e-1))*(p-1)*(p-KroneckerSymbol(r[4]^2-4*r[3],p)));
    elif r[1] lt e then return ExactQuotient(m,p^(2*(e+r[1]-1))*(p-1)*(p-KroneckerSymbol(r[4]^2-4*r[3],p)));
    else return 1; end if;
end function;

intrinsic GL2SimilarityClassSizeMap(N::RngIntElt) -> UserProgram
{ Returns a function to compute the length of a given similarity class that is optimized to the shape of N. }
    if N eq 1 then return func<s|1>; end if;
    return func<s|&*[sslen(A[i][1],A[i][2],s[i]):i in [1..#A]]> where A:=Factorization(N);
end intrinsic;

intrinsic GL2SimilarityClassSize(g::GrpMatElt) -> RngIntElt
{ Number of elements of GL(2,Z/NZ) in the similarity/conjugacy class of g. }
    return &*[sslen(A[i][1],A[i][2],s[i]):i in [1..#A]] where s := GL2SimilarityInvariant(g) where A:=Factorization(#BaseRing(g));
end intrinsic;

intrinsic GL2ConjugacyClassSize(g::GrpMatElt) -> RngIntElt
{ Number of elements of GL(2,Z/NZ) in the similarity/conjugacy class of g. }
    return GL2SimilarityClassSize(g);
end intrinsic;

intrinsic GL2IsConjugate(g::GrpMatElt,h::GrpMatElt) -> BoolElt
{ Returns true iff g and h are conjugate elements of GL(2,Z/NZ). You can use GL2Conjugator to get a conjugating element. }
    return GL2SimilarityInvariant(g) eq GL2SimilarityInvariant(h);
end intrinsic;

intrinsic GL2Conjugator(g::GrpMatElt,h::GrpMatElt) -> GrpMatElt
{ Given conjugate elements g and h of GL(2,Z/NZ) returns c in GL(2,Z/NZ) such that g^c eq h.  Expected running time is quasi-linear in N (square-root of conjugacy class size, which is O(N^2)). }
    G := GL(2,BaseRing(g)); g := G!g; h := G!h;
    n := GL2SimilarityClassSize(g); m := Ceiling(Sqrt(n)); G := Parent(g);
    X := AssociativeArray(); for i:=1 to m do c:=Random(G); X[g^c] := c; end for;
    for i:=1 to 2*m do ci:=Random(G); b,c := IsDefined(X,h^ci); if b then return c*ci^-1; end if; end for;
    assert GL2IsConjugate(g,h);
    repeat ci:=Random(G); b,c := IsDefined(X,h^ci); until b; return c*ci^-1;
end intrinsic;

intrinsic GL2Conjugator(G::GrpMat, g::GrpMatElt, h::GrpMatElt) -> GrpMatElt
{ Given conjugate elements g and h of G returns c in GL(2,Z/NZ) such that g^c eq h.  Expected running time is quasi-linear in N.  May run forever if g and h are not conjugate elements of G. }
    g := G!g; h := G!h;
    n := GL2SimilarityClassSize(g); m := Ceiling(Sqrt(n)); G := Parent(g);
    X := AssociativeArray(); for i:=1 to m do c:=Random(G); X[g^c] := c; end for;
    for i:=1 to 2*m do ci:=Random(G); b,c := IsDefined(X,h^ci); if b then return c*ci^-1; end if; end for;
    assert GL2IsConjugate(g,h);
    repeat ci:=Random(G); b,c := IsDefined(X,h^ci); until b; return c*ci^-1; // just keep trying, it may be too expensive to do anything else
end intrinsic;

// Based on the "baby 2x2 case" in https://arxiv.org/abs/0708.1608 (also see https://mountainscholar.org/bitstream/handle/10217/68201/Williams_colostate_0053A_11267.pdf)
intrinsic GL2SimilarityInvariant(M::GrpMatElt[RngIntRes]) -> SeqEnum[SeqEnum[RngIntElt]]
{ Given a matrix in GL(2,Z/NZ) returns a list of quadruples of integers (one for each prime divisor of N) that uniquely identifies its similarity/conjugacy class. }
    N := #BaseRing(M);
    Z := Integers();
    S := [];
    for a in Factorization(N) do
        p := a[1]; e := a[2];
        A := ChangeRing(M,Integers(p^e));
        j := Max([0] cat [j:j in [1..e] | isscalar(ChangeRing(A,Integers(p^j)))]);
        if j eq 0 then S cat:= [[Z|0,0,Determinant(A),Trace(A)]]; continue; end if;
        if j eq e then S cat:= [[Z|e,A[1][1],0,0]]; continue; end if;
        q := p^j; r := p^(e-j);
        A := ChangeRing(A,Integers());
        z := A[1][1] mod q;
        S cat:= [[Z|j,z,ExactQuotient((A[1][1]-z)*(A[2][2]-z)-A[1][2]*A[2][1],q*q) mod r,ExactQuotient(Trace(A)-2*z,q) mod r]];
    end for;
    return S;
end intrinsic;

intrinsic GL2SimilaritySet(N::RngIntElt) -> SetIndx[SeqEnum[SeqEnum[RngIntElt]]]
{ Sorted indexed set of similarity invariants in GL(2,Z/NZ). }
    ZZ := Integers();
    if IsDefined(ZZ`GL2Cache["ssets"],N) then return ZZ`GL2Cache["ssets"][N]; end if;
    if N eq 1 then return {@ [Universe([[ZZ|]])|] @}; end if;
    A := Factorization(N);
    if #A gt 1 then
        S := IndexedSet(Sort([[c[i][1]:i in [1..#A]]:c in CartesianProduct([GL2SimilaritySet(a[1]^a[2]):a in A])]));
        ZZ`GL2Cache["ssets"][N] := S;
        return S;
    end if;
    p := A[1][1]; e:= A[1][2];
    reps := [[0,0,d,t]:d,t in [0..p^e-1]|d mod p ne 0];
    for j:=1 to e-1 do reps cat:=[[j,z,d,t]:z in [1..p^j-1],d,t in [0..p^(e-j)-1]|z mod p ne 0]; end for;
    reps cat:=[[e,z,0,0]:z in [1..p^e-1]|z mod p ne 0];
    S := IndexedSet([[r]:r in Sort(reps)]);
    ZZ`GL2Cache["ssets"][N] := S;
    return S;
end intrinsic;

intrinsic SL2SimilaritySet(N::RngIntElt) -> SetIndx[SeqEnum[SeqEnum[RngIntElt]]]
{ Sorted indexed set of similarity invariants in SL(2,Z/NZ). }
    ZZ := Integers();
    if IsDefined(ZZ`SL2Cache["ssets"],N) then return ZZ`SL2Cache["ssets"][N]; end if;
    if N eq 1 then return {@ [Universe([[ZZ|]])|] @}; end if;
    // This could be made much faster by optimizing for the SL2 case, but this optimization is non-trivial so we won't bother (it is a cached precomputation)
    S :=IndexedSet([r:r in GL2SimilaritySet(N)|Determinant(rep(r)) eq 1]) where rep:=GL2SimilarityClassRepMap(N);
    ZZ`SL2Cache["ssets"][N] := S;
    return S;
end intrinsic;

intrinsic GL2SimilarityClasses(N::RngIntElt) -> SeqEnum[Tup]
{ Sequence of tuples <inv,rep> corresponding to similarity/conjugacy classes of GL(2,Integers(N)) sorted by similarity invariant (this is faster than GL2ConjugacyClasses and sufficient if you do not need to the order or size of each class). }
    ZZ := Integers();
    if IsDefined(ZZ`GL2Cache["sclasses"],N) then return ZZ`GL2Cache["sclasses"][N]; end if;
    if IsDefined(ZZ`GL2Cache["cclasses"],N) then S := [<r[4],r[3]>:r in ZZ`GL2Cache["cclasses"][N]]; ZZ`GL2Cache["sclasses"][N] := S; return S; end if;
    if N eq 1 then return [<[Universe([ZZ|])|],GL2Ambient(1)![1,0,0,1]>]; end if;
    A := Factorization(N); GL2 := GL2Ambient(N);
    if #A gt 1 then
        M2 := MatrixRing(Integers(),2);
        S := CartesianProduct([[<r[1],M2!r[2]>:r in GL2SimilarityClasses(a[1]^a[2])]:a in A]);
        S := Sort([<[r[1][1]:r in x],a> where a:=GL2!CRT([M2!r[2]:r in x],[A[i][1]^A[i][2]:i in [1..#A]]):x in S]);
        ZZ`GL2Cache["sclasses"][N] := S; 
        return S;
    end if;
    p := A[1][1]; e:= A[1][2];
    reps := [[0,0,d,t]:d,t in [0..p^e-1]|d mod p ne 0];
    for j:=1 to e-1 do reps cat:=[[j,z,d,t]:z in [1..p^j-1],d,t in [0..p^(e-j)-1]|z mod p ne 0]; end for;
    reps cat:=[[e,z,0,0]:z in [1..p^e-1]|z mod p ne 0];
    S := Sort([<[r],mat(r)>:r in reps]) where mat := func<r|GL2!(r[2]*I2+p^r[1]*M2![0,1,-r[3],r[4]])> where I2:=Identity(M2) where M2 := MatrixRing(Integers(N),2);
    ZZ`GL2Cache["sclasses"][N] := S;
    return S;
end intrinsic;

intrinsic SL2SimilarityClasses(N::RngIntElt) -> SeqEnum[Tup]
{ Sequence of tuples <inv,rep> corresponding to similarity classes of SL(2,Integers(N)) sorted by similarity invariant (note that for SL2 similarity is weaker than conjugacy). }
    ZZ := Integers();
    if IsDefined(ZZ`SL2Cache["sclasses"],N) then return ZZ`SL2Cache["sclasses"][N]; end if;
    if IsDefined(ZZ`SL2Cache["cclasses"],N) then S := [<r[4],r[3]>:r in ZZ`SL2Cache["cclasses"][N]]; ZZ`SL2Cache["sclasses"][N] := S; return S; end if;
    if N eq 1 then return [<[Universe([ZZ|])|],SL2Ambient(1)![1,0,0,1]>]; end if;
    S := [<r[1],SL2!r[2]>:r in GL2SimilarityClasses(N)|Determinant(r[2]) eq 1] where SL2 := SL2Ambient(N);
    ZZ`SL2Cache["sclasses"][N] := S;
    return S;
end intrinsic;

intrinsic GL2ConjugacyClasses(N::RngIntElt) -> SeqEnum[Tup]
{ Sequence of tuples <order,length,rep,inv> giving the conjugacy classes of GL(2,Integers(N)) ordered by inv (so order matches that of GL2SimilarityClasses, not ConjugacyClasses). }
    ZZ := Integers();
    b, S := IsDefined(ZZ`GL2Cache["cclasses"],N);
    if b then return S; end if;
    if N eq 1 then return [<1,1,GL2Ambient(1)![1,0,0,1],[]>]; end if;
    A := Factorization(N);  GL2 := GL2Ambient(N);
    if #A gt 1 then
        S := CartesianProduct([[<r[1],r[2],M2!r[3],r[4]>:r in GL2ConjugacyClasses(a[1]^a[2])]:a in A]) where M2 := MatrixRing(Integers(),2);;
        S := Sort([<LCM([r[1]:r in x]),&*[r[2]:r in x],a,[r[4][1]:r in x]> where a:=GL2!CRT([r[3]:r in x],[A[i][1]^A[i][2]:i in [1..#A]]):x in S],
                  func<a,b|a[4] lt b[4] select -1 else 1>);
        ZZ`GL2Cache["cclasses"][N] := S;
        return S;
    end if;
    p := A[1][1]; e:= A[1][2];
    reps := [[0,0,d,t]:d,t in [0..p^e-1]|d mod p ne 0];
    for j:=1 to e-1 do reps cat:=[[j,z,d,t]:z in [1..p^j-1],d,t in [0..p^(e-j)-1]|z mod p ne 0]; end for;
    reps cat:=[[e,z,0,0]:z in [1..p^e-1]|z mod p ne 0];
    S := Sort([<Order(h),sslen(p,e,r),h,[r]> where h:=mat(r):r in reps], func<a,b|a[4] lt b[4] select -1 else 1>) where mat:=func<r|GL2!(r[2]*I2+p^r[1]*M2![0,1,-r[3],r[4]])> where I2 := Identity(M2) where M2 := MatrixRing(Integers(N),2);
    ZZ`GL2Cache["cclasses"][N] := S;
    return S;
end intrinsic;

intrinsic SL2GL2ConjugacyClasses(N::RngIntElt) -> SeqEnum[Tup]
{ Sequence of tuples <order,length,rep,inv> giving the GL2 conjugacy/similarity classes of SL(2,Integers(N)) ordered by inv (so order matches that of SL2SimilarityClasses). }
    ZZ := Integers();
    b, S := IsDefined(ZZ`SL2Cache["cclasses"],N);
    if b then return S; end if;
    if N eq 1 then return [<1,1,SL2Ambient(1)![1,0,0,1],[Universe([ZZ|])|]>]; end if;
    SL2 := SL2Ambient(N);
    S := [<r[1],r[2],SL2!r[3],r[4]>:r in GL2ConjugacyClasses(N)|Determinant(r[3]) eq 1];
    ZZ`SL2Cache["cclasses"][N] := S;
    return S;
end intrinsic;

intrinsic GL2SimilarityReps(N::RngIntElt) -> SetIndx
{ Sorted indexed set of similarity invariants in GL(2,Z/NZ). }
    ZZ := Integers();
    if IsDefined(ZZ`GL2Cache["sreps"],N) then return ZZ`GL2Cache["sreps"][N]; end if;
    if N eq 1 then return [Identity(GL2Ambient(1))]; end if;
    S := [mat(r):r in S] where S:=GL2SimilaritySet(N) where mat := GL2SimilarityClassRepMap(N);
    ZZ`GL2Cache["sreps"][N] := S;
    return S;
end intrinsic;

intrinsic SL2SimilarityReps(N::RngIntElt) -> SetIndx
{ Sorted indexed set of similarity invariants in SL(2,Z/NZ). }
    ZZ := Integers();
    if IsDefined(ZZ`SL2Cache["sreps"],N) then return ZZ`SL2Cache["sreps"][N]; end if;
    if N eq 1 then return [Identity(SL2Ambient(1))]; end if;
    S := [mat(r):r in S] where S:=SL2SimilaritySet(N) where mat := SL2SimilarityClassRepMap(N);
    ZZ`SL2Cache["sreps"][N] := S;
    return S;
end intrinsic;

intrinsic GL2PrimitiveSimilarityReps(N::RngIntElt) -> SetIndx
{ Sorted indexed set of similarity invariants in GL(2,Z/NZ). }
    ZZ := Integers();
    if IsDefined(ZZ`GL2Cache["psreps"],N) then return ZZ`GL2Cache["psreps"][N]; end if;
    if N eq 1 then return [Identity(GL2Ambient(1))]; end if;
    S := [mat(r):r in S] where S:=GL2PrimitiveSimilaritySet(N) where mat := GL2SimilarityClassRepMap(N);
    ZZ`GL2Cache["psreps"][N] := S;
    return S;
end intrinsic;

intrinsic SL2PrimitiveSimilarityReps(N::RngIntElt) -> SetIndx
{ Sorted indexed set of similarity invariants in SL(2,Z/NZ). }
    ZZ := Integers();
    if IsDefined(ZZ`SL2Cache["psreps"],N) then return ZZ`SL2Cache["psreps"][N]; end if;
    if N eq 1 then return [Identity(SL2Ambient(1))]; end if;
    S := [mat(r):r in S] where S:=SL2PrimitiveSimilaritySet(N) where mat := SL2SimilarityClassRepMap(N);
    ZZ`SL2Cache["psreps"][N] := S;
    return S;
end intrinsic;

intrinsic GL2SavePrimitiveSimilarityIndexes(N::RngIntElt) -> BoolElt
{ Write list of primitive similarity indexes for GL(2,Z/NZ) to disk. }
    filename := "gl2psindex_" cat itoa(N) cat ".dat";
    if OpenTest(filename,"r") then return false; end if;
    WriteObject(Open(filename,"w"),GL2PrimitiveSimilarityIndexes(N:NoFile));
    return true;
end intrinsic;

intrinsic GL2LoadPrimitiveSimilarityIndexes(N::RngIntElt) -> BoolElt
{ Read list of primitive similarity indexes for GL(2,Z/NZ) from disk. }
    b,fp := OpenTest("gl2psindex_" cat itoa(N) cat ".dat","r"); if not b then return false; end if;
    ZZ := Integers();
    try
        ZZ`GL2Cache["psindexes"][N] := ReadObject(fp);
    catch e;
        return false;
    end try;
    return true;
end intrinsic;

intrinsic SL2SavePrimitiveSimilarityIndexes(N::RngIntElt) -> BoolElt
{ Write list of primitive similarity indexes for SL(2,Z/NZ) to disk. }
    filename := "sl2psindex_" cat itoa(N) cat ".dat";
    if OpenTest(filename,"r") then return false; end if;
    WriteObject(Open(filename,"w"),SL2PrimitiveSimilarityIndexes(N:NoFile));
    return true;
end intrinsic;

intrinsic SL2LoadPrimitiveSimilarityIndexes(N::RngIntElt) -> BoolElt
{ Read list of primitive similarity indexes for GL(2,Z/NZ) from disk. }
    b,fp := OpenTest("sl2psindex_" cat itoa(N) cat ".dat","r"); if not b then return false; end if;
    ZZ := Integers();
    try
        ZZ`SL2Cache["psindexes"][N] := ReadObject(fp);
    catch e;
        return false;
    end try;
    return true;
end intrinsic;

intrinsic GL2PrimitiveSimilarityIndexes(N::RngIntElt:NoCache:=false,NoFile:=false) -> SetIndx[RngIntElt]
{ Indices of the entries in the ordered list of similarity/conjugacy classes of GL(2,Integers(N)) returned by GL2SimilarityClasses/GL2ConjugacyClasses of classes that are 
  the minimal representatives of their division (the union of conjugacy classes whose representative generate the same cyclic group, up to conjugacy).  Two subgroups of
  GL(2,Z/NZ) are Gassmann equivalent if and only if they contain the same number of elements in each primitive similarity class. }
    if N eq 1 then return {@ 1 @}; end if;
    ZZ := Integers();
    if not NoCache and IsDefined(ZZ`GL2Cache["psindexes"],N) then return ZZ`GL2Cache["psindexes"][N]; end if;
    if not NoFile and GL2LoadPrimitiveSimilarityIndexes(N) then return ZZ`GL2Cache["psindexes"][N]; end if;
    timer := Realtime();
    C := GL2SimilarityClasses(N); ind := GL2SimilarityClassIndexMap(N);
    I := []; J := [true : i in [1..#C]];
    for i:=1 to #C do
        if J[i] then
            Append(~I,i);
            g := C[i][2]; n := Order(g); m := 1; h := g;
            for m:=2 to n-1 do h *:= g; if GCD(m,n) eq 1 then J[ind(h)] := false; end if; end for;
        end if;
    end for;
    S := IndexedSet(I); ZZ`GL2Cache["psindexes"][N] := S;
    vprintf GL2,2: "Extended primitive GL2 similarity index table to include N=%o in %.3os\n", N, Realtime()-timer; 
    return S;
end intrinsic;

// this doesn't seem to be worth using -- it doesn't help the enum/cc algorithms and for the action/gl2action algorithms computing the permutation rep is the limiting factor.
// it makes the signatures shorter, but since we only store hashes anyway this isn't a huge benefit, and it requires precomputation for every scalar subgroup to be efficient.
intrinsic GL2ScalarPrimitiveSimilarityIndexes(Z::GrpMat) -> SetIndx[RngIntElt]
{ Indices of non-scalar primitive similarity classes that are minimal up to the action of the specified scalar subgroup Z. }
    N := #BaseRing(Z); if not IsFinite(N) then return {@ 1 @}; end if;
    if Degree(Z) eq 1 then Z := sub<GL(2,BaseRing(Z))|[[g[1][1],0,0,g[1][1]]:g in Generators(Z)]>; end if;
    S := GL2PrimitiveSimilarityReps(N); ind := GL2PrimitiveSimilarityClassIndexMap(N);
    I := GL2PrimitiveSimilarityIndexes(N); B := [true:i in I];
    for i:=1 to #I do if B[i] then if isscalar(S[i]) then B[i] := false; else for z in Z do j := ind(z*S[i]); if j gt i then B[j] := false; end if; end for; end if; end if; end for;
    return IndexedSet([I[i]:i in [1..#I]|B[i]]);
end intrinsic;

intrinsic SL2PrimitiveSimilarityIndexes(N::RngIntElt:NoCache:=false,NoFile:=false) -> SetIndx[RngIntElt]
{ Indices of the entries in the ordered list of similarity/conjugacy classes of SL(2,Integers(N)) returned by SL2SimilarityClasses/GL2ConjugacyClasses of classes that are 
  the minimal representatives of their division (the union of conjugacy classes whose representative generate the same cyclic group, up to conjugacy). }
    if N eq 1 then return [1]; end if;
    ZZ := Integers();
    if not NoCache and IsDefined(ZZ`SL2Cache["psindexes"],N) then return ZZ`SL2Cache["psindexes"][N]; end if;
    if not NoFile and SL2LoadPrimitiveSimilarityIndexes(N) then return ZZ`SL2Cache["psindexes"][N]; end if;
    timer := Realtime();
    C := SL2SimilarityClasses(N); ind := SL2SimilarityClassIndexMap(N);
    I := []; J := [true : i in [1..#C]];
    for i:=1 to #C do
        if J[i] then
            Append(~I,i);
            g := C[i][2]; n := Order(g); m := 1; h := g;
            for m:=2 to n-1 do h *:= g; if GCD(m,n) eq 1 then J[ind(h)] := false; end if; end for;
        end if;
    end for;
    S := IndexedSet(I); ZZ`SL2Cache["psindexes"][N] := S;
    vprintf GL2,2: "Extended primitive SL2 similarity index table to include N=%o in %.3os\n", N, Realtime()-timer; 
    return S;
end intrinsic;

intrinsic GL2PrimitiveSimilaritySet(N::RngIntElt) -> SetIndx[SeqEnum[SeqEnum[RngIntElt]]]
{ Sequence of tuples <inv,rep> corresponding to conjugacy classes of cyclic subgroups of GL(2,Integers(N)) of prime power order sorted by minimal similarity invariant of a generator. }
    ZZ := Integers();
    if IsDefined(ZZ`GL2Cache["pssets"],N) then return ZZ`GL2Cache["pssets"][N]; end if;
    S := {@ S[i] : i in GL2PrimitiveSimilarityIndexes(N) @} where S:=GL2SimilaritySet(N);
    ZZ`GL2Cache["pssets"][N] := S;
    return S;
end intrinsic;

intrinsic SL2PrimitiveSimilaritySet(N::RngIntElt) -> SetIndx[SeqEnum[SeqEnum[RngIntElt]]]
{ Sequence of tuples <inv,rep> corresponding to conjugacy classes of cyclic subgroups of GL(2,Integers(N)) of prime power order sorted by minimal similarity invariant of a generator. }
    ZZ := Integers();
    if IsDefined(ZZ`SL2Cache["pssets"],N) then return ZZ`SL2Cache["pssets"][N]; end if;
    S := {@ S[i] : i in SL2PrimitiveSimilarityIndexes(N) @} where S:=SL2SimilaritySet(N);
    ZZ`SL2Cache["pssets"][N] := S;
    return S;
end intrinsic;

intrinsic GL2PrimitiveSimilarityClasses(N::RngIntElt) -> SeqEnum[Tup]
{ Sequence of tuples <inv,rep> corresponding to conjugacy classes of cyclic subgroups of GL(2,Integers(N)) of prime power order sorted by minimal similarity invariant of a generator. }
    ZZ := Integers();
    if IsDefined(ZZ`GL2Cache["psclasses"],N) then return ZZ`GL2Cache["psclasses"][N]; end if;
    S := [ S[i] : i in GL2PrimitiveSimilarityIndexes(N) ] where S:=GL2SimilarityClasses(N);
    ZZ`GL2Cache["psclasses"][N] := S;
    return S;
end intrinsic;

intrinsic SL2PrimitiveSimilarityClasses(N::RngIntElt) -> SeqEnum[Tup]
{ Sequence of tuples <inv,rep> corresponding to conjugacy classes of cyclic subgroups of GL(2,Integers(N)) of prime power order sorted by minimal similarity invariant of a generator. }
    ZZ := Integers();
    b, S := IsDefined(ZZ`SL2Cache["psclasses"],N);
    if b then return S; end if;
    S := [ S[i] : i in SL2PrimitiveSimilarityIndexes(N) ] where S:=SL2SimilarityClasses(N);
    ZZ`SL2Cache["psclasses"][N] := S;
    return S;
end intrinsic;

intrinsic GL2SimilarityCounts(N::RngIntElt) -> SeqEnum[RngIntElt]
{ returns an array T with T[i] counting elements of GL(2,Z/NZ) with the ith similarity invariant (i is an index into GL2SimilaritySet(N)). }
    ZZ := Integers();
    if IsDefined(ZZ`GL2Cache["scnts"],N) then return ZZ`GL2Cache["scnts"][N]; end if;
    S := [&*[ZZ|sslen(A[j][1],A[j][2],S[i][j]):j in [1..#A]]: i in [1..#S]] where A := Factorization(N) where S:=GL2SimilaritySet(N);
    ZZ`GL2Cache["scnts"][N] := S;
    return S; 
end intrinsic;

intrinsic SL2SimilarityCounts(N::RngIntElt) -> SeqEnum[RngIntElt]
{ returns an array T with T[i] counting elements of SL(2,Z/NZ) with the ith similarity invariant (i is an index into GL2SimilaritySet(N)). }
    ZZ := Integers();
    if IsDefined(ZZ`SL2Cache["scnts"],N) then return ZZ`SL2Cache["scnts"][N]; end if;
    S := [&*[ZZ|sslen(A[j][1],A[j][2],S[i][j]):j in [1..#A]]: i in [1..#S]] where A := Factorization(N) where S:=SL2SimilaritySet(N);
    ZZ`SL2Cache["scnts"][N] := S;
    return S; 
end intrinsic;

intrinsic GL2PrimitiveSimilarityCounts(N::RngIntElt) -> SeqEnum[RngIntElt]
{ returns an array T with T[i] counting elements of GL(2,Z/NZ) with the ith primitive similarity invariant (i is an index into GL2PrimitiveSimilaritySet(N)). }
    ZZ := Integers();
    if IsDefined(ZZ`GL2Cache["pscnts"],N) then return ZZ`GL2Cache["pscnts"][N]; end if;
    S := [ S[i] : i in GL2PrimitiveSimilarityIndexes(N) ] where S:=GL2SimilarityCounts(N);
    ZZ`GL2Cache["pscnts"][N] := S;
    return S; 
end intrinsic;

intrinsic SL2PrimitiveSimilarityCounts(N::RngIntElt) -> SeqEnum[RngIntElt]
{ returns an array T with T[i] counting elements of GL(2,Z/NZ) with the ith primitive similarity invariant (i is an index into SL2PrimitiveSimilaritySet(N)). }
    ZZ := Integers();
    if IsDefined(ZZ`SL2Cache["pscnts"],N) then return ZZ`SL2Cache["pscnts"][N]; end if;
    S := [ S[i] : i in SL2PrimitiveSimilarityIndexes(N) ] where S:=SL2SimilarityCounts(N);
    ZZ`SL2Cache["pscnts"][N] := S;
    return S; 
end intrinsic;

intrinsic GL2ConjugacyClassCount(N::RngIntElt) -> RngIntElt
{ Returns the number of conjugacy/similarity classes of elements of GL(2,Z/NZ). }
    require N gt 0: "N must be positive";
    return &*[Integers()|a[1]^(2*a[2])-a[1]^(a[2]-1):a in A] where A:=Factorization(N);
end intrinsic;

intrinsic GL2SimilarityClassCount(N::RngIntElt) -> RngIntElt
{ Returns the number of conjugacy/similarity classes of elements of GL(2,Z/NZ). }
    return GL2ConjugacyClassCount(N);
end intrinsic;

intrinsic SL2SimilarityClassCount(N::RngIntElt) -> RngIntElt
{ Returns the number of GL2-conjugacy/similarity classes of elements of SL(2,Z/NZ). }
    return #SL2SimilaritySet(N);
end intrinsic;

intrinsic GL2PrimitiveSimilarityClassCount(N::RngIntElt) -> RngIntElt
{ Returns the number of conjugacy/similarity classes of elements of GL(2,Z/NZ). }
    return #GL2PrimitiveSimilarityIndexes(N);
end intrinsic;

intrinsic SL2PrimitiveSimilarityClassCount(N::RngIntElt) -> RngIntElt
{ Returns the number of GL2-conjugacy/similarity classes of elements of SL(2,Z/NZ). }
    return #SL2PrimitiveSimilarityIndexes(N);
end intrinsic;

/*
    The basic fact we use to compute similarity/conjugacy counts #(H cap g^G) using the permutation rep pi for [H\G] comes from (1.2) of https://arxiv.org/abs/2104.01956

    chi_H(g) := #Fix(pi(g)) = N_G(<g>)/#H * #{K^g subset H:g in G} = Z_G(g)/#H * #(g^G cap H) = (#G/#g^G)/#H * #(g^G cap H) = [G:H]*#(g^G cap H)/#g^G

    This implies #(g^G cap H) = #Fix(pi(g))*g^G / [G:H]
*/

intrinsic GL2SimilarityCounts(H::GrpMat:Algorithm:="default",Primitive:=false,Sparse:=false) -> SeqEnum
{ returns an array T with T[i] counting elements of H with similarity invariant index i (into GL2SimilaritySet(N) or GL2PrimitiveSimilaritySet(N), depending on Primitive flag).
  If Sparse is true, only nonzero counts are returned and each list elment is a pair [n,i] such that the ith similarity invariant occurs n times in H.  }
    require Algorithm in gl2permrepalgs: "Invalid value for Algorithm use one of " cat sprint(gl2permrepalgs);
    require not assigned H`SL: "H should be a subgroup of GL2 that is not be marked as a subgroup of SL2 (even if it happens to be contained in SL2).";
    N := #BaseRing(H); if not IsFinite(N) then assert H eq gl2N1; return Sparse select [[1,1]] else [1]; end if;
    if Algorithm eq "default" then Algorithm := gl2permrepalg(H); end if;
    if Algorithm eq "enum" or Algorithm eq "cc" then
        ind := Primitive select GL2PrimitiveSimilarityClassIndexMap(N) else GL2SimilarityClassIndexMap(N);
        cnts := [0:i in [1..n]] where n := Primitive select GL2PrimitiveSimilarityClassCount(N) else GL2SimilarityClassCount(N);
        if Algorithm eq "enum" then
            for h in H do i := ind(h); if i gt 0 then cnts[i] +:= 1; end if; end for;
        else
            for c in ConjugacyClasses(H) do i := ind(c[3]); if i gt 0 then cnts[i] +:= c[2]; end if; end for;
        end if;
    else
        if Primitive then C := GL2PrimitiveSimilarityCounts(N); S := GL2PrimitiveSimilarityReps(N);
        else C := GL2SimilarityCounts(N); S := GL2SimilarityReps(N); end if;
        n := GL2Index(H);
        // There is a very difficult to reproduce magma bug (as of 2.27-8) that will occasionally cause ExactQuotient to fail due to a bogus map returned by CosetAction
        // Re-executing the exact same line will often fix the problem
        try
        cnts := [ExactQuotient(C[i]*#Fix(pi(S[i])),n):i in [1..#C]] where pi := Algorithm eq "action" select CosetAction(GL2Ambient(N),H) else GL2PermutationRepresentation(H);
        catch e
            print "ExactQuotient failed in GL2SimilarityCounts",N,sprint(GL2Generators(H)),Algorithm,Primitive,Sparse,n;
            cnts := [C[i]*#Fix(pi(S[i]))/n:i in [1..#C]] where pi := Algorithm eq "action" select CosetAction(GL2Ambient(N),H) else GL2PermutationRepresentation(H);
            if not &and[Denominator(c) eq 1: c in cnts] then
                print "Retry failed:", sprint(cnts);
                error e;
            end if;
            cnts := [Numerator(c):c in C];
        end try;
    end if;
    return Sparse select [[i,cnts[i]]:i in [1..#cnts]|cnts[i] ne 0] else cnts;
end intrinsic;

intrinsic GL2SimilarityCount(H::GrpMat,g::GrpMatElt:Algorithm:="default") -> RngIntElt
{ Returns the number of elements in H that are GL2-conjugate to g. }
    require Algorithm in gl2permrepalgs: "Invalid value for Algorithm use one of " cat sprint(gl2permrepalgs);
    require not assigned H`SL: "H should be a subgroup of GL2 that is not be marked as a subgroup of SL2 (even if it happens to be contained in SL2).";
    N := #BaseRing(H); if not IsFinite(N) then assert H eq gl2N1 and Order(g) eq 1; return 1; end if;
    if Algorithm eq "default" then Algorithm := gl2permrepalg(H); end if;
    if Algorithm eq "enum" or Algorithm eq "cc" then
        inv := GL2SimilarityInvariant(g); cnt := 0;
        if Algorithm eq "enum" then
            for h in H do if GL2SimilarityInvariant(h) eq inv then cnt +:=1; end if; end for;
        else
            for c in ConjugacyClasses(H) do if GL2SimilarityInvariant(c[3]) eq inv then cnt +:= c[2]; end if; end for;
        end if;
    else
        n := GL2Index(H); m := GL2SimilarityClassSize(g);
        try
            cnt := ExactQuotient(m*#Fix(pi(g)),n) where pi := Algorithm eq "action" select CosetAction(GL2Ambient(N),H) else GL2PermutationRepresentation(H);
        catch e
            print "ExactQuotient failed in GL2SimilarityCount",N,sprint(GL2Generators(H)),Algorithm;
            cnt := ExactQuotient(m*#Fix(pi(g)),n) where pi := Algorithm eq "action" select CosetAction(GL2Ambient(N),H) else GL2PermutationRepresentation(H);
            if Denominator(cnt) ne 1 then print "Retry failed:", sprint(cnt); error e; end if;
            cnt := Numerator(cnt);
        end try;
    end if;
    return cnt;
end intrinsic;

/*
  For SL2 we always use the enum or cc algorithms by default because we cannot in general use the perm rep [H\SL2] to compute similarity counts.
  However, the action approach will work if H is the intersection of some full determinant subgroup with SL2 (we need to know that SL2-conjugacy counts in H
  are GL2-invarian).  We trust the caller to know that this holds whenever the action algorithm is specified but never assume or attempt to determine this.
*/
intrinsic SL2SimilarityCounts(H::GrpMat:Primitive:=false,Algorithm:="default",Sparse:=false) -> SeqEnum[RngIntElt]
{ Returns an array T with T[i] counting elements of H with similarity invariant index i (into SL2SimilaritySet(N) or SL2PrimitiveSimilaritySet(N), depending on Primitive flag).
  If Sparse is true, only nonzero counts are returned and a second parameter giving the corresponding index of each count is also returned.
  WARNING: Do not specify the action algorithm unless you know H is the intersection of a full determinant subgroup with SL2. }
    require Algorithm in sl2permrepalgs: "Invalid value for Algorithm use one of " cat sprint(sl2permrepalgs);
    require assigned H`SL: "H should be a subgroup of SL2 that is marked as a subgroup of SL2.";
    N := #BaseRing(H); if not IsFinite(N) then assert H eq sl2N1; return Sparse select [[1,1]] else [1]; end if;
    if not assigned H`Order then H`Order := SL2Order(H); end if;
    if Algorithm eq "default" then Algorithm := sl2permrepalg(H); end if;
    if Algorithm eq "defaultoraction" then Algorithm := sl2permrepalg(H); if Algorithm eq "cc" then Algorithm := "action"; end if; end if;
    if Algorithm eq "enum" or Algorithm eq "cc" then
        ind := Primitive select SL2PrimitiveSimilarityClassIndexMap(N) else SL2SimilarityClassIndexMap(N);
        cnts := [0:i in [1..n]] where n := Primitive select SL2PrimitiveSimilarityClassCount(N) else SL2SimilarityClassCount(N);
        if Algorithm eq "enum" then
            for h in H do i := ind(h); if i gt 0 then cnts[i] +:= 1; end if; end for;
        else
            for c in ConjugacyClasses(H) do i := ind(c[3]); if i gt 0 then cnts[i] +:= c[2]; end if; end for;
        end if;
    else
        if Primitive then C := SL2PrimitiveSimilarityCounts(N); S := SL2PrimitiveSimilarityReps(N);
        else C := SL2SimilarityCounts(N); S := SL2SimilarityReps(N); end if;
        n := SL2Index(H);
        // For the argument that this works when H is the SL2-intersection of a full-det subgroup of GL2 see GL2PermutationRepresentation
        cnts := [ExactQuotient(C[i]*#Fix(pi(S[i])),n):i in [1..#C]] where pi := CosetAction(SL2Ambient(N),H);
    end if;
    return Sparse select [[i,cnts[i]]:i in [1..#cnts]|cnts[i] ne 0] else cnts;
end intrinsic;

function filtcon(H,L)
    if #L eq 1 then return L; end if;
    X := IndexedSet(L);  LL := [];
    while #X gt 0 do Append(~LL,X[1]); X diff:= Conjugates(H,X[1]); end while;
    return LL;
end function;

intrinsic GL2PrimitiveSimilarityLists(H::GrpMat:Algorithm:="default") -> SeqEnum[RngIntElt], SeqEnum[RngIntElt], UserProgram
{ Returns a list I of the primitive similarity indices i that occur in H (the i for which H contains a GL2-conjugate of GL2PrimitiveSimilarityReps(H`level)[i]),
  along with a function that given i returns a list of H-conjugacy class reps of the elements in H in the similarity class I[i] }
    require Algorithm in gl2permrepalgs: "Invalid value for Algorithm use one of " cat sprint(gl2permrepalgs);
    require not assigned H`SL: "H should be a subgroup of GL2 that is not be marked as a subgroup of SL2 (even if it happens to be contained in SL2).";
    N := #BaseRing(H); require IsFinite(N): "H must be defined over a finite ring.";
    if Algorithm eq "default" then Algorithm := gl2permrepalg(H); end if;
    if Algorithm eq "enum" or Algorithm eq "cc" then
        ind := GL2PrimitiveSimilarityClassIndexMap(N);
        if Algorithm eq "enum" then
            S := [h : h in H]; T := [ind(h) : h in S];
            J := [j : j in [1..#T]|T[j] gt 0]; S := S[J]; T := T[J]; M := Multiset(T);
            I := Sort([i:i in I]) where I := Set(M);
            return I, func<i|filtcon(H,[S[j] : j in [1..#S] | T[j] eq i])>;
        else
            C := ConjugacyClasses(H); T := [ind(c[3]) : c in C];
            J := [j : j in [1..#T]|T[j] gt 0]; S := [C[j][3]:j in J]; M := {* T[j]^^C[j][2] : j in J *}; T := T[J];
            I := Sort([i:i in I]) where I := Set(M);
            return I, func<i|[S[j] : j in [1..#S] | T[j] eq i]>;
        end if;
    else
        C := GL2PrimitiveSimilarityCounts(N); R := GL2PrimitiveSimilarityReps(N); G := GL2Ambient(N);
        T,phi := RightTransversal(G,H);
        pi := hom<G->S|[<g,perm(g)>:g in Generators(G)]> where perm := func<g|S![Index(T,phi(t*g)):t in T]> where S:=Sym(#T);
        I := [i : i in [1..#C] | #Fix(pi(R[i])) gt 0];
        return I, func<i|filtcon(H,[T[j]*h*T[j]^(-1):j in Fix(pi(h))]) where h:=R[i]>;
    end if;
end intrinsic;

intrinsic SL2PrimitiveSimilarityLists(H::GrpMat:Algorithm:="default",Counts:=false) -> SeqEnum[RngIntElt], SeqEnum[RngIntElt], UserProgram
{ Returns a list I of the primitive similarity indices i that occur in H (the positive integer i for which H contains a GL2-conjugate of SL2PrimitiveSimilarityReps(H`level)[i]) and a function that given i in I returns a list of the elements in H in this similarity class.  WARNING: Do not specify the action algorithm unless you know H extends to a full determinant subgroup of GL2. }
    require Algorithm in sl2permrepalgs: "Invalid value for Algorithm use one of " cat sprint(sl2permrepalgs);
    require assigned H`SL: "H should be a subgroup of SL2 that is marked as a subgroup of SL2.";
    N := #BaseRing(H); require IsFinite(N): "H must be defined over a finite ring.";
    if not assigned H`Order then H`Order := SL2Order(H); end if;
    if Algorithm eq "default" then Algorithm := sl2permrepalg(H); end if;
    if Algorithm eq "enum" or Algorithm eq "cc" then
        ind := SL2PrimitiveSimilarityClassIndexMap(N);
        if Algorithm eq "enum" then
            S := [h : h in H]; T := [ind(h) : h in S];
            J := [j : j in [1..#T]|T[j] gt 0]; S := S[J]; T := T[J];
            I := Sort([i:i in I]) where I := Set(T);
            return I, func<i|filtcon(H,[S[j] : j in [1..#S] | T[j] eq i])>;
        else
            C := ConjugacyClasses(H); T := [ind(c[3]) : c in C];
            J := [j : j in [1..#T]|T[j] gt 0]; S := [C[j][3]:j in J]; M := {* T[j]^^C[j][2] : j in J *}; T := T[J];
            I := Sort([i:i in I]) where I := Set(T);
            return I, func<i|[S[j] : j in [1..#S] | T[j] eq i]>;
        end if;
    else
        C := SL2PrimitiveSimilarityCounts(N); R := SL2PrimitiveSimilarityReps(N); G := GL2Ambient(N);
        T,phi := RightTransversal(G,H);   // This is going to be slow but there does not seem to be an efficient way to do this using the SL2 permutation rep
        pi := hom<G->S|[<g,perm(g)>:g in Generators(G)]> where perm := func<g|S![Index(T,phi(t*g)):t in T]> where S:=Sym(#T);
        I := [i : i in [1..#C] | #Fix(pi(R[i])) gt 0];
        return I, func<i|filtcon(H,[T[j]*h*T[j]^(-1):j in Fix(pi(h))]) where h:=R[i]>;
    end if;
end intrinsic;

intrinsic GL2SimilarityIndexes(H::GrpMat : Algorithm:="default",Primitive:=false) -> SeqEnum[RngIntElt]
{ List of the indexes (into GL2SimilaritySet(N) or GL2PrimitiveSimilaritySet(N), depending on Primitive flag) of similarity classes arising in H. }
    return [i:i in [1..#C]|C[i] gt 0] where C := GL2SimilarityCounts(H:Algorithm:=Algorithm,Primitive:=Primitive);
end intrinsic;

intrinsic SL2SimilarityIndexes(H::GrpMat : Algorithm:="default",Primitive:=false) -> SeqEnum[RngIntElt]
{ List of the indexes (into SL2SimilaritySet(N) or SL2PrimitiveSimilaritySet(N), depending on Primitive flag) of similarity classes arising in H.
  Warning: Do not specify the action algorithm unless you know H is the intersection of a full determinant subgroup with SL2. }
    return [i:i in [1..#C]|C[i] gt 0] where C := SL2SimilarityCounts(H:Algorithm:=Algorithm,Primitive:=Primitive);
end intrinsic;

intrinsic GL2SimilaritySet(H::GrpMat : Algorithm:="default",Primitive:=false) -> SetEnum[SeqEnum[SeqEnum[RngIntElt]]]
{ Set of similarity invariants arising in H. }
    require Algorithm in gl2permrepalgs: "Invalid value for Algorithm use one of " cat sprint(gl2permrepalgs);
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2 (even if it lies in SL2).";
    N := #BaseRing(H); if not IsFinite(N) then assert #H eq 1; return {[]}; end if;
    if Algorithm eq "default" then Algorithm := gl2permrepalg(H); end if;
    if Algorithm eq "enum" then
        return Primitive
            select { S[i] : i in I | i ne 0 } where S := GL2PrimitiveSimilaritySet(N) where I := { ind(h): h in H } where ind := GL2PrimitiveSimilarityClassIndexMap(N)
            else { inv(h) : h in H } where inv := GL2SimilarityClassMap(N);
    elif Algorithm eq "cc" then
        C := ConjugacyClasses(H);
        return Primitive
            select { S[i] : i in I | i ne 0 } where S := GL2PrimitiveSimilaritySet(N) where I := { ind(c[3]): c in C } where ind := GL2PrimitiveSimilarityClassIndexMap(N)
            else { inv(c[3]) : c in C } where inv := GL2SimilarityClassMap(N);
    else
        S := Primitive select GL2PrimitiveSimilarityClasses(N) else GL2SimilarityClasses(N);
        return { S[i][1] : i in [1..#S] | #Fix(pi(S[i][2])) gt 0 } where pi := Algorithm eq "action" select CosetAction(GL2Ambient(N),H) else GL2PermutationRepresentation(H);
    end if;
end intrinsic;

intrinsic SL2SimilaritySet(H::GrpMat : Algorithm:="default",Primitive:=false) -> SetEnum[SeqEnum[SeqEnum[RngIntElt]]]
{ Set of similarity invariants arising in H. Warning: Do not specify the action algorithm unless you know H is the intersection of a full determinant subgroup with SL2. }
    require Algorithm in sl2permrepalgs: "Invalid value for Algorithm use one of " cat sprint(sl2permrepalgs);
    require assigned H`SL: "H should be a subgroup of SL2 that is marked as a subgroup of SL2.";
    N := #BaseRing(H); if not IsFinite(N) then assert #H eq 1; return {[]}; end if;
    if Algorithm eq "default" then Algorithm := sl2permrepalg(H); end if;
    if Algorithm eq "enum" then
        return Primitive
            select { S[i] : i in I | i ne 0 } where S := SL2PrimitiveSimilaritySet(N) where I := { ind(h): h in H } where ind := SL2PrimitiveSimilarityClassIndexMap(N)
            else { inv(h) : h in H } where inv := SL2SimilarityClassMap(N);
    elif Algorithm eq "cc" then
        C := ConjugacyClasses(H);
        return Primitive
            select { S[i] : i in I | i ne 0 } where S := SL2PrimitiveSimilaritySet(N) where I := { ind(c[3]): c in C } where ind := SL2PrimitiveSimilarityClassIndexMap(N)
            else { inv(c[3]) : c in C } where inv := SL2SimilarityClassMap(N);
    else
        S := Primitive select SL2PrimitiveSimilarityClasses(N) else SL2SimilarityClasses(N);
        return { S[i][1] : i in [1..#S] | #Fix(pi(S[i][2])) gt 0 } where pi := CosetAction(SL2Ambient(N),H);
    end if;
end intrinsic;

intrinsic GL2SimilarityMultiset(H::GrpMat:Algorithm:="default",Primitive:=false) -> SetMulti[SeqEnum[SeqEnum[RngIntElt]]]
{ Multiset of similarity invariants arising in H. }
    require not assigned H`SL: "H should be a subgroup of GL2 that is not marked as a subgroup of SL2 (even if it lies in SL2).";
    require Algorithm in gl2permrepalgs: "Invalid value for Algorithm use one of " cat sprint(gl2permrepalgs);
    N := #BaseRing(H); if not IsFinite(N) then assert #H eq 1; return {*[]*}; end if;
    C := GL2SimilarityCounts(H:Algorithm:=Algorithm,Primitive:=Primitive);
    S := Primitive select GL2PrimitiveSimilaritySet(N) else GL2SimilaritySet(N);
    return {* S[i]^^C[i] : i in [1..#C] | C[i] ne 0 *}; 
end intrinsic;

// For SL2 we just use the enum and cc algorithms.  We would have to use the GL2-action in the action algorithms and this will very rarely be faster (and generally much slower)
intrinsic SL2SimilarityMultiset(H::GrpMat : Algorithm:="default",Primitive:=false) -> SetMulti[SeqEnum[SeqEnum[RngIntElt]]]
{ Multiset of similarity invariants arising in H. Warning: Do not specify the action algorithm unless you know H is the intersection of a full determinant subgroup with SL2. }
    require assigned H`SL: "H should be a subgroup of SL2 that is marked as a subgroup of SL2.";
    require Algorithm in sl2permrepalgs: "Invalid value for Algorithm use one of " cat sprint(sl2permrepalgs);
    N := #BaseRing(H); if not IsFinite(N) then assert #H eq 1; return {*[]*}; end if;
    C := SL2SimilarityCounts(H:Algorithm:=Algorithm,Primitive:=Primitive);
    S := Primitive select SL2PrimitiveSimilaritySet(N) else SL2SimilaritySet(N);
    return {* S[i]^^C[i] : i in [1..#C] | C[i] ne 0 *}; 
end intrinsic;

intrinsic GL2PrimitiveSimilarityCounts(H::GrpMat : Algorithm:="default", Sparse:=false) -> SeqEnum[RngIntElt]
{ Returns an array T with T[i] counting elements of H with primitive similarity invariant index i. }
    return GL2SimilarityCounts(H:Algorithm:=Algorithm,Primitive:=true,Sparse:=Sparse);
end intrinsic;

intrinsic SL2PrimitiveSimilarityCounts(H::GrpMat : Algorithm:="default", Sparse:=false) -> SeqEnum[RngIntElt]
{ Returns an array T with T[i] counting elements of H with primitive similarity invariant index i.
  Warning: Do not specify the action algorithm unless you know H is the intersection of a full determinant subgroup with SL2.  }
    return SL2SimilarityCounts(H:Algorithm:=Algorithm,Primitive:=true,Sparse:=Sparse);
end intrinsic;

intrinsic GL2PrimitiveSimilarityIndexes(H::GrpMat : Algorithm:="default") -> SeqEnum[RngIntElt]
{ List of indexes into GL2PrimitiveSimilaritySet(N) of the primtive similarity classes arising in H. }
    return GL2SimilarityIndexes(H:Algorithm:=Algorithm,Primitive:=true);
end intrinsic;

intrinsic SL2PrimitiveSimilarityIndexes(H::GrpMat : Algorithm:="default") -> SeqEnum[RngIntElt]
{ List of indexes into SL2PrimitiveSimilaritySet(N) of the primtive similarity classes arising in H.
  Warning: Do not specify the action algorithm unless you know H is the intersection of a full determinant subgroup with SL2. }
    return SL2SimilarityIndexes(H:Algorithm:=Algorithm,Primitive:=true);
end intrinsic;

intrinsic GL2PrimitiveSimilaritySet(H::GrpMat : Algorithm:="default") -> SetEnum[SeqEnum[SeqEnum[RngIntElt]]]
{ Set of primitive similarity invariants arising in H. }
    return GL2SimilaritySet(H:Algorithm:=Algorithm,Primitive:=true);
end intrinsic;

intrinsic SL2PrimitiveSimilaritySet(H::GrpMat : Algorithm:="default") -> SetEnum[SeqEnum[SeqEnum[RngIntElt]]]
{ Set of primitive similarity invariants arising in H. Warning: Do not specify the action algorithm unless you know H is the intersection of a full determinant subgroup with SL2. }
    return SL2SimilaritySet(H:Algorithm:=Algorithm,Primitive:=true);
end intrinsic;

intrinsic GL2PrimitiveSimilarityMultiset(H::GrpMat : Algorithm:="default") -> SetMulti[SeqEnum[SeqEnum[RngIntElt]]]
{ Multiset of primitive similarity invariants arising in H. }
    return GL2SimilarityMultiset(H:Algorithm:=Algorithm,Primitive:=true);
end intrinsic;

intrinsic SL2PrimitiveSimilarityMultiset(H::GrpMat : Algorithm:="default") -> SetMulti[SeqEnum[SeqEnum[RngIntElt]]]
{ Multiset of primitive similarity invariants arising in H. Warning: Do not specify the action algorithm unless you know H is the intersection of a full determinant subgroup with SL2. }
    return GL2SimilarityMultiset(H:Algorithm:=Algorithm,Primitive:=true);
end intrinsic;

/*** GL2 orbit/kummer/isogeny/gassmann signatures and torsion/isogeny degrees ***/

// Magma wants matrices to act on row vectors from the right, so when computing orbits we transpose
// to remain consistent with our convention that matrices act on column vectors from the left.

gl2osig := func<H|lmset({*[ord(o[1]),#o]:o in Orbits(H)|o ne {RSpace(H)!0}*})
                  where H := GL2Transpose(H) where ord := func<v|Min([n:n in D|n*v eq 0*v])> where D:=Divisors(#BaseRing(H))>;
sl2osig := gl2osig;
gl2ksig := func<H|lmset({*[ord(o[1]),ExactQuotient(#o,#{o[1],-o[1]})]:o in Orbits(H)|o ne {RSpace(H)!0}*})
                  where H := GL2Transpose(GL2IncludeNegativeOne(H)) where ord := func<v|Min([n:n in D|n*v eq 0*v])> where D:=Divisors(#BaseRing(H))>;
function gl2isig(H) // for isogney orbits we don't need to transpose
     S := {sub<RSpace(H)|[i,j]>:i in D,j in [0..N-1]} where D:=Divisors(N) where N := #BaseRing(H); X :={**};
     while #S gt 0 do v := Random(S); T := v^H; Include(~X,[#v,#T]); S diff:= T; end while;
     return lmset(Exclude(X,[1,1]));
end function;
gl2csig := func<H|lmset({* csig(c) : c in C *}) where C := ConjugacyClasses(H) where csig := func<c|[c[1],Integers()!Determinant(c[3]),Integers()!Trace(c[3]),c[2]]>>;
gl2gsig := func<H:old:=false|old select llmset(GL2SimilarityMultiset(H)) else GL2PrimitiveSimilarityCounts(H)>;
sl2gsig := func<H|SL2PrimitiveSimilarityCounts(H)>;

intrinsic GL2OrbitSignature(H::GrpMat) -> SeqEnum[SeqEnum[RngIntElt]]
{ The orbit signature of H (the ordered list of triples [e,s,m] where m is the number of non-trivial left H-orbits of (Z/NZ)^2 of size s and exponent e). }
    if assigned H`SL then return SL2OrbitSignature(H); end if;
    return N eq 1 select [Universe([[1]])|] else gl2osig(H) where N,H := GL2Level(H);
end intrinsic;

intrinsic GL2OrbitSignature(H::GrpMat, N::RngIntElt) -> SeqEnum[SeqEnum[RngIntElt]]
{ The multiset of orbits of H acting on points of order N. }
    if assigned H`SL then return SL2OrbitSignature(H,N); end if;
    return N eq 1 select [Universe([[1]])|] else gl2osig(GL2Project(H,N));
end intrinsic;

intrinsic SL2OrbitSignature(H::GrpMat) -> SeqEnum[SeqEnum[RngIntElt]]
{ The orbit signature of H (the ordered list of triples [e,s,m] where m is the number of non-trivial left H-orbits of (Z/NZ)^2 of size s and exponent e). }
    return N eq 1 select [Universe([[1]])|] else sl2osig(H) where N,H := SL2Level(H);
end intrinsic;

intrinsic SL2OrbitSignature(H::GrpMat, N::RngIntElt) -> SeqEnum[SeqEnum[RngIntElt]]
{ The multiset of orbits of H acting on points of order N. }
    return N eq 1 select [Universe([[1]])|] else sl2osig(SL2Project(H,N));
end intrinsic;

intrinsic GL2KummerSignature(H::GrpMat) -> SeqEnum[SeqEnum[RngIntElt]]
{ The divpoly signature of H (the ordered list of triples [e,s,m] where m is the number of left H-orbits of (Z/NZ)^2/<-1> of size s and exponent e, giving the factorization pattern of the N-division polynomial.). }
    return N eq 1 select [Universe([[1]])|] else gl2ksig(H) where N,H := GL2Level(H);
end intrinsic;

intrinsic GL2KummerSignature(H::GrpMat, N::RngIntElt) -> SeqEnum[SeqEnum[RngIntElt]]
{ The divpoly signature of H (the ordered list of triples [e,s,m] where m is the number of left H-orbits of (Z/NZ)^2/<-1> of size s and exponent e, giving the factorization pattern of the N-division polynomial.). }
    return N eq 1 select [Universe([[1]])|] else gl2ksig(GL2Project(H,N));
end intrinsic;

intrinsic GL2IsogenySignature(H::GrpMat) -> SeqEnum[SeqEnum[RngIntElt]]
{ The isogeny signature of the subgroup H of GL(2,Z/NZ) (the ordered list of triples [e,s,m] where m is the number of left H-orbits of cyclic submodules of (Z/NZ)^2 of size s and degree e). }
    return N eq 1 select [Universe([[1]])|] else gl2isig(H) where N,H := GL2Level(H);
end intrinsic;

intrinsic GL2IsogenySignature(H::GrpMat, N::RngIntElt) -> SeqEnum[SeqEnum[RngIntElt]]
{ The isogeny signature of the subgroup H of GL(2,Z/NZ) (the ordered list of triples [e,s,m] where m is the number of left H-orbits of cyclic submodules of (Z/NZ)^2 of size s and degree e). }
    return N eq 1 select [Universe([[1]])|] else gl2isig(GL2Project(H,N));
end intrinsic;

intrinsic GL2ClassSignature(H::GrpMat) -> SeqEnum[SeqEnum[RngIntElt]]
{ The orbit signature of H (the ordered list of triples [e,s,m] where m is the number of non-trivial left H-orbits of (Z/NZ)^2 of size s and exponent e). }
    return N eq 1 select [Universe([[1]])|] else gl2csig(H) where N,H := GL2Level(H);
end intrinsic;

intrinsic GL2GassmannSignature(H::GrpMat:old:=false) -> SeqEnum[Tup]
{ Sorted list of pairs <r,m> where r is a similarity invariant of GL_2(N) and m > 0 is its multiplicity in H; this uniquely identifies the Gassmann equivalence class of H as a subgroup of GL_2(N). }
    if assigned H`SL then return SL2GassmannSignature(H); end if;
    return N eq 1 select (old select [Universe([[1]])|] else [Universe([1])|]) else gl2gsig(H:old:=old) where N,H := GL2Level(H);
end intrinsic;

intrinsic SL2GassmannSignature(H::GrpMat) -> SeqEnum[Tup]
{ Sorted list of pairs <r,m> where r is a similarity invariant of GL_2(N) and m > 0 is its multiplicity in H; this uniquely identifies the Gassmann equivalence class of H as a subgroup of GL_2(N). }
    return N eq 1 select [Universe([1])|] else sl2gsig(H) where N,H := SL2Level(H);
end intrinsic;

intrinsic GL2GassmannHash(H::GrpMat:old:=false) -> SeqEnum[Tup]
{ djb2 hash of Gassmann signture of H. }
    if assigned H`SL then return SL2GassmannHash(H); end if;
    return djb2(sprint(gl2gsig(H:old:=old))) where _,H := GL2Level(H);
end intrinsic;

intrinsic SL2GassmannHash(H::GrpMat) -> SeqEnum[Tup]
{ djb2 hash of Gassmann signture of H. }
    return djb2(sprint(sl2gsig(H))) where _,H := SL2Level(H);
end intrinsic;

intrinsic GL2SubgroupKey(osig::SeqEnum[SeqEnum[RngIntElt]],gsig::SeqEnum[RngIntElt]) -> RngIntElt
{ Subgroup hash formed from orbit signature and Gassmann signature. }
    return djb2(sprint(osig))*djb2(sprint(gsig));
end intrinsic;

intrinsic GL2SubgroupKey(H::GrpMat : old:=false) -> RngIntElt
{ Returns subgroup hash used for table lookup. }
    if assigned H`SL then return SL2SubgroupKey(H); end if;
    return N eq 1 select djb2("[]")*djb2("[1]") else GL2SubgroupKey(gl2osig(H),gl2gsig(H:old:=old)) where N,H := GL2Level(H);
end intrinsic;

intrinsic SL2SubgroupKey(H::GrpMat) -> RngIntElt
{ Returns subgroup hash used for table lookup. }
    return N eq 1 select djb2("[]")*djb2("[1]") else GL2SubgroupKey(sl2osig(H),sl2gsig(H)) where N,H := SL2Level(H);
end intrinsic;

intrinsic GL2TorsionDegree (H::GrpMat) -> RngIntElt
{ The minimal size of a left H-orbit of (Z/NZ)^2 of exponent N (for elliptic curves with mod-N image H this is the minimal degree extension over which they acquire a rational point of order N). }
    return d where d := Min([r[2]:r in O|r[1] eq N]) where O := gl2osig(H) where N,H := GL2Level(H);
end intrinsic;

intrinsic GL2TorsionDegree (H::GrpMat,N::RngIntElt) -> RngIntElt
{ The minimal size of a left H-orbit of (Z/NZ)^2 of exponent N (for elliptic curves with mod-N image H this is the minimal degree extension over which they acquire a rational point of order N). }
    return d where d := Min([r[2]:r in O|r[1] eq N]) where O := gl2osig(H) where H := GL2Project(H,N);
end intrinsic;

intrinsic GL2IsogenyDegree (H::GrpMat) -> RngIntElt
{ The minimal size of a left H-orbit of (Z/NZ)^2 of exponent N (for elliptic curves with mod-N image H this is the minimal degree extension over which they acquire a rational point of order N). }
    return d where d := Min([r[2]:r in O|r[1] eq N]) where O := gl2isig(H) where N,H := GL2Level(H);
end intrinsic;

intrinsic GL2IsogenyDegree (H::GrpMat,N::RngIntElt) -> RngIntElt
{ The minimal size of a left H-orbit of (Z/NZ)^2 of exponent N (for elliptic curves with mod-N image H this is the minimal degree extension over which they acquire a rational point of order N). }
    return d where d := Min([r[2]:r in O|r[1] eq N]) where O := gl2isig(H) where H := GL2Project(H,N);
end intrinsic;

/*** GL2/SL2 canonical generators ***/

intrinsic GL2CanonicalGenerators(H::GrpMat) -> SeqEnum[SeqEnum[RngIntElt]]
{ Sorted list of canonical generators for H produced by GL2Canonicalize. }
    return GL2Generators(GL2Canonicalize(H));
end intrinsic;

gl2neg := func<a,M|[c eq 0 select 0 else M-c : c in a]>;
gl2fgens := func<H|[gens[i]:i in [1..#gens]|s ne [1,0,0,1] and not s in gens[1..i-1] where s:=gl2neg(gens[i],#BaseRing(H))] where gens:=GL2Generators(H)>; // generators of coarse H modulo -I

intrinsic SL2Canonicalize(H::GrpMat:Algorithm:="default") -> GrpMat, GrpMatElt
{ Canonically generated canonical representative of the GL2-conjugacy class of the intersection of H with SL2 as a subgroup of SL(2,Z/NZ) where N is the SL2-level of H.
  Let S be the concatenation of all primitive similarity classes that intersect H in which we order similarity classes by increasing size, decreasing order,
  and lexicographically increasing similarity invariants, and we order elements within each similarity class lexicographically (matrices [[a,b],[c,d]] are treated as quadruples [a,b,c,d] via Eltseq).
  The first generator of H is the least element of S in this ordering, the second generator is the next element of S that does not lie in the subgroup generated by the first element
  and which lies in a GL2-conjugate of H that contains the first element, and so on.
  Second return value is an element of GL(2,Z/NZ) such that the returned group is equal to the intersection of H^g with SL2 (note that g need not lie in SL2!). }
    start := Cputime(); timer := start;
    N,H := SL2Level(H); if N eq 1 then return sl2N1, Identity(sl2N1); end if;
    G := GL2Ambient(N);
    if not SL2ContainsNegativeOne(H) then
        H1 := SL2IncludeNegativeOne(H);   
        HH,c := SL2Canonicalize(H1:Algorithm:=Algorithm);
        c := GL2ElementLifter(HH`Level,N)(c); // Changed from SL2ElementLifter on 11/22/2023 because c need not have determinant 1
        HH := SL2Lift(HH,N);
        assert HH eq H1^c;
        NHH := Normalizer(G,HH); T := RightTransversal(NHH,HH); assert T[1] eq Identity(HH);
        gens := gl2fgens(HH);
        Kgens := Sort([Eltseq(G!h in Hc select h else gl2neg(h,N)): h in gens]) where Hc := H^c;
        K := sub<G|Kgens>;
        assert H^c eq K;
        t := T[1];
        for i:=2 to #T do
            Ktgens := Sort([Eltseq(G!h in Kt select h else gl2neg(h,N)) : h in gens]) where Kt := K^T[i];
            if Ktgens lt Kgens then Kgens := Ktgens; t := T[i]; end if;
        end for;
        K := sl2copyattr(sub<G|Kgens>,H);
        vprintf GL2,2: "Computed canonical generators %of for fine level %o SL2 subgroup of order %o in %.3os\n", sprint(GL2Generators(K)), N, sprint(GL2Generators(H)), H`Order, Cputime()-start;
        assert H^(c*t) eq K;
        return K,c*t;
    end if;
    R := SL2PrimitiveSimilarityReps(N); I,f := SL2PrimitiveSimilarityLists(H); GC := SL2PrimitiveSimilarityCounts(N);
    J := [r[3] : r in Sort([<-Order(R[I[i]]),-GC[I[i]],i> : i in [1..#I]])]; I := I[J];
    vprintf GL2,4: "Computed primitive SL2 similarity lists for level %o group H in %.3os\n", N, Cputime()-timer; timer := Cputime();
    L := f(I[1]); hmin := Min([Eltseq(x):x in Conjugates(G,L[1])]);
    g := GL2Conjugator(L[1],G!hmin);
    K := sub<G|hmin>; K`SL := true; H := sl2copyattr(H^g,H);
    if SL2Index(K) eq H`Index then
      vprintf GL2,4: "First GL2-generator %o generates!\n", sprint(Eltseq(hmin));
      K := sl2copyattr(K,H);
      return K,g;
    end if;
    vprintf GL2,4: "Computed initial generator %o yielding subgroup K of index %o in H of index %o in %.3os\n", sprint(Eltseq(hmin)), K`Index, H`Index, Cputime()-timer; timer := Cputime();
    T := [t:t in GL2RightTransversal(Normalizer(G,H))|h^(t^-1) in H] where h:=G!hmin;
    vprintf GL2,4: "Computed right transversal of order %o of NH in %.3os\n", #T, Cputime()-timer; timer := Cputime();
    for i in I do
        C := &join[Conjugates(H,h^g):h in f(i)];
        C := Sort([h:h in Set(&cat[[Eltseq(h^t):h in C]:t in T])]);
        check := false;
        for e in C do
            h := G!e;
            if h in K or (check and not &or[h^(t^-1) in H:t in T]) then continue; end if;
            K := sub<G|K,h>; K`SL := true;
            vprintf GL2,4: "Added generator %o in primitive similarity class %o yielding K of order %o with #T= %o\n", Eltseq(h), i, SL2Order(K), #T;
            if #T gt 1 then
                Tnew := [t : t in T | h^(t^-1) in H];
                if #Tnew lt #T then
                    T := Tnew; check := true;
                    vprintf GL2,4: "Trimmed T to %o elements in %.3os\n", #T, Cputime()-timer; timer := Cputime();
                end if;
                delete Tnew;
            end if;
            if SL2Order(K) eq H`Order then break; end if;
         end for;
        if SL2Order(K) eq H`Order then break; end if;
    end for;
    vprintf GL2,2: "Computed canonical generators %o for level %o SL2 subgroup %o of order %o in %.3os\n", sprint(SL2Generators(K)), N, sprint(SL2Generators(H)), H`Order, Cputime()-start;
    assert H^T[1] eq K;
    K := sl2copyattr(K,H);
    return K,g*T[1]; // Note that we replaced H with H^g above
end intrinsic;

intrinsic GL2Canonicalize(H::GrpMat:Algorithm:="default") -> GrpMat, GrpMatElt
{ Canonically generated canonical representative of the GL2-conjugacy class of a full determinant subgroup H reduced to its level N.
  This is the trivial subgroup of GL(2,Z) when N is 1 and otherwise has the following structure.
  The list of generators includs a list of canoncial generators for the intersection of H with SL2.  When the SL2Level M of H is less than N this
  will consist of the matrices [1,M,0,1],[1,0,M,1],[1+M,M,-M,1-M] generating the kernel of the reduction map from SL(2,Z/NZ) -> SL(2,Z/MZ)
  followed by canoncial lifts to level N of the generators g produced by SL2Canonicalize (as computed by SL2Lift using hensel+CRT).
  The list of generators continues with generators that do not have determinant one chosen using the same algorithm used by SL2Canonicalize.
  The second return value is an element of GL(2,Z/NZ) such that the returned group is equal to H^g (when H is reduced to its level N). }
    if assigned H`SL then return SL2Canonicalize(H:Algorithm:=Algorithm); end if;
    dindex := GL2DeterminantIndex(H);
    start := Cputime(); timer := start;
    N,H := GL2Level(H); if N eq 1 then return gl2N1,Identity(gl2N1); end if;
    G := GL2Ambient(N);
    if not GL2ContainsNegativeOne(H) then
        HH,c := GL2Canonicalize(GL2IncludeNegativeOne(H):Algorithm:=Algorithm);
        c := GL2ElementLifter(HH`Level,N)(c);
        HH := GL2Lift(HH,N); NHH := Normalizer(G,HH); T := RightTransversal(NHH,HH); assert T[1] eq Identity(HH);
        gens := gl2fgens(HH);
        Kgens := Sort([Eltseq(G!h in Hc select h else gl2neg(h,N)): h in gens]) where Hc := H^c;
        K := sub<HH|Kgens>;
        assert H^c eq K;
        t := T[1];
        assert H^c eq K^t;
        for i:=2 to #T do
            Ktgens := Sort([Eltseq(G!h in Kt select h else gl2neg(h,N)) : h in gens]) where Kt := K^T[i];
            if Ktgens lt Kgens then Kgens := Ktgens; t := T[i]; end if;
        end for;
        K := gl2copyattr(sub<GL(2,Integers(N))|Kgens>,H);
        vprintf GL2,2: "Computed canonical generators %of for fine level %o GL2 subgroup of order %o in %.3os\n", sprint(GL2Generators(K)), N, sprint(GL2Generators(H)), H`Order, Cputime()-start;
        assert H^(c*t) eq K;
        return K,c*t;
    end if;
    K,g := SL2Canonicalize(H:Algorithm:=Algorithm); M := K`Level;
    vprintf GL2,4: "Computed canonical SL2 subgroup K = %o of level %o, order %o, index %o in %.3os\n", sprint(GL2Generators(K)), K`Level, K`Order, K`Index, Cputime()-timer; timer := Cputime();
    if K`Order eq H`Order then assert M eq N; delete K`SL; return K,g; end if;
    if M lt N then K := SL2Lift(K,N); g := GL2ElementLifter(M,N)(g); end if;
    H := gl2copyattr(H^g,H);
    R := GL2PrimitiveSimilarityReps(N); I,f := GL2PrimitiveSimilarityLists(H:Algorithm:=Algorithm); GC := GL2PrimitiveSimilarityCounts(N);
    J := [r[3] : r in Sort([<-Order(R[I[i]]),-GC[I[i]],i> : i in [1..#I] | Determinant(R[I[i]]) ne 1])]; I := I[J];
    vprintf GL2,4: "Computed primitive GL2 similarity lists for level %o group H in %.3os\n", N, Cputime()-timer; timer := Cputime();
    NK := Normalizer(G,K);
    vprintf GL2,4: "Computed GL2-normalizer NK of index %o subgroup K of SL2 in %.3os\n", K`Index, Cputime()-timer; timer := Cputime();
    L := f(I[1]); hmins := [Min([Eltseq(x):x in Conjugates(NK,h)]):h in L];
    hmin,imin := Min(hmins);
    c := GL2Conjugator(NK,L[imin],G!hmin);
    delete K`SL; delete K`Index;
    K := sub<G|K,hmin>; H := gl2copyattr(H^c,H); g := g*c;
    if GL2Index(K) eq H`Index then
      vprintf GL2,4: "First GL2-generator %o generates!\n", sprint(Eltseq(hmin));
      K := gl2copyattr(K,H);
      return K,g;
    end if;
    vprintf GL2,4: "Computed initial generator %o yeilding subgroup K of index %o in H of index %o in %.3os\n", sprint(Eltseq(hmin)), K`Index, H`Index, Cputime()-timer; timer := Cputime();
    if GL2Index(H) le 1024 then
        T := [h:h in GL2RightTransversal(H)|K^h subset K];
        vprintf GL2,4: "Computed right GL2-transversal of index %o subgroup H with %o elements normalizing K in %.3os\n", H`Index, #T, Cputime()-timer; timer := Cputime();
    else
        NK := Normalizer(G,K);
        vprintf GL2,4: "Computed GL2-normalizer NK of index %o subgroup K of GL2 in %.3os\n", K`Index, Cputime()-timer; timer := Cputime();    
        NH := Normalizer(NK,H);
        vprintf GL2,4: "Computed NK-normalizer of index %o subgroup H of GL2 in %.3os\n", H`Index, Cputime()-timer; timer := Cputime();
        T := RightTransversal(NK,NH);
        vprintf GL2,4: "Computed right NK-transversal of index %o subgroup NH in %.3os\n", #T, Cputime()-timer; timer := Cputime();
    end if;
    // T should now contain reps (modulo stabilizer) of all conjugators that fix K
    vprintf GL2,4: "Computed %o conjugates of level %o order %o GL2 subgroup %o containing K in %.3os\n", #T, N, H`Order, sprint(GL2Generators(H)), Cputime()-timer; timer := Cputime();
    GL1 := GL1Ambient(N); D := sub<GL1|>;
    for i in I[2..#I] do
        if GL1![Determinant(R[i])] in D then continue; end if;
        L := &join[Conjugates(H,h^c):h in f(i)];
        L := &cat[[Eltseq(h^t):h in L]:t in T];
        h := G!Min(L);
        K := sub<G|K,h>; D := sub<GL1|D,[Determinant(G!h)]>;
        vprintf GL2,4: "Added generator %o in primitive similarity class %o yielding K of order %o\n", Eltseq(h), i, GL2Order(K);
        if #T gt 1 then
            T := [t : t in T | h^(t^-1) in H];
            vprintf GL2,4: "Trimmed T to %o elements in %.3os\n", #T, Cputime()-timer; timer := Cputime();
        end if;
        if GL1Index(D) eq dindex then break; end if;
    end for;
    vprintf GL2,2: "Computed canonical generators %o for level %o GL2 subgroup %o of order %o in %.3os\n", sprint(GL2Generators(K)), N, sprint(GL2Generators(H)), H`Order, Cputime()-start;
    // assert H^(g*T[1]) eq K;
    K := gl2copyattr(K,H);
    return K,g*T[1];
end intrinsic;

intrinsic SL2CanonicalGenerators(H::GrpMat) -> SeqEnum[SeqEnum[RngIntElt]]
{ Sorted list of canonical generators for H produced by SL2Canonicalize. }
    return SL2Generators(SL2Canonicalize(H));
end intrinsic;

/*** GL2 Refinements ***/

intrinsic GL2RemoveConjugates(S::SeqEnum[GrpMat],G::GrpMat) -> SeqEnum[GrpMat]
{ Reduces a list of subgroups of a group G to a sublist of G-conjugacy class representatives. }
    X := IndexFibers([1..#S],func<i|GL2SubgroupKey(S[i])>);
    L := [];
    for k in Keys(X) do T := [X[k][1]]; r := X[k]; for i:=2 to #r do if &and[not IsConjugate(G,S[r[i]],S[j]): j in T] then Append(~T,r[i]); end if; end for; L cat:=T; end for;
    return S[Sort(L)];
end intrinsic;

intrinsic GL2HasRefinements(H::GrpMat) -> SeqEnum[GrpMat]
{ Given H containing -I, returns true of H has at least one quadratic refinement and false otherwise. }
    H2 := GL2Lift(H,2*GL2Level(H)); nI := H2!-Identity(H2);
    A,pi:=AbelianQuotient(H2);  A2 := Image(hom<A->A|x:->2*x>);
    return not pi(nI) in A2;
end intrinsic;

intrinsic GL2Refinements(H::GrpMat) -> SeqEnum[GrpMat]
{ Given H containing -I, returns a list of index-2 subgroups of H that do not contain -I, up to conjugacy in the ambient GL2. }
    H := GL2MinimizeGenerators(H:MaxAttempts:=5);
    g := [g:g in Generators(H)]; V := CartesianPower([true,false],#g); n := GL2Order(H);
    S := [sub<H|[v[i] select g[i] else -g[i]:i in [1..#g]]>: v in V];
    S := [K:K in S|GL2Order(K) lt n];
    return GL2RemoveConjugates(S,H);
end intrinsic;

intrinsic GL2QuadraticTwists(H::GrpMat : IncludeGeneric:=true) -> SeqEnum[GrpMat]
{ Given a subgroup H of GL(2,Z/NZ), returns the list of subgroups K of <H,-I> := G for which <K,-I> = G (including H), up to conjugacy in GL2. }
    R := BaseRing(H); N := #R;  if not IsFinite(N) then assert H eq gl2N1; return [H]; end if;
    // caller should deal with this, if #R mod 4 eq 2 then H:=GL2Lift(H,4*#R); R:=BaseRing(H); end if; // need to lift level 2*m to 8*m to be sure to see all quadratic twists
    G := GL2IncludeNegativeOne(H); nI := -Identity(G);
    S := [K`subgroup:K in MaximalSubgroups(G:IndexEqual:=2)|not nI in K`subgroup];
    GL2 := GL2Ambient(N);
    if #S gt 1 then time S := GL2RemoveConjugates(S,G); end if;
    for i:=1 to #S do S[i]`NegOne := false; S[i]`Index := G`Order div S[i]`Order; end for;
    return IncludeGeneric select [G] cat S else S;
end intrinsic;

intrinsic GL2QuarticCMTwists(N::RngIntElt : NegOneOnly:=false) -> SeqEnum[GrpMat]
{ Returns a list of the quartic twists of H:=GL2CartanNormalizer(-4,N), all subgroups K for which H = <K,zeta_4> up to conjugacy in GL2. }
    if N eq 1 then return [gl2N1]; end if;
    H := GL2CartanNormalizer(-4,N); z4 := H![0,1,-1,0]; nI := z4^2; G := GL2Ambient(N);
    I2 := GL2RemoveConjugates([K`subgroup: K in MaximalSubgroups(H:IndexEqual:=2) | not z4 in K`subgroup], G);
    S := [H] cat I2; for i:=1 to #S do S[i]`NegOne := true; end for;
    if not NegOneOnly then 
        I4 := GL2RemoveConjugates(&cat[[K`subgroup: K in MaximalSubgroups(J:IndexEqual:=2) | not nI in K`subgroup]:J in I2],G);
        for i := 1 to #I4 do I4[i]`NegOne := false; end for;
        S cat:= I4;
    end if;
    for i := 1 to #S do S[i]`Index := G`Order div S[i]`Order; end for;
    return S;
end intrinsic;

intrinsic GL2SexticCMTwists(N::RngIntElt : NegOneOnly := false) -> SeqEnum[GrpMat]
{ Returns a list of the sextic twists of H:=GL2CartanNormalizer(-3,N), all subgroups K for which H = <K,zeta_6> up to conjugacy in GL2. }
    if N eq 1 then return [gl2N1]; end if;
    H := GL2CartanNormalizer(-3,N); z3 := H![0,1,-1,-1]; G := GL2Ambient(N);
    S := NegOneOnly select [H] else GL2QuadraticTwists(H);
    I3 := GL2RemoveConjugates([K`subgroup: K in MaximalSubgroups(H:IndexEqual:=3) | not z3 in K`subgroup],G);
    for i :=1 to #I3 do I3[i]`NegOne := true; end for;
    if not NegOneOnly then
        I2 := S[2..#S];
        I6 := GL2RemoveConjugates(&cat[[K`subgroup: K in MaximalSubgroups(J:IndexEqual:=3) | not z3 in K`subgroup]:J in I2],G);
        for i:=1 to #I6 do I6[i]`NegOne := false; end for;
        S cat:= I3 cat I6;
    else
        S cat:= I3;
    end if;
    for i := 1 to #S do S[i]`Index := G`Order div S[i]`Order; end for;
    return S;
end intrinsic;
