freeze;

intrinsic ProfileTimes(:All:=false) -> SeqEnum
{ Lists vertices in profile graph in order of time.  You need to SetProfile(true), run something, then call this (which will SetProfile(false) before dumping). }
    SetProfile(false);
    return S where S := Sort([Label(V!i):i in [1..#V]|All or (r`Count gt 0 and r`Time gt 0.01 where r:=Label(V!i))] where V:=Vertices(ProfileGraph()),func<a,b|a`Time-b`Time>);
end intrinsic;

intrinsic PrintProfile(:All:=false)
{ Lists vertices in profile graph in order of time.  You need to SetProfile(true), run something, then call this (which will SetProfile(false) before dumping). }
    S := ProfileTimes(:All:=All);
    for r in S do printf "%.3os in %o calls to %o\n",r`Time,r`Count,r`Name; end for;
end intrinsic;

intrinsic Factorization(r::FldRatElt) -> SeqEnum
{ The prime factorization of the rational number r. }
    return Sort(Factorization(Numerator(r)) cat [<a[1],-a[2]>:a in Factorization(Denominator(r))]);
end intrinsic;

intrinsic GSp(d::RngIntElt, q::RngIntElt) -> GrpMat
{ The group of symplectic similitudes of degree d over F_q. }
    return CSp(d,q);
end intrinsic;

intrinsic Eltseq(s::SetMulti[RngIntElt]) -> SeqEnum
{ Sorted sequence of tuples representing a multiset of integers. }
    return Sort([<n,Multiplicity(s,n)>:n in Set(s)]);
end intrinsic;

intrinsic ReplaceCharacter(s::MonStgElt,c::MonStgElt,d::MonStgElt) -> MonStgElt
{ Efficiently replace every occurrence of the character c in s with the string d (c must be a single character but d need not be). }
    require #c eq 1: "The second parameter must be a single character (string of length 1).";
    t := Split(s,c:IncludeEmpty);
    if s[#s] eq c then Append(~t,""); end if; // add empty string at the end which Split omits
    return Join(t,d);
end intrinsic;

intrinsic ReplaceString(s::MonStgElt,c::MonStgElt,d::MonStgElt) -> MonStgElt
{ Greedily replace each occurrence of string c in s with the string d. }
    require #c ge 1: "The string to be replaced cannot be empty.";
    m := #c;
    t := "";
    n := Index(s,c);
    while n gt 0 do
        t cat:= s[1..n-1] cat d;
        s := s[n+m..#s];
        n := Index(s,c);
    end while;
    return t cat s;
end intrinsic;

intrinsic djb2(s::MonStgElt:b:=64) -> RngIntElt
{ Returns the b-bit djb2 hash of s. Default value of b is 64. }
    h:=5381; m:=2^b-1; s := BinaryString(s);
    for i:=1 to #s do h := BitwiseAnd(33*h+s[i],m); end for;
    return h;
end intrinsic;

intrinsic PySplit(s::MonStgElt, sep::MonStgElt : limit:=-1) -> SeqEnum[MonStgElt]
{Splits using Python semantics (different when #sep > 1, and different when sep at beginning or end)}
    if #sep eq 0 then
        error "Empty separator";
    end if;
    i := 1;
    j := 0;
    ans := [];
    while limit gt 0 or limit eq -1 do
        if limit ne -1 then limit -:= 1; end if;
        pos := Index(s, sep, i);
        if pos eq 0 then break; end if;
        j := pos - 1;
        Append(~ans, s[i..j]);
        i := j + #sep + 1;
    end while;
    Append(~ans, s[i..#s]);
    return ans;
end intrinsic;

intrinsic split(s::MonStgElt,d::MonStgElt) -> SeqEnum[MonStgElt]
{ Splits the string s using the delimter d, including empty and trailing elements (equivalent to python r.split(d) in python). }
    return Split(s,d:IncludeEmpty) cat (s[#s] eq d select [""] else []);
end intrinsic;

intrinsic getrecs(filename::MonStgElt:Delimiter:=":") -> SeqEnum[SeqEnum[MonStgElt]]
{ Reads a delimited file, returns list of lists of strings (one list per line). }
    return [split(r,Delimiter):r in Split(Read(filename))];
end intrinsic;

intrinsic putrecs(filename::MonStgElt,S::SeqEnum[SeqEnum[MonStgElt]]:Delimiter:=":")
{ Given a list of lists of strings, creates a colon delimited file with one list per line. }
    fp := Open(filename,"w");
    n := 0;
    for r in S do Puts(fp,Join(r,Delimiter)); n+:=1; end for;
    Flush(fp);
end intrinsic;

intrinsic StringToStrings (s::MonStgElt) -> SeqEnum[MonStgElt]
{ Given a string encoding a list of strings that do not contain commas or whitespace, e.g. "[cat,dog]", returns a list of the strings, e.g [ "cat", "dog" ]. }
    s := StripWhiteSpace(s);
    require s[1] eq "[" and s[#s] eq "]": "Input must be a string representing a list";
    s := s[2..#s-1];
    return Split(s,",");
end intrinsic;

intrinsic sum(X::[]) -> .
{ Sum of a sequence (empty sum is 0). }
    if #X eq 0 then
        try
            return Universe(X)!0;
        catch e
            return Integers()!0;
        end try;
    end if;
    return &+X;
end intrinsic;

intrinsic sum(v::ModTupRngElt) -> .
{ Sum of a vector. }
    return  sum(Eltseq(v));
end intrinsic;

intrinsic prod(X::[]) -> .
{ Product of a sequence (empty product is 1). }
    if #X eq 0 then
        try
            return Universe(X)!1;
        catch e
            return Integers()!1;
        end try;
    end if;
    return &*X;
end intrinsic;

intrinsic prod(v::ModTupRngElt) -> .
{ Product of a vector. }
    return prod(Eltseq(v));
end intrinsic;

intrinsic strip(X::MonStgElt) -> MonStgElt
{ Strips spaces and carraige returns from string; used to be faster than StripWhiteSpace, now that StripWhiteSpace is faster we just call it. }
    return StripWhiteSpace(X);
end intrinsic;

intrinsic sprint(X::.) -> MonStgElt
{ Sprints object X with spaces and carraige returns stripped. }
    if Type(X) eq Assoc then return Join(Sort([ $$(k) cat "=" cat $$(X[k]) : k in Keys(X)]),":"); end if;
    return strip(Sprintf("%o",X));
end intrinsic;

intrinsic atoi(s::MonStgElt) -> RngIntElt
{ Converts a string to an integer (alias for StringToInteger). }
    return #s gt 0 select StringToInteger(s) else 0;
end intrinsic;

intrinsic itoa(n::RngIntElt) -> MonStgElt
{ Converts an integer to a string (equivalent to but slightly slower than IntegerToString, faster than sprint). }
    return IntegerToString(n);
end intrinsic;

intrinsic StringToReal(s::MonStgElt) -> RngIntElt
{ Converts a decimal string (like 123.456 or 1.23456e40 or 1.23456e-10) to a real number at default precision. }
    if #s eq 0 then return 0.0; end if;
    if "e" in s then
        t := Split(s,"e");
        require #t eq 2: "Input should have the form 123.456e20 or 1.23456e-10";
        return StringToReal(t[1])*10.0^StringToInteger(t[2]);
    end if;
    t := Split(s,".");
    require #t le 2: "Input should have the form 123 or 123.456 or 1.23456e-10";
    n := StringToInteger(t[1]);  s := t[1][1] eq "-" select -1 else 1;
    return #t eq 1 select RealField()!n else RealField()!n + s*RealField()!StringToInteger(t[2])/10^#t[2];
end intrinsic;

intrinsic atof (s::MonStgElt) -> RngIntElt
{ Converts a decimal string (like "123.456") to a real number at default precision. }
    return StringToReal(s);
end intrinsic;

intrinsic StringsToAssociativeArray(s::SeqEnum[MonStgElt]) -> Assoc
{ Converts a list of strings "a=b" to an associative array A with string keys and values such that A[a]=b. Ignores strings not of the form "a=b". }
    A := AssociativeArray(Universe(["string"]));
    for a in s do t:=Split(a,"="); if #t eq 2 then A[t[1]]:=t[2]; end if; end for;
    return A;
end intrinsic;

intrinsic atod(s::SeqEnum[MonStgElt]) -> Assoc
{ Converts a list of strings "a=b" to an associative array A with string keys and values such that A[a]=b (alias for StringsToAssociativeArray). }
    return StringsToAssociativeArray(s);
end intrinsic;

intrinsic StringToIntegerArray(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Given string representing a sequence of integers, returns the sequence (faster and safer than eval). }
    t := strip(s);
    if t eq "[]" then return [Integers()|]; end if;
    assert #t ge 2 and t[1] eq "[" and t[#t] eq "]";
    return [Integers()|StringToInteger(n):n in Split(t[2..#t-1],",")];
end intrinsic;

intrinsic atoii(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Converts a string to a sequence of integers (alias for StringToIntegerArray). }
    return StringToIntegerArray(s);
end intrinsic;

intrinsic iitoa(a::SeqEnum[RngIntElt]) -> MonStgElt
{ Converts a sequence of integers to a string (faster than sprint). }
    return "[" cat Join([IntegerToString(n) : n in a],",") cat "]";
end intrinsic;

intrinsic atoiii(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Converts a string to a sequence of sequences of integers. }
    t := strip(s);
    if t eq "[]" then return []; end if;
    if t eq "[[]]" then return [[Integers()|]]; end if;
    assert #t gt 4;
    if t[1..2] eq "[<" and t[#t-1..#t] eq ">]" then
        r := Split(t[2..#t-1],"<");
        return [[Integers()|StringToInteger(n):n in Split(a[1] eq ">" select "" else Split(a,">")[1],",")]:a in r];
    elif t[1..2] eq "[[" and t[#t-1..#t] eq "]]" then
        r := Split(t[2..#t-1],"[");
        return [[Integers()|StringToInteger(n):n in Split(a[1] eq "]" select "" else Split(a,"]")[1],",")]:a in r];
    else
        error "atoiii: Unable to parse string " cat s;
    end if;
end intrinsic;

intrinsic atoiiii(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Converts a string to a sequence of sequences of sequences of integers. }
    t := strip(s);
    if t eq "[]" then return []; end if;
    if t eq "[[]]" then return [[Integers()|]]; end if;
    if t eq "[[[]]]" then return [[[Integers()|]]]; end if;
    assert #t gt 5 and t[1..3] eq "[[[" and t[#t-2..#t] eq "]]]";
    s := s[2..#s-1];
    a := [];
    while true do
        i := Index(s,"]],[[");
        if i eq 0 then Append(~a,atoiii(s)); break; end if;
        Append(~a,atoiii(s[1..i+1]));
        s := s[i+3..#s];
    end while;
    return a;
end intrinsic;

intrinsic StringToRationalArray(s::MonStgElt) -> SeqEnum[RatFldElt]
{ Given string representing a sequence of rational numbers, returns the sequence (faster and safer than eval). }
    if s eq "[]" then return []; end if;
    t := strip(s);
    assert #t ge 2 and t[1] eq "[" and t[#t] eq "]";
    return [StringToRational(n):n in Split(t[2..#t-1],",")];
end intrinsic;

intrinsic StringToRealArray(s::MonStgElt) -> SeqEnum[RatFldElt]
{ Given string representing a sequence of real numbers, returns the sequence (faster and safer than eval). }
    if s eq "[]" then return []; end if;
    t := strip(s);
    assert #t ge 2 and t[1] eq "[" and t[#t] eq "]";
    return [atof(n):n in Split(t[2..#t-1],",")];
end intrinsic;

intrinsic atoff(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Converts a string to a sequence of reals (alias for StringToRealArray). }
    return StringToRealArray(s);
end intrinsic;

intrinsic atofff(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Converts a string to a sequence of sequences of real numbers. }
    t := strip(s);
    if t eq "[]" then return []; end if;
    if t eq "[[]]" then return [[RealField()|]]; end if;
    assert #t gt 4 and t[1..2] eq "[[" and t[#t-1..#t] eq "]]";
    r := Split(t[2..#t-1],"[");
    return [[RealField()|StringToReal(n):n in Split(a[1] eq "]" select "" else Split(a,"]")[1],",")]:a in r];
end intrinsic;

intrinsic goodp(f::RngUPolElt,p::RngIntElt) -> RngIntElt
{ Returns true if the specified polynomial is square free modulo p (without computing the discrimnant of f). }
    return Discriminant(PolynomialRing(GF(p))!f) ne 0;
end intrinsic;

intrinsic Base26Encode(n::RngIntElt) -> MonStgElt
{ Given a nonnegative integer n, returns its encoding in base-26 (a=0,..., z=25, ba=26,...). }
    require n ge 0: "n must be a nonnegative integer";
    alphabet := "abcdefghijklmnopqrstuvwxyz";
    s := alphabet[1 + n mod 26]; n := (n-(n mod 26)) div 26;
    while n gt 0 do
        s := alphabet[1 + n mod 26] cat s; n := (n-(n mod 26)) div 26;
    end while;
    return s;
end intrinsic;

intrinsic Base26Decode(s::MonStgElt) -> RngIntElt
{ Given string representing a nonnegative integer in base-26 (a=0,..., z=25, ba=26,...) returns the integer. }
    alphabetbase := StringToCode("a");
    n := 0;
    for c in Eltseq(s) do n := 26*n + StringToCode(c) - alphabetbase; end for;
    return n;
end intrinsic;

intrinsic OrderStats(G::Grp) -> SetMulti[RngIntElt]
{ Multiset of order statistics of elements of the group G. }
    if #G eq 1 then return {*1*}; end if;
    if IsAbelian(G) then
        function pos(p,a)
            s := Multiset(a);  n := Round(Log(p,a[#a]));
            t:= [1] cat [&*[Integers()|n:n in a|n lt p^i] * &*[Integers()|p^Multiplicity(s,r):r in Set(s)|r ge p^i]^i:i in [1..n]];
            return [[1,1]] cat [[p^i,t[i+1]-t[i]]:i in [1..#t-1]];
        end function;
        G := AbelianGroup(G);
        Z := [pos(p,pPrimaryInvariants(G,p)):p in PrimeDivisors(#G)];
        return {* &*[r[1]:r in x]^^&*[r[2]:r in x] : x in CartesianProduct(Z) *};
    end if;
    C:=ConjugacyClasses(G);
    return SequenceToMultiset(&cat[[c[1]:i in [1..c[2]]]:c in C]);
end intrinsic;

intrinsic CyclicGenerators(G::GrpAb) -> SeqEnum[GrpAb]
{ A list of generators of the distinct cyclic subgroups of the finite abelian group G. }
    require IsFinite(G): "G must be finite.";
    if #G eq 1 then return [Identity(G)]; end if;
    if #Generators(G) eq 1 then g := G.1; return [e*g:e in Reverse(Divisors(Exponent(G)))]; end if;
    X := [[Identity(G)] cat &cat[[H`subgroup.1: H in Subgroups(Gp:Sub:=[n])]:n in Reverse(Divisors(Exponent(Gp)))|n gt 1] where Gp:=SylowSubgroup(G,p):p in PrimeDivisors(Exponent(G))];
    return [&+[z[i]:i in [1..#z]]:z in CartesianProduct(X)];
end intrinsic;

intrinsic ConjugateIntersection(G::Grp, H1::Grp, H2::Grp) -> Grp
{ Given finite subgroups H1 and H2 of a group G, returns a largest subgroup of G contained in a conjugate of H1 and a conjugate of H2. }
    S := [H1 meet H:H in Conjugates(G,H2)];
    I := [<Index(G,S[i]),i>:i in [1..#S]];
    return S[Min(I)[2]];
end intrinsic;
    
intrinsic ConjugateCompositum(G::Grp, H1::Grp, H2::Grp) -> Grp
{ Given subgroups H1 and H2 of G, returns a smallest subgroup of G that contains a conjugate of H1 and a conjugate of H2. }
    S := [sub<G|H1,H>:H in Conjugates(G,H2)];
    I := [<#S[i],i>:i in [1..#S]];
    return S[Min(I)[2]];
end intrinsic;

getval := func<X,k| b select v else [] where b,v := IsDefined(X,k)>;

intrinsic IndexFibers (S::SeqEnum, f::UserProgram : Unique:=false, Project:=false) -> Assoc
{ Given a list of objects S and a function f on S creates an associative array satisfying A[f(s)] = [t:t in S|f(t) eq f(s)]. }
    A := AssociativeArray();
    if Type(Project) eq UserProgram then
        if Unique then for x in S do A[f(x)] := Project(x); end for; return A; end if;
        for x in S do y := f(x); A[y] := Append(getval(A,y),Project(x)); end for;
    else
        if Unique then for x in S do A[f(x)] := x; end for; return A; end if;
        for x in S do y := f(x); A[y] := Append(getval(A,y),x); end for;
    end if;
    return A;
end intrinsic;

intrinsic IndexFibers (S::List, f::UserProgram : Unique:=false, Project:=false) -> Assoc
{ Given a list of objects S and a function f on S creates an associative array satisfying A[f(s)] = [t:t in S|f(t) eq f(s)]. }
    A := AssociativeArray();
    if Type(Project) eq UserProgram then
        if Unique then for x in S do A[f(x)] := Project(x); end for; return A; end if;
        for x in S do y := f(x); A[y] := Append(getval(A,y),Project(x)); end for;
    else
        if Unique then for x in S do A[f(x)] := x; end for; return A; end if;
        for x in S do y := f(x); A[y] := Append(getval(A,y),x); end for;
    end if;
    return A;
end intrinsic;

intrinsic IndexFile (filename::MonStgElt, key::. : Delimiter:=":", Unique:=false, data:=[]) -> Assoc
{ Loads file with colon-delimited columns (or as specified by Delimiter) creating an AssociativeArray with key specified by keys (a column index or list of column indexes) and contents determined by data, which should be either a column index or list of column indexes (empty list means entire record). }
    require Type(key) eq RngIntElt or Type(key) eq SeqEnum: "second parameter should be a column index or list of column indices";
    if Type(data) eq RngIntElt then data := [data]; end if;
    if #data eq 1 then Project := func<r|r[data[1]]>; else if #data gt 1 then Project := func<r|r[data]>; else Project := func<r|r>; end if; end if;
    return IndexFibers(getrecs(filename), func<r|r[key]> : Unique:=Unique, Project:=Project);
end intrinsic;

intrinsic ReduceToReps (S::[], E::UserProgram: min:=func<a,b|a>) -> SeqEnum
{ Given a list of objects S and an equivalence relation E on S returns a maximal sublist of inequivalent objects. }
    if #S le 1 then return S; end if;
    if #S eq 2 then return E(S[1],S[2]) select [min(S[1],S[2])] else S; end if;
    T:=[S[1]];
    for i:=2 to #S do
        s:=S[i]; sts:=true;
        for j:=#T to 1 by -1 do // check most recently added entries first in case adjacent objects in S are more likely to be equivalent (often true)
            if E(s,T[j]) then T[j]:=min(s,T[j]); sts:=false; break; end if;
        end for;
        if sts then T:=Append(T,s); end if;
    end for;
    return T;
end intrinsic;

intrinsic Classify (S::[], E::UserProgram) -> SeqEnum[SeqEnum]
{ Given a list of objects S and an equivalence relation E on them returns a list of equivalence classes (each of which is a list). }
    if #S eq 0 then return []; end if;
    if #S eq 1 then return [S]; end if;
    if #S eq 2 then return E(S[1],S[2]) select [S] else [[S[1]],[S[2]]]; end if;
    T:=[[S[1]]];
    for i:=2 to #S do
        s:=S[i]; sts:=true;
        for j:=#T to 1 by -1 do // check most recently added classes first in case adjacent objects in S are more likely to be equivalent (often true)
            if E(s,T[j][1]) then T[j] cat:= [s]; sts:=false; break; end if;
        end for;
        if sts then T:=Append(T,[s]); end if;
    end for;
    return T;
end intrinsic;

intrinsic DihedralGroup(G::GrpAb) -> Grp
{ Construct the generalized dihedral group dih(G) := G semidirect Z/2Z with Z/2Z acting by inversion. }
    Z2 := AbelianGroup([2]);
    h:=hom<Z2->AutomorphismGroup(G)|x:->hom<G->G|g:->IsIdentity(x) select g else -g>>;
    return SemidirectProduct(G,Z2,h);
end intrinsic;

intrinsic Quotients(G::Grp:Order:=0) -> SeqEnum
{ Returns a list of quotients of G (either all non-trivial quotients or those of the specified Order). }
    n := #G;
    return [quo<G|H> where H:=K`subgroup : K in NormalSubgroups(G) | (Order eq 0 and not #K`subgroup in [1,n]) or Index(G,K`subgroup) eq Order];
end intrinsic;

function TransformForm(f, T : co := true, contra := false)
    R := Parent(f);
    vars := Matrix([ [ mon ] : mon in MonomialsOfDegree(R, 1) ]);
    if (not co) or contra then
        return Evaluate(f, Eltseq(ChangeRing(Transpose(T)^(-1), R) * vars));
    end if;
    return Evaluate(f, Eltseq(ChangeRing(T, R) * vars));
end function;

function RandomInvertibleMatrix(R, B)
    assert B ge 1;
    n := Rank(R); F := BaseRing(R);
    D := [ -B..B ];
    repeat T := Matrix(F, n, n, [ Random(D) : i in [1..n^2] ]); until IsUnit(Determinant(T));
    return T;
end function;

intrinsic RandomizeForm(f::RngMPolElt: B:=3) -> RngMPolElt
{ Applies a random invertible linear change of variables to the specified homogeneous polynomial (preserves integrality). }
    require IsHomogeneous(f): "Input polynomial must be homogeneous";
    return TransformForm(f, RandomInvertibleMatrix(Parent(f), B));
end intrinsic;

intrinsic RandomizeForms(forms::SeqEnum[RngMPolElt]: B:=3) -> SeqEnum[RngMPolElt]
{ Applies a random invertible linear change of variables to the specified sequence of homogeneous polynomials (preserves integrality). }
    require &and[IsHomogeneous(f) : f in forms]: "Input polynomial must be homogeneous";
    if #forms eq 0 then return forms; end if;
    M := RandomInvertibleMatrix(Parent(forms[1]),B);
    return [TransformForm(f, M) : f in forms];
end intrinsic;

intrinsic MinimizeGenerators(G::Grp) -> Grp
{ Given a finite group G tries to reduce the number of generators by sampling random elements.  Result is not guaranteed to minimize the number of generators but this is very likely. }
    require IsFinite(G): "G must be a finite group";
    n := #G;
    if IsAbelian(G) then
        Gab,pi := AbelianGroup(G);
        B := AbelianBasis(Gab);
        return sub<G|[Inverse(pi)(b):b in B]>;
    end if;
    r := 2;
    while true do
        for i:=1 to 100 do H := sub<G|[Random(G):i in [1..r]]>; if #H eq n then return H; end if; end for;
        r +:= 1;
    end while;
end intrinsic;

intrinsic RegularRepresentation(H::Grp) -> GrpPerm
{ The regular representation of H as a permutation group of degree #H. }
    _,H := RegularRepresentation(H,sub<H|>);
    return H;
end intrinsic;

intrinsic HurwitzClassNumber(N::RngIntElt) -> FldRatElt
{ The Hurwitz class number of positive definite binary quadratic forms of discriminant -N with each class C counted with multiplicity 1/#Aut(C), extended by Zagier to H(0)=-1/12 and H(-u^2)=-u/2, with H(-n) = 0 for all nonsquare n>0. }
    if N eq 0 then return -1/12; end if; if N lt 0 then b,u:=IsSquare(N); return b select -u/2 else 0;  end if;
    if not N mod 4 in [0,3] then return 0; end if;
    D := FundamentalDiscriminant(-N); f := Integers()!Sqrt(-N/D); w := D lt -4 select 1 else (D lt -3 select 2 else 3);
    return ClassNumber(D)/w * &+[MoebiusMu(d)*KroneckerSymbol(D,d)*SumOfDivisors(f div d):d in Divisors(f)];
end intrinsic;

intrinsic KroneckerClassNumber(D::RngIntElt) -> RngIntElt
{ The sum of the class numbers of the discriminants DD that divide the given imaginary quadratic discriminant D (this is not the same as the Hurwitz class number of -D, in particular, it is always an integer). }
    require D lt 0 and IsDiscriminant(D): "D must be an imaginary quadratic discriminant.";
    D0 := FundamentalDiscriminant(D);
    if D0 lt -4 then return HurwitzClassNumber(-D); end if;
    _,f := IsSquare(D div D0);
    return &+[ClassNumber(d^2*D0): d in Divisors(f)];
end intrinsic;

function plog(p,e,a,b) // returns nonnegative integer x such that a^x = b or -1, assuming a has order p^e
    if e eq 0 then return a eq 1 and b eq 1 select 0 else -1; end if;
    if p^e le 256 then return Index([a^n:n in [0..p^e-1]],b)-1; end if;
    if e eq 1 then
        // BSGS base case
        aa := Parent(a)!1;
        r := Floor(Sqrt(p)); s := Ceiling(p/r);
        babys := AssociativeArray(); for x:=0 to r-1 do babys[aa] := x; aa *:= a; end for;
        bb := b;
        x := 0; while x lt s do if IsDefined(babys,bb) then return (babys[bb]-r*x) mod p; end if; bb *:= aa; x +:=1; end while;
        return -1;
    end if;
    e1 := e div 2; e0 := e-e1;
    x0 := $$(p,e0,a^(p^e1),b^(p^e1)); if x0 lt 0 then return -1; end if;
    x1 := $$(p,e1,a^(p^e0),b*a^(-x0)); if x1 lt 0 then return -1; end if;
    return (x0 + p^e0*x1);
end function;

function qlog(p,e,m,a,b) // computes discrete log of b wrt a in Z/p^eZ given the order m of a
    R := Integers(p^e); a := R!a; b := R!b;
    if p eq 2 then return plog(2,Valuation(m,2),a,b); end if;
    me := Valuation(m,p);  m1 := p^me; m2 := GCD(m,p-1);
    x1 := plog(p,me,a^m2,b^m2); if x1 lt 0 then return x1; end if;
    x2 := Log(GF(p)!(a^m1),GF(p)!(b^m1)); if x2 lt 0 then return x2; end if;
    return CRT([x1,x2],[m1,m2]);
end function;

intrinsic Log (a::RngIntResElt, b::RngIntResElt) -> RngIntElt
{ Given a,b in (Z/nZ)* returns least nonnegative x such that a^x = b or -1 if no such x exists. }
    R := Parent(a); n := #R;
    require Parent(b) eq R: "Arguments must be elements of the same ring Z/nZ";
    m := Order(a); if m le 5000 then return Index([a^n:n in [0..m-1]],b)-1; end if;
    P := Factorization(n);
    M := [Order(Integers(p[1]^p[2])!a) : p in P];
    L := [qlog(P[i][1],P[i][2],M[i],a,b) : i in [1..#P]];
    if -1 in L then return -1; end if;
    return CRT(L,M);
end intrinsic;

intrinsic C4C6Invariants(E::CrvEll[FldRat]) -> RngInt, RngInt
{ Returns the c4 and c6 invariants of the specified elliptic curve E/Q (assumes E is defined by an integral model). }
    a := Coefficients(E);
    b2 := a[1]^2+4*a[2];
    b4 := a[1]*a[3]+2*a[4];
    b6 := a[3]^2+4*a[5];
    b8 := a[1]^2*a[5] - a[1]*a[3]*a[4] + 4*a[2]*a[5] + a[2]*a[3]^2 - a[4]^2;
    c4 := b2^2-24*b4;
    c6 := -b2^3+36*b2*b4-216*b6;
    return Integers()!(b2^2-24*b4),Integers()!(-b2^3+36*b2*b4-216*b6);
end intrinsic;

intrinsic GetFilenames(I::Intrinsic) -> SeqEnum
{ Return the filenames where such intrinsics are defined }
    lines := Split(Sprint(I, "Maximal"));
    res := [];
    def := "Defined in file: ";
    for i->line in lines do
        if line[1] eq "(" and Position(line, "->") ne 0 then
            s := Split(StripWhiteSpace(line), "->");
            assert #s eq 2;
            arguments := [Split(elt, ":")[2] : elt in Split(&cat Split(s[1], "()"))];
            values := Split(s[2], ",");
            if i gt 1 and lines[i-1][1..#def] eq def then
                comma := Position(lines[i-1], ",");
                filename := lines[i-1][#def + 1..comma-1];
            else
                filename := "";
            end if;
            Append(~res, <filename, arguments, values>);
        end if;
    end for;
    return res;
end intrinsic;

intrinsic WriteStderr(s::MonStgElt)
{ write to stderr }
  E := Open("/dev/stderr", "a");
  Write(E, s);
  Flush(E);
end intrinsic;

intrinsic WriteStderr(e::Err)
{ write to stderr }
  WriteStderr(Sprint(e) cat "\n");
end intrinsic;

intrinsic MonicQuadraticRoots(b::RngIntElt, c::RngIntElt, p::RngIntElt, e:RngIntElt) -> SeqEnum[RngIntElt]
{ Returns the complete list of solutions to x^2+bx+c = 0 in Z/p^eZ for p prime and e ge 1 (does not verify the primality of p). }
    require e gt 0: "e must be positive";
    q := p^e;
    b mod:= q; c mod:= q;
    // for the sake of simplicity we just hensel linearly; this could/should be improved
    if p eq 2 then
        if IsOdd(c) and IsOdd(b) then return [Integers()|]; end if;
        S := IsEven(c) select (IsOdd(b) select [0,1] else [0]) else [1];
    else
        bp := GF(p)!b;
        s,u := IsSquare(bp^2-4*c);
        if not s then return [Integers()|]; end if;
        S := u eq 0 select [Integers()|-bp/2] else [Integers()|(-bp-u)/2,(-bp+u)/2]; // solutions mod p
    end if;
    m := p;
    lift := func<x,p,m|x+m*Integers()!(-1/(GF(p)!2*x+b)*((x*(x+b)+c) div m))>;
    for n:=2 to e do
        mm := m*p;
        S := &cat[(2*x+b) mod p eq 0 select ((x*(x+b)+c) mod mm eq 0 select [x+m*i:i in [0..p-1]] else [Integers()|]) else [lift(x,p,m)] : x in S];
        if #S eq 0 then return S; end if;
        m := mm;
    end for;
    return S;
end intrinsic;

intrinsic MonicQuadraticRoots(b::RngIntElt, c::RngIntElt, m::RngIntElt) -> SeqEnum[RngIntElt]
{ Returns the complete list of solutions to x^2+bx+c = 0 in Z/mZ. }
    require m ge 2: "m must be at least 2";
    M := Factorization(m);
    return [CRT([v[i]:i in [1..#M]],[a[1]^a[2]:a in M]) : v in CartesianProduct([MonicQuadraticRoots(b,c,a[1],a[2]):a in M])];
end intrinsic;

intrinsic ChangeRing(f::RngUPolElt, pi::Map) -> RngUPolElt
{ Given f = sum a_i*x^i returns sum pi(a_i)*x^i }
    return PolynomialRing(Codomain(pi))![pi(c):c in Coefficients(f)];
end intrinsic;

intrinsic PrimePowers(B::RngIntElt) -> SeqEnum[RngInt]
{ Ordered list of prime powers q <= B (complexity is O(B log(B) loglog(B)), which is suboptimal but much better than testing individual prime powers). }
    if B lt 2 then return [Integers()|]; end if;
    P := PrimesInInterval(2,B); L := Floor(Log(2,B));
    I := [#P] cat [Index(P,NextPrime(Floor(B^(1/n))))-1:n in [2..L]];
    // sorting is asymptotically stupid (we could merge in linear time or just sieve), but this is not the dominant step for the B we care about
    // even at 10^9 more than half the time is spent enumerating primes
    return Sort(&cat[[p^n:p in P[1..I[n]]]:n in [1..L]]);
end intrinsic;

intrinsic ProperDivisors(N::RngIntElt) -> SeqEnum[RngIntElt]
{ Sorted list of postive proper divisors of the integer N. }
    return N eq 1 select [] else D[2..#D-1] where D:=Divisors(N);
end intrinsic;

intrinsic PrimesInInterval(K::FldNum,min::RngIntElt,max::RngIntElt:coprime_to:=1) -> SeqEnum
{ Primes of K with norm in [min,max]. }
    S := PrimesUpTo(max,K:coprime_to:=coprime_to); 
    return max lt 2 select S else [p:p in S|Norm(p) ge min];
end intrinsic;

// This is often slower than &+[r[2]:r in Roots(f)] but faster when f has lots of roots, e.g. splits completely
intrinsic NumberOfRoots(f::RngUPolElt[FldFin]) -> RngIntElt
{ The number of rational roots of the polynomial f. }
    a := SquareFreeFactorization(f);
    b := [DistinctDegreeFactorization(r[1]:Degree:=1):r in a];
    return &+[a[i][2]*(#b[i] gt 0 select Degree(b[i][1][2]) else 0):i in [1..#a]];
end intrinsic;

intrinsic TracesToLPolynomial (t::SeqEnum[RngIntElt], q::RngIntElt) -> RngUPolElt
{ Given a sequence of Frobenius traces of a genus g curve over Fq,Fq^2,...,Fq^g returns the corresponding L-polynomial. }
    require IsPrimePower(q): "q must be a prime power.";
    R<T> := PolynomialRing(Integers());
    if #t eq 0 then return R!1; end if;
    g := #t;
    // use Newton identities to compute compute elementary symmetric functions from power sums
    e := [t[1]];  for k:=2 to g do e[k] := ExactQuotient((-1)^(k-1)*t[k]+&+[(-1)^(i-1)*e[k-i]*t[i]:i in [1..k-1]],k); end for;
    return R!([1] cat [(-1)^i*e[i]:i in [1..g]] cat [(-1)^i*q^i*e[g-i]:i in [1..g-1]] cat [q^g]);
end intrinsic;

intrinsic PointCountsToLPolynomial (n::SeqEnum[RngIntElt], q::RngIntElt) -> RngUPolElt
{ Given a sequence of point counts of a genus g curve over Fq,Fq^2,...,Fq^g returns the corresponding L-polynomial. }
    return TracesToLPolynomial([q^i+1-n[i] : i in [1..#n]], q);
end intrinsic;

intrinsic LPolynomialToTraces (L::RngUPolElt:d:=0) -> SeqEnum[RngIntElt], RngIntElt
{ Returns the sequence of Frobenius traces for a genus g curve over Fq,Fq^2,...,Fq^g corresponding to the givien L-polynomial of degree 2g (or just over Fq,..Fq^d if d is specified). }
    require Degree(L) gt 0 and IsEven(Degree(L)): "Lpolynomial must have positive even degree 2g";
    g := ExactQuotient(Degree(L),2);
    b,p,e := IsPrimePower(Integers()!LeadingCoefficient(L));
    require b: "Not a valid L-polynomial, leading coefficient is not a prime power";
    require IsDivisibleBy(e,g): "Not a valid L-polynomial, leading coefficient is not a prime power with an integral gth root.";
    q := p^ExactQuotient(e,g);
    L := Reverse(L);
    if d eq 0 then d:=g; end if;
    e := [Integers()|(-1)^i*Coefficient(L,2*g-i):i in [1..d]];
    // use Newton identities to compute compute power sums from elementary symmetric functions;
    t := [e[1]]; for k:=2 to d do t[k] := (-1)^(k-1)*k*e[k] + &+[(-1)^(k-1+i)*e[k-i]*t[i] : i in [1..k-1]]; end for;
    return t, q;
end intrinsic;

intrinsic LPolynomialToPointCounts (L::RngUPolElt:d:=0) -> SeqEnum[RngIntElt], RngIntElt
{ Returns the sequence of point counrs of a genus g curve over Fq,Fq^2,...,Fq^g corresponding to the givien L-polynomial of degree 2g (or just over Fq,..Fq^d if d is specified). }
    t, q := LPolynomialToTraces(L:d:=d);
    if d eq 0 then d := #t; end if;
    return [q^i+1-t[i] : i in [1..d]];
end intrinsic;
