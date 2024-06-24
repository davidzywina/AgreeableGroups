// Contains our group theory functions for constructing and dealing with matrix groups; especially subgroups of GL(2,Z/N) and SL(2,Z/NZ).   
// The most involved functions is for computing maximal agreeable subgroups.

function LiftMatrix(A,n)
 /* 
    Input: 
        A: matrix in GL(2,Z/NZ) with N>1,
        n: an integer that is congruent to det(A) modulo N.
    Output:
        A matrix B in M(2,Z) with det(B)=n whose reduction modulo N is A.
 */
    N:=#BaseRing(Parent(A));
    a:=Integers()!A[1,1]; b:=Integers()!A[1,2];
    c:=Integers()!A[2,1]; d:=Integers()!A[2,2];
   
    // The matrix [a,b;c,d] is congruent to A modulo N.
    // We now alter our choices so that a and c are relatively prime.
    if a eq 0 then a:=N; end if;
    if c eq 0 then c:=N; end if;
    if GCD(a,c) ne 1 then
        M:=&*[p: p in PrimeDivisors(a) | GCD(p,N) eq 1];
        ZM:=Integers(M);
        t:=Integers()!( (1-c)*(ZM!N)^(-1));
        c:=c+N*t;
        assert GCD(a,c) eq 1;
    end if;
  
    g:= (n-(a*d-b*c)) div N;  
    _,x0,y0:=Xgcd(a,c);
    x:=g*x0; y:=g*y0;  
    B:=Matrix([[a,b-N*y],[c,d+N*x]]);

    assert GL(2,Integers(N))!B eq A and Determinant(B) eq n;  // check!
    return B;
end function;

function ExpressAsProductOfSL2AndUpperTriangular(A)
 /* 
    Input:
        a matrix A in M(2,Z) with positive determinant
    Output:
        matrices B and C in M(2,Z) satisfying B*C=A such that B has determinant 1 and C is upper triangular with positive diagonal terms.
 */
    a:=A[1,1]; c:=A[2,1]; d:=Determinant(A);   
    error if d le 0, "The matrix A should have positive determinant.";

    if d eq 1 then return A, Matrix([[1,0],[0,1]]); end if;

    if AbsoluteValue(c) gt AbsoluteValue(a) then
        B:=Matrix([[0,-1],[1,0]]);
        B0,A0:=ExpressAsProductOfSL2AndUpperTriangular(B*A);
        return B^(-1)*B0, A0;
    end if;
    
    if c lt 0 then
        B0,A0:=ExpressAsProductOfSL2AndUpperTriangular(-A);
        return -B0, A0; 
    end if;

    if c ne 0 then 
        q,r:=Quotrem(a,c);
        if r le c/2 then
            B:=Matrix([[1,-q],[0,1]]);
        else
            B:=Matrix([[1,-(q+1)],[0,1]]);
        end if;
        B0,A0:=ExpressAsProductOfSL2AndUpperTriangular(B*A);
        return B^(-1)*B0, A0;       
    end if;

    if a lt 0 then
        B:=Matrix([[-1,0],[0,-1]]);
        B0,A0:=ExpressAsProductOfSL2AndUpperTriangular(B*A);
        return B^(-1)*B0, A0;  
    end if;

    return Matrix([[1,0],[0,1]]), A;
end function;

function crt(A,B,N1,N2)
    /* Input:
        N1, N2: integers greater than 1 which are relatively prime
        A: a matrix in GL(2,Z/N1)
        B: a matrix in GL(2,Z/N2)
            (A and B can also be given by a sequence of integers of length 4)
        Output:
            A matrix C in GL(2,Z/N1*N2) whose image modulo N1 and N2 is A and B, respectively.
    */
    GL2:=GL(2,Integers(N1*N2));
    A:=[Integers()!i: i in Eltseq(A)]; 
    B:=[Integers()!i: i in Eltseq(B)];
    return GL2![ CRT([A[i],B[i]],[N1,N2]) : i in [1..4]];
end function;

function gl2Level(G : index:=0)
    /*  Input:
            G : subgroup of GL(2,Z/NZ) for some integer N>1   
        Output:    
            m : the least positive divisor m of N such that G is the full inverse image of its reduction mod m.
        The parameter "index" can be set to the index of G in GL(2,Z/NZ) if already computed.
    */

    N:=#BaseRing(G);
    if index eq 0 then index:=#GL(2,Integers(N)) div #G; end if;
    if index eq 1 then return 1; end if;
    if IsPrime(N) then return N; end if;

    P:=PrimeDivisors(N);    
    for p in P do

        m:=N div p;
        GL2:=GL(2,Integers(m));
        G_:=ChangeRing(G,Integers(m));
        
        if Index(GL2,G_) eq index then    // Equivalently, the level of G divides N/p            
            return gl2Level(G_:index:=index);
        end if;
    end for;
    return N;
end function;

function sl2Level(G : index:=0)
    /*  Input:
            G : subgroup of SL(2,Z/NZ) for some integer N>1        
        Output:    
            m : the least positive divisor m of N such that G is the full inverse image of its reduction mod m.
        The user parameter "index" can be set to the index of G in SL(2,Z/NZ) if already computed.
    */
    N:=#BaseRing(G);
    if index eq 0 then index:=#SL(2,Integers(N)) div #G; end if;
    if index eq 1 then return 1; end if;
    if IsPrime(N) then return N; end if;

    P:=PrimeDivisors(N);    
    for p in P do
        m:=N div p;
        SL2:=SL(2,Integers(m));
        G_:=ChangeRing(G,Integers(m));
        if Index(SL2,G_) eq index then    // Equivalently, the level of G divides N/p 
            return sl2Level(G_:index:=index);
        end if;
    end for;
    return N;
end function;

function sl2Lift(H,m)
    /* Input:
            H : a subgroup of SL(2,Z/nZ) for some n>1
            m : a positive integer that is a multiple of n
        Output:
            The full preimage of H in SL(2,Z/mZ) under the reduction modulo n map.
    */
    n:=#BaseRing(H);  
    assert IsDivisibleBy(m,n);
    if n eq m then return H; end if;

    SL2m:=SL(2,Integers(m));
    //SL2n,pi:=ChangeRing(SL2m,Integers(n));
    assert false notin {Determinant(h) eq 1: h in Generators(H)};  

    a:=&*[p^Valuation(m,p): p in PrimeDivisors(n)]; 
    b:=m div a;

    // Construct a set S that generates the kernel of the reduction map SL(2,Z/aZ) x SL(2,Z/bZ) = SL(2/ZmZ) -> SL(2,Z/nZ)
    S:={ [[1,n,0,1],[1,0,0,1]], [[1,0,n,1],[1,0,0,1]], [[1-n,-n,n,1+n],[1,0,0,1]] };
 
    if b ne 1 then
        T:={ [Integers()!c: c in Eltseq(g)] : g in Generators(SL(2,Integers(b))) };
        S:=S join {[[1,0,0,1],t] : t in T};
    end if;
    S:={ [CRT([c[1][1],c[2][1]],[a,b]), CRT([c[1][2],c[2][2]],[a,b]), 
          CRT([c[1][3],c[2][3]],[a,b]), CRT([c[1][4],c[2][4]],[a,b])] : c in S};

    S:={SL2m!c: c in S}; 

    //H1:=sub<SL2m| S join {g @@ pi: g in Generators(H)} >;

    H1:=sub<SL2m| S join {SL2m!LiftMatrix(g,1): g in Generators(H)} >;
    
    return H1;
end function;



function gl2Lift(G,m)
    /* Input:
            G : a subgroup of GL(2,Z/nZ) for some n>1
            m : a positive integer that is a multiple of n
        Output:
            The full preimage of G in GL(2,Z/mZ) under the reduction modulo n map.
    */

    n:=#BaseRing(G);  
    assert IsDivisibleBy(m,n);
    if n eq m then return G; end if;
    
    m1:=&*[p^Valuation(m,p) : p in PrimeDivisors(n)];
    // We first lift G modulo m1; construct a set of generators gens1
    gens1:=[Eltseq(g): g in Generators(G)];
    gens1:=[[Integers()!a: a in g] : g in gens1];
    if m1 ne n then
        gens1:=gens1 cat [[1,n,0,1],[1,0,n,1],[1-n,-n,n,1+n],[1+n,0,0,1]];
        if Valuation(n,2) eq 1 then
            gens1:=gens1 cat [[1+2*n,0,0,1]];
        end if;
    end if;
    if m1 eq m then
        return sub<GL(2,Integers(m)) | gens1>;
    end if;

    m2:=m div m1;
    assert GCD([n,m2]) eq 1 and m1*m2 eq m;

    // We find a specific set of generators of GL(2,Z/m2Z)
        U,iota:=UnitGroup(Integers(m2));
        gens0:=[Integers()!iota(U.i) : i in [1..Ngens(U)]];
    gens2:=[[1,1,0,1],[0,-1,1,0]] cat [[a,0,0,1]: a in gens0];
    //gens2:=[Eltseq(g): g in Generators(GL(2,Integers(m2)))];
    //gens2:=[[Integers()!a: a in g]: g in gens2];

    gens:=[ [CRT([a[1],1],[m1,m2]), CRT([a[2],0],[m1,m2]), 
             CRT([a[3],0],[m1,m2]), CRT([a[4],1],[m1,m2])]  : a in gens1] cat
          [ [CRT([1,a[1]],[m1,m2]), CRT([0,a[2]],[m1,m2]), 
             CRT([0,a[3]],[m1,m2]), CRT([1,a[4]],[m1,m2])]  : a in gens2];
    
    G_lift:=sub<GL(2,Integers(m)) | gens>;

    return G_lift;
end function;

function FindCommutatorSubgroup(G)
    /* 
        Input:
            G: a subgroup of GL(2,Z/NZ) for some N>1

        Taking the inverse image under the reduction modulo N map, we may view G as an open subgroup of GL(2,Z_N),
        where Z_N is the ring of N-adic integers.
        Let [G,G] be the commutator subgroup of GL(2,Z_N); it is an open subgroup of SL(2,Z_N).

        Output:
            M:      the level of [G,G] in SL(2,Z_N)
            gens:   generators for the image of [G,G] modulo M
            index:  index of [G,G] in SL(2,Z_N).
    */
    N:=#BaseRing(G);
    P:=PrimeDivisors(N);

    // First consider the prime power case
    if #P eq 1 then
        p:=P[1];
        
        M:=gl2Level(G);
        // Deal directly with the case M=1
        if M eq 1 then
            if p ne 2 then
                return 1, [], 1;
            else 
                return 2, [[1,1,1,0]], 2;
            end if;
        end if;

        G:=ChangeRing(G,Integers(M));
        if M eq 2 then M:=4; G:=gl2Lift(G,4); end if;

        repeat
            G_M:=gl2Lift(G,M);     
            S:=CommutatorSubgroup(G_M);
       
            G_Mp:=gl2Lift(G,M*p);
            Sp:=CommutatorSubgroup(G_Mp);

            i_M:=Index(SL(2,Integers(M)),S);
            i_Mp:=Index(SL(2,Integers(M*p)),Sp);
            
            if  i_M ne i_Mp then
                M:=M*p;
            end if;        
        until i_M eq i_Mp;
    
        M:=sl2Level(S); 
        if M eq 1 then return 1, [], 1; end if;

        gens:= [Eltseq( SL(2,Integers(M))!g ): g in Generators(S)];
        return M, gens, i_M;          
    end if;

    // When N is not a prime power, we first find an integer M that is divisible by the level of [G,G].
    // We go prime by prime and use the above computations.
    M:=1;
    for p in P do
        q:= p^Valuation(N,p);
        m:= N div q;

        phi:=hom<G->GL(2,Integers(m))| [ChangeRing(G.i,Integers(m)): i in [1..Ngens(G)]]>;
        B:=ChangeRing(Kernel(phi),Integers(q));
        //  B x {I} is a subgroup of GL(2,Z/q) x GL(2,Z/m) = GL(2,Z/N)
        Mp,_,_:=FindCommutatorSubgroup(B);        
        M:=M*Mp;
    end for;
    // The level of [G,G] divides M.
    G_:=gl2Lift(G,LCM([M,N]));  
    G_:=ChangeRing(G_,Integers(M));  
    S:=CommutatorSubgroup(G_);  // have lifted group so that this will be the desired commutator subgroup

    M:=sl2Level(S);
    S:=ChangeRing(S,Integers(M));
    gens:= [Eltseq(g): g in Generators(S)];
    index:=Index(SL(2,Integers(M)),S);

    return M, gens, index; 
end function;


function IndexOfCommutator(G)
    /*  The group G is a subgroup of GL(2,Z/NZ) with N>1 that we can idenitify with an open subgroup of GL(2,Zhat). 
        This function computes the index [SL(2,Zhat) : [G,G]], where [G,G] is the commutator subgroup of G in GL(2,Zhat).
    */
    _,_,index:=FindCommutatorSubgroup(G);
    N:=#BaseRing(G);
    if IsOdd(N) then index:=2*index; end if;
    return index;
end function;

function ContainsScalars(G)
    // For a subgroup of GL(2,Z/N) with N>1, return true if G contains all the scalar matrices and false otherwise.
    N:=#BaseRing(G);
    GL2:=GL(2,Integers(N));
    U,iota:=UnitGroup(Integers(N));
    return &and [ (GL2![iota(U.i),0,0,iota(U.i)]) in G : i in [1..Ngens(U)] ];
end function;

function AdjoinScalars(G)
    // For a subgroup of GL(2,Z/N) with N>1, return the group obtained by adding all the scalar matrices to G.
    N:=#BaseRing(G); 
    GL2:=GL(2,Integers(N));
    gens:=[G.i: i in [1..Ngens(G)]];
    U,iota:=UnitGroup(Integers(N));
    gens:= gens cat [ GL2![iota(U.i),0,0,iota(U.i)] : i in [1..Ngens(U)] ];
    return sub<GL2|gens>;
end function;

function GL2DetIndex(H)
    // Given a subgroup H of GL(2,Z/NZ), computes the index of det(H) in (Z/NZ)^*
    M,pi:=MultiplicativeGroup(BaseRing(H));
    return Index(M,sub<M|[Inverse(pi)(Determinant(h)):h in Generators(H)]>);
end function;

function IsAgreeable(G)
    /* Input:
            G:  a subgroup of GL(2,Z/N) with N>1.   
                By taking its inverse image, we may view G as an open subgroup of GL(2,Zhat).

            We also allow G to be a modular curve given by a record of type ModularCurveRec (it is given by a group).  
            This is often preferable since some quantities will have been precomputed.

        Output:
            returns true if G is agreeable and false otherwise.
    */
    if Type(G) eq MakeType("Rec") then
        M:=G;
        if M`index eq 1 then return true; end if;  // G=GL(2,Zhat) case

        G:=M`G;
        sl2level:=M`sl2level;
        gl2level:=M`N;
    else
        H:=G meet SL(2,BaseRing(G)); 
        gl2level:=gl2Level(G);
        sl2level:=sl2Level(H);
    end if;

    if GL2DetIndex(G) eq 1 and ContainsScalars(G) then
	    P1:={p: p in PrimeDivisors(gl2level) | p ge 3};
        P2:={p: p in PrimeDivisors(sl2level) | p ge 3};
        if P1 eq P2 then
            return true;
        end if;
    end if;
    return false;
end function;

function MaximalAgreeable(X)
    /* Input: 
            X:  a record of type "ModularCurveRec" corresponding to the modular curve X_G with 
                G a subgroup of GL(2,Z/mZ) with m>1 and det(G)=(Z/mZ)^*.   We assume m is the level of G.

                Lifting G, we can identify it with an open subgroup of GL(2,Zhat).  We assume the group G is agreeable.
       Output:
            a sequence consisting of all maximal agreeable subgroups of G, up to conjugation in GL(2,Zhat), that have the 
            same l-adic images for all primes l.
            
            More precisely, each group is given by a tuple consisting of: 
                - its image in GL(2,Z/MZ) with M its level
                - the level of its intersection with SL(2,Zhat)
                - its index in GL(2,Zhat).
    */

    if X`degree eq 1 then
        // Deal with the j-line directly, since Magma does not like the group GL(2,Z/1)
        H1:=sub<GL(2,Integers(6)) | [[3,5,2,5], [0,1,5,5]]>;
        return [[*H1,6,6*]];
    end if;

    G:=X`G;    
    index0:=X`index;  // Index of G in GL(2,Zhat)

    m:=gl2Level(G); 
    assert X`N eq m;  // check  
    N:=&*PrimeDivisors(m); //product of primes that divide the level m of G

    S1:=[]; S2:=[]; S3:=[]; S4:=[];
    // sequences for the four kinds of maximal agreeable subgroups in the paper; will concatenate at the end.  



    // ******  CASE 1:  *******
    // When gcd(N,2)=1, we find the maximal agreeable subgroups whose level has the same prime divisors as 2N.
    if N mod 2 ne 0 and #G mod 2 eq 0 then        
        G1:=GL(2,Integers(8));
        sub1:=[ H`subgroup : H in NormalSubgroups(G1:OrderEqual:=#G1 div 2) ];   
        sub1:=[ ChangeRing(H,Integers(gl2Level(H))) : H in sub1  ];      
        // Correspond to index 2 subgroups of GL(2,Zhat) whose level is a power of 2; there are 7 of them.

        G2:=G;
        N2:=m;
        sub2:=[ H`subgroup : H in NormalSubgroups(G2:OrderEqual:=#G2 div 2) ];     
        // Correspond to index 2 subgroups of G in GL(2,Zhat) whose level divides some power of N.
        sub2:=[ H: H in sub2 | ContainsScalars(H) ];  // Groups should contain scalars.

        for H2 in sub2 do
            _:=exists(g2){g: g in G2 | g notin H2}; // pick an element in G2 that is not in H2
            for H1 in sub1 do
                N1:=#BaseRing(H1);
                _:=exists(g1){g: g in GL(2,Integers(N1)) | g notin H1}; // pick an element in G1 that is not in H1
                
                // There is a unique proper subgroup of G1 x G2 that surjects onto each factor and
                // contains H1 x H2; it is generated by H1 x H2 and (g1,g2).
                                           
                gens:={ crt(h,[1,0,0,1],N1,N2) : h in Generators(H1)} join { crt([1,0,0,1],h,N1,N2) : h in Generators(H2)};              
                gens:=gens join { crt(g1,g2,N1,N2) };  
                
                Gnew:=sub<GL(2,Integers(N1*N2)) | gens>;  
                Gnew:=ChangeRing(Gnew,Integers(gl2Level(Gnew))); // a little slow, but works
                
                if IsAgreeable(Gnew) then
                    index:=X`index * 2;
                    sl2level:=m * sl2Level(H1 meet SL(2,BaseRing(H1)));

                        //check
                        sl2level_:=sl2Level(Gnew meet SL(2,BaseRing(Gnew)));
                        assert sl2level eq sl2level_; 
                    S1:=S1 cat [ [*Gnew, sl2level, index*] ];
                end if;

            end for;
        end for;
    end if;
   
    // ******  CASE 2:  *******
    // When gcd(N,3)=1, we find the maximal agreeable subgroups whose level has the same prime divisors as 3N.
    if N mod 3 ne 0 and #G mod 6 eq 0 then

        Sym3:=SymmetricGroup(3);  
        Q3,iota3:=quo<GL(2,Integers(3))| CommutatorSubgroup(SL(2,Integers(3)))>;
        _,f3:=IsIsomorphic(Q3,Sym3);
        phi3:=iota3*f3;  
        // A surjective homomorphism phi: GL(2,Z/3Z) -> Sym3; we only need one since the others are obtained by composition 
        // with inner automorphisms, and a different choice would produce conjugate agreeable groups.
        
        BB:=[ H`subgroup: H in NormalSubgroups(G:OrderEqual:=#G div 6) ];      
        for B in BB do
            Q,iotaN:=quo<G|B>;
            b,f:=IsIsomorphic(Q,Sym3);  // again choice of f doesn't matter
            if not b then continue B; end if;
              
            phiN:=iotaN*f;   // a surjective homomorphism G->Sym3 with kernel B
            gens:=           { crt(a,[1,0,0,1],3,X`N) : a in Generators(Kernel(phi3))};
            gens:= gens join { crt([1,0,0,1],b,3,X`N) : b in Generators(Kernel(phiN))};
            gens:= gens join { crt((Sym3![2,3,1]) @@ phi3 ,(Sym3![2,3,1]) @@ phiN,3,X`N) };
            gens:= gens join { crt((Sym3![2,1,3]) @@ phi3 ,(Sym3![2,1,3]) @@ phiN,3,X`N) };    
                
            GL2:=GL(2,Integers(3*X`N));
            H:=sub<GL2 | gens>;

            // Ensure that H has full determinant and contains scalars.
            if GL2DetIndex(H) ne 1 or ContainsScalars(H) eq false then  
                continue B;
            end if;

            sl2level:= sl2Level( H meet SL(2,Integers(3*X`N)) );
            index:=6*X`index;                        
            S2:=S2 cat [[*H,sl2level,index*]];              
        end for;
    end if;

    // ******  CASE 3:  *******
    // When gcd(N,6)=1, we find the maximal agreeable subgroups whose level has the same prime divisors as 6N.
    if GCD([N,6]) eq 1 then
        // G6 is an index 6 subgroup of GL(2,Z/6) whose image mod p is GL(2,Z/p) for p=2 and p=3.
        G6:=sub<GL(2,Integers(6)) | [[ 3, 5, 2, 5 ], [ 0, 1, 5, 5 ]]>;        
        gens:=  { crt([1,0,0,1],b,6,X`N) : b in Generators(G)} join { crt(a,[1,0,0,1],6,X`N) : a in Generators(G6)};
        H:=sub<GL(2,Integers(6*X`N)) | gens>;
        sl2level:=6*X`sl2level;
        index:=6*X`index;
        S3:=S3 cat [[*H,sl2level,index*]];
    end if;
    
    // ******  CASE 4: main case *******
    // It remains to find maximal agreeable subgroups whose level has same prime divisors as N.
    N:=X`N;
    radN:= &*(PrimeDivisors(N)); 
    D:=[d: d in Divisors(radN) | d ne 1 and d le Isqrt(radN)];

    for d1 in D do  
        d2:=radN div d1;
        N1:=&*[p^Valuation(N,p): p in PrimeDivisors(d1)];
        N2:=&*[p^Valuation(N,p): p in PrimeDivisors(d2)];

        G1, modN1:=ChangeRing(G,Integers(N1)); 
        G2, modN2:=ChangeRing(G,Integers(N2));
        B1:=ChangeRing( Kernel(modN2),  Integers(N1) );
        B2:=ChangeRing( Kernel(modN1),  Integers(N2) );
        //B1:=ChangeRing( Kernel( hom<G->G2| [ChangeRing(G.i,Integers(N2))  : i in [1..Ngens(G)]]> ),  Integers(N1) );
        //B2:=ChangeRing( Kernel( hom<G->G1| [ChangeRing(G.i,Integers(N1))  : i in [1..Ngens(G)]]> ),  Integers(N2) );

        // In the computation of M(G) from the paper, we now compute all the possible groups C_1 and C_2.
        // We first compute the group E_i generated by the commutator subgroup of B_i and the scalar matrices.

        M1, gens1:=FindCommutatorSubgroup(B1);
        E1:=sub<SL(2,Integers(M1))|gens1>;
        if IsEven(M1) then
            M1:=2*LCM(4,M1);
            E1:=sl2Lift(E1,M1);
        end if;
        E1:=AdjoinScalars(E1);

        N1:=LCM(N1,M1);
        G1:=gl2Lift(G1,N1);
        B1:=gl2Lift(B1,N1);
        E1:=gl2Lift(E1,N1);


        M2, gens2:=FindCommutatorSubgroup(B2);
        E2:=sub<SL(2,Integers(M2))|gens2>;
        if IsEven(M2) then
            M2:=2*LCM(4,M2);
            E2:=sl2Lift(E2,M2);
        end if;
        E2:=AdjoinScalars(E2);

        N2:=LCM(N2,M2);
        G2:=gl2Lift(G2,N2);
        B2:=gl2Lift(B2,N2);
        E2:=gl2Lift(E2,N2);


        // Compute the possible C1
        Q1,iota1:=quo<B1|E1>; // abelian
        CC1:=[H`subgroup @@ iota1: H in Subgroups(Q1)];
        CC1:=[H: H in CC1 | H ne B1 and IsNormal(G1,H)];
        CC1:=[H: H in CC1 |  not &or[H subset H_ and H ne H_ : H_ in CC1] ];  //maximality of C1

        // Compute the possible C2
        Q2,iota2:=quo<B2|E2>;
        CC2:=[H`subgroup @@ iota2: H in Subgroups(Q2)];
        CC2:=[H: H in CC2 | H ne B2 and IsNormal(G2,H)];
        CC2:=[H: H in CC2 |  not &or[H subset H_ and H ne H_ : H_ in CC2] ];   //maximality of C2

        // Keep track of quotients G1/C1 and G2/C2 with quotient maps
        QQ1:=[]; iota1:=[];
        for i in [1..#CC1] do
            Q, iota:= quo<G1|CC1[i]>;
            QQ1:=QQ1 cat [Q];
            iota1:=iota1 cat [iota];
        end for;
        QQ2:=[]; iota2:=[];
        for i in [1..#CC2] do
            Q, iota:= quo<G2|CC2[i]>;
            QQ2:=QQ2 cat [Q];
            iota2:=iota2 cat [iota];
        end for;
        
        // Keep track of (abelian) groups B1/C1 and B2/C2
        BC1:=[ quo<B1|C> : C in CC1];
        BC2:=[ quo<B2|C> : C in CC2];
        assert &and [IsAbelian(Q): Q in BC1 cat BC2];
        
        G_:=gl2Lift(G,N1*N2);

        for i in [1..#CC1] do
        for j in [1..#CC2] do
            // Want G1/C1 isomorphic to G2/C2 and B1/C1 isomorphic to B2/C2.
            if not IsIsomorphic(BC1[i],BC2[j]) or not IsIsomorphic(QQ1[i],QQ2[j]) then
                continue j;
            end if;

            C1:=CC1[i]; 
            C2:=CC2[j];

            Q1:=QQ1[i]; 
            Q2:=QQ2[j];
            alpha1:=iota1[i];
            alpha2:=iota2[j];

            D,alpha:=DirectProduct([Q1,Q2]);   // isomorphic to (G1 x G2)/(C1 x C2)
            Dset:={g: g in D};
            Dalt:={g: g in CartesianProduct([Q1,Q2])};
            phi:=map<Dset->Dalt| [ <alpha[1](a[1])*alpha[2](a[2]),a> : a in Dalt] >;
            gens_:={   alpha[1](alpha1(g)) * alpha[2](alpha2(g)) : g in Generators(G_) };
            GQ:=sub<D| gens_>;  // Image of G in (G1 x G2)/(C1 x C2) = (G1/C_1) x (G2/C_2)

            ind:=#BC1[i]; assert #GQ mod ind eq 0;   // order of the groups B1/C1 and B2/C2
            
            // The maximal agreeable subgroups H we are trying to construct have index "ind" in G
            // and lie between G and C1 x C2.
            HH:=[H`subgroup: H in Subgroups(GQ: OrderEqual:=#GQ div ind)]; 

            gens0 := {crt(A,[1,0,0,1],N1,N2): A in Generators(C1)} join {crt([1,0,0,1],B,N1,N2): B in Generators(C2)};
            assert {GL(2,Integers(N1*N2))!g: g in gens0 } subset G_;

            for H in HH do
                gens:={phi(h): h in Generators(H)};    // generators in (G1/C_1) x (G2/C_2)                                    
                gens:=  gens0 join {  crt(a[1] @@ alpha1, a[2] @@ alpha2, N1,N2) : a in gens   };
                // generators as subgroup of G

                GL2:=GL(2,Integers(N1*N2));
                M:=sub<GL2 | gens>;

                // We only want groups with full determinant.                
                if GL2DetIndex(M) ne 1 then
                    continue H;
                end if;

                // Our group should have the same mod N1 and N2 images as G_
                if ChangeRing(G_,Integers(N1)) ne ChangeRing(M,Integers(N1)) or 
                   ChangeRing(G_,Integers(N2)) ne ChangeRing(M,Integers(N2)) then 
                   continue H;
                end if;

                index := X`index * ind;                                            
                N_:=gl2Level(M: index:=index ); 
                M:=ChangeRing(M,Integers(N_));
                sl2level:= sl2Level( M meet SL(2,Integers(N_)) );  // can be slow
                assert {p: p in PrimeDivisors(N_)| p ge 3} eq {p: p in PrimeDivisors(sl2level)| p ge 3};

                S4:=S4 cat [[*M,sl2level,index*]];                  
            end for;

        end for;
        end for;
      
    end for;

    S:=S1 cat S2 cat S3 cat S4;

    //check!
    for H_ in S do
        H:=H_[1];
        N:=#BaseRing(H);
        assert N mod X`N eq 0;
        G:=gl2Lift(X`G,N);

        for p in PrimeDivisors(N) do
            m:=p^Valuation(N,p);
            assert ChangeRing(G,Integers(m)) eq ChangeRing(H,Integers(m));
            assert H subset G;
        end for;

    end for;

    //print "                                                           ",[#S1,#S2,#S3,#S4];
    return S;
end function;


function IsUnentangled(G)
    // For a subgroup G of GL(2,Z/N), we say it is unentangled if G is isomorphic to the product of its
    // images in GL(2,Z/qZ) where q varies over the maximal prime powers dividing N.
    // The function returns true if and only if G is unentangled
    N:=#BaseRing(G);
    Q:=[p^Valuation(N,p): p in PrimeDivisors(N)];
    return #G eq &*[#ChangeRing(G,Integers(q)): q in Q];
end function;


// The remaining functions are from earlier joint work with Andrew Sutherland.  We will use "GL2ContainsCC" later.

function GL2IsSubModule(A,B)
    // Given invariants A and B of two Z/nZ-submodules of Z/nZ x Z/nZ, return true if A is isomorphic to a submodule of B
    i:=#B-#A;
    if i lt 0 then return false; end if;
    for j in [1..#A] do if not IsDivisibleBy(B[i+j],A[j]) then return false; end if; end for;
    return true;
end function;

function GL2ModuleInvariants(V)
    // Compute the abelian group invariants of a Z/nZ-submodule of Z/nZ x Z/nZ 
    // (which Magma apparently doesn't now is an abelian group)
    if Dimension(V) eq 0 then return []; end if;
    if Dimension(V) eq 1 then return [#V]; end if;
    assert Dimension(V) le 2;
    r1:=#sub<V|V.1>;  r2:=#sub<V|V.2>;
    return [GCD(r1,r2),LCM(r1,r2)];
end function;

function GL2FixModule(H)
    // Given a subgroup of GL(2,Z/nZ), computes the invariants of the sub-module of Z/nZ x Z/nZ fixed by the left action of G 
    // (returns a list [], [a], or [a,b] with a|b|n)
    V := Eigenspace(Identity(H),1);
    for h in Generators(H) do V:= V meet Eigenspace(Transpose(h),1); end for;   // take transpose so that we  are using left actions 
                                                                                //(Magma default is right action!)
    return GL2ModuleInvariants(V);
end function;

function GL2ContainsCC(H)
    /* Given a subgroup H of GL(2,Z/nZ), returns true if H contains an element corresponding to complex conjugation.  
      This is tested by checking det = -1, tr = 0, and fixing a maximal cyclic subgroup 
      (note: this is faster than checking for an element conjugate to [1,0,0,-1] or [1,1,0,-1])
    */
    N:=#BaseRing(H);
    N0:=2^Valuation(N,2)* &*([1] cat [p: p in PrimeDivisors(N) | p ne 2]);
    if N0 lt N then
        return GL2ContainsCC(ChangeRing(H,Integers(N0)));
    end if;
    
    return exists {h:h in H|Determinant(h) eq -1 and Trace(h) eq 0 and GL2IsSubModule([#BaseRing(H)],GL2FixModule(sub<H|h>)) };
end function;


