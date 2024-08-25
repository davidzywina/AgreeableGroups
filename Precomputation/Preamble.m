

/*  
    We first load the data that describes the open subgroups H of SL(2,Zhat), up to conjugacy in GL(2,Zhat),
    that contain -I and have genus at most 24.
    This is obtained from the congruence subgroup data of Cummins and Pauli.
*/

filename:="../CPdata/CPdata.dat";  
I:=Open(filename, "r"); 
_,cp_data:=ReadObjectCheck(I); 

load "../EarlierCode/GL2GroupTheory.m";  // Group theory from original open image paper
AttachSpec("../EarlierCode/magma.spec");  // Andrew Sutherland's package for dealing with open subgroups of GL(2,Zhat) and SL(2,Zhat)


// Record for keeping track of data for a modular curve (associate to an open subgroup G of GL(2,Zhat) that contains -I):

NewModularCurveRec := recformat<  
    N, index, degree, genus, v2, v3, vinf, sl2level, level, k, dimMk, dimSk, prec, commutator_index :RngIntElt, 
    gens, cusps, widths, regular, F, F0, f, trdet, pts, key, exceptional_jinvariants, Gc_decomp, high_genus_model, 
        cyclic_invariants, cyclic_models, cyclic_generators, cover_with_same_commutator_subgroup, psi :SeqEnum,   
    has_point, has_infinitely_many_points, has_nonCM_point, is_agreeable, is_entangled, extraneous, is_serre_type_model: BoolElt, 
    G, H, Hc, Gc :GrpMat, 
    Hc_gen, ell_adic_labels : SeqEnum,
    C:Crv, 
    map_to_jline, pi, pi0 :List, 
    sturm: FldRatElt,
    label, sup, CPname: MonStgElt,
    det_index, det_disc :RngIntElt, det_primary, det_field :SeqEnum,
    added: BoolElt
    >;	 

/*  The above record contains more fields than are currently used.  Here are the used fields:  

        N, level:   the level of the group
        G       :   the open subgroup of GL(2,Zhat) given as a subgroup of GL(2,Z/NZ), where N
                    is the level of G (except when the level is 1 since Magma does not like GL(2,Z/1Z)).
                    The group G will always contain all the scalar matrices.
        index   :   the index of G in GL(2,Zhat)
        genus   :   genus of the modular curve X_G
        is_agreeable:  true if G is agreeable and false otherwise

        H       :   the intersection of G with SL(2,Zhat); given as a subgroup of SL(2,Z/NZ)
        sl2level:   the level of H in SL(2,Zhat); it will be a divisor of N
        CPname  :   Cummins-Pauli label of corresponding congruence subgroup of SL(2,Z)
        degree  :   degree of the morphism X_G to the j-line

        Hc      :   the commutator subgroup of G
        commutator_index:   the index of Hc in SL(2,Zhat)

        det_field:  The modular curve X_G is defined over a number K_G that is the compositum
                    of quadratic extensions of Q.  The sequence "det_field" is a minimal list of
                    squarefree integers for which K_G is obtained from Q by adjoining the square-root
                    of each d in the sequence
        det_index:  The degree of the extension K_G/Q; equivalently, the index of det(G) in Zhat^*


        label   :   a string describing the group G if in an associative array
        sup     :   the groups are constructed so that G is contained in another
                    larger group; "sup" is the label of such a group.  This
                    can be used in the future for computing morphisms down to 
                    the j-line
*/
 


function InitializeModularCurve(G,H)
    /*  Creates a record of type "NewModularCurveRec" with G given as a subgroup of GL(2,Z/NZ) and H its interesection with SL(2,Z/NZ).
        We assume -I in H     
    */
    
    if IsFinite(BaseRing(G)) then N:=#BaseRing(G); else N:=1; end if;

    X:=rec<NewModularCurveRec | >;
    
    // Silly step to ensure G and H are of the expected form
    G1:=sub<GL2Ambient(N)|Generators(G)>;
    H1:=sub<SL2Ambient(N)|Generators(H)>;
    H1`SL:=true;
    assert not assigned G1`SL;
    if assigned G`Level then G1`Level:=G`Level; end if;
    if assigned G`Index then G1`Index:=G`Index; end if;
    if assigned G`Order then G1`Order:=G`Order; end if;
    if assigned G`Genus then G1`Genus:=G`Genus; end if;
    if assigned H`Level then H1`Level:=H`Level; end if;
    if assigned H`Index then H1`Index:=H`Index; end if;
    if assigned H`Order then H1`Order:=H`Order; end if;
    if assigned H`Genus then H1`Genus:=H`Genus; end if;
    G:=G1;
    H:=H1;

    // Want the group G modulo its level
    N,G:=GL2Level(G);

    G:=GL2Project(G,N);
    H:=SL2Project(H,N);
        
    //assigns basic quantities
    X`N:=N;  
    X`level:=N;  
    X`sl2level:=SL2Level(H);    
    X`index:=GL2Index(G);
    X`degree:=SL2Index(H);   // assumes -I in H     
    X`det_index:=GL2DeterminantIndex(G);

    G`Level:=X`level;
    H`Level:=X`sl2level;
    G`Index:=X`index;
    H`Index:=X`degree; // assumes -I in H

    G`Order:=GL2Size(N) div G`Index;
    H`Order:=SL2Size(N) div H`Index;

    if not assigned H`Genus then
        H`Genus:=GL2Genus(H);
    end if;
    G`Genus:=H`Genus;
    X`genus:=H`Genus;

    X`G:=G;
    X`H:=H;

    assert X`index eq X`degree * X`det_index;    
  
    U,iota:=UnitGroup(Integers(N));
    D:=sub<U | [ Determinant(g) @@ iota: g in Generators(G) ]>;
    D_qt:=quo<U|D>;
    inv:=PrimaryInvariants(AbelianGroup(D_qt));
    assert &*(inv cat [1]) eq X`det_index; 
    X`det_primary:=inv; 

    // Now compute "det_field"
    if X`det_index eq 1 then 
        X`det_field:=[];
    else   
        DG:=DirichletGroup(N);
        A,phi:=AbelianGroup(DG);

        M:=&*PrimeDivisors(N);
        D:={d: d in Divisors(M)} join {-d: d in Divisors(M)};
        D:=D diff {1};
        D:=[d: d in D | N mod Conductor(KroneckerCharacter(d)) eq 0];
        function sort(x,y)
            if x eq y then return 0; end if;
            if AbsoluteValue(x) gt AbsoluteValue(y) then  return 1; end if; 
            if AbsoluteValue(x) lt AbsoluteValue(y) then  return -1; end if;        
            if y gt 0 then return 1; end if;
            return -1;
        end function;
        Sort(~D,sort);

        U,iota:=UnitGroup(Integers());
        K:=A;
        for g in Generators(G) do
            b:=[  (Integers()!phi(A.i)(Determinant(g))) @@ iota  : i in [1..Ngens(A)] ];
            K:=K meet Kernel(hom<A->U| b>);
        end for;

        seq:=[];
        W:=sub<K|[]>;
        while W ne K do
            for d in D do
                chi:=KroneckerCharacter(d) @@ phi;
                if chi in K and chi notin W then
                    seq:=seq cat [d];
                    W:=sub<K|Generators(W) join {chi}>;
                    break d;
                end if;
            end for;
        end while;
        X`det_field:=seq;
    end if;

    return X;
end function;


function FindCommutatorSubgroupSL(G)
    /* 
        Input:
            G: a subgroup of SL(2,Z/NZ) for some N>1

        Taking the inverse image under the reduction modulo N map, we may view G as an open subgroup of SL(2,Z_N),
        where Z_N is the ring of N-adic integers.
        Let [G,G] be the commutator subgroup of G; it is an open subgroup of SL(2,Z_N).

        Output:
            M:      the level of [G,G] in SL(2,Z_N)
            gens:   generators for the image of [G,G] modulo M
            index:  index of [G,G] in SL(2,Z_N).
    */
    G`SL:=true;  //TODO: dangerous?
    N:=#BaseRing(G);
    P:=PrimeDivisors(N);

    // First consider the prime power case
    if #P eq 1 then
        p:=P[1];
        
        M:=SL2Level(G);
        // Deal directly with the case M=1
        if M eq 1 then
            if p eq 2 then
                return 4, [[3,1,3,0], [2,3,3,1]], 4;
            elif p eq 3 then
                return 3, [[2,2,2,1], [0,1,2,0], [2,0,0,2]], 3;
            else
                return 1, [], 1;
            end if;
        end if;

        G:=SL2Project(G,M);
        if M eq 2 then M:=4; G:=SL2Lift(G,4); end if; 

        repeat
            G_M:=SL2Lift(G,M);     
            S:=CommutatorSubgroup(G_M); S`SL:=true;
       
            G_Mp:=SL2Lift(G,M*p);
            Sp:=CommutatorSubgroup(G_Mp);  Sp`SL:=true;

            i_M:=SL2Index(S);   
            i_Mp:=SL2Index(Sp); 
            
            if  i_M ne i_Mp then
                M:=M*p;
            end if;        
        until i_M eq i_Mp;
    
        M:=SL2Level(S); 
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

        phi:=hom<G->SL(2,Integers(m))| [ChangeRing(G.i,Integers(m)): i in [1..Ngens(G)]]>;
        B:=ChangeRing(Kernel(phi),Integers(q));
        //  B x {I} is a subgroup of GL(2,Z/q) x GL(2,Z/m) = GL(2,Z/N)
        Mp,_,_:=FindCommutatorSubgroupSL(B);        
        M:=M*Mp;
    end for;
    // The level of [G,G] divides M.
    G_:=SL2Lift(G,LCM([M,N]));  
    G_:=SL2Project(G_,M);  
    S:=CommutatorSubgroup(G_);  // have lifted group so that this will be the desired commutator subgroup
    S`SL:=true;

    M,S:=SL2Level(S);
    gens:= [Eltseq(g): g in Generators(S)];
    index:=SL2Index(S);

    return M, gens, index; 
end function;


function FindCPName(H)
    /*
        Input:  H an open subgroup of SL(2,Zhat) that contains -I (given modulo an integer N) and has genus at most 24.

        The group H is conjugate in GL(2,Zhat) to a unique group H' in our sequence "cp_data" that comes from 
        Cummins-Pauli data.

        Output:
            The label describing the group H' and a matrix g that conjugates H into H'.
    */

    H`SL:=true;
    N:=SL2Level(H);
    if N eq 1 then 
        name:=Rep({r`name: r in cp_data | r`level eq 1});
        return name, Identity(H);
    end if;

    assert SL2ContainsNegativeOne(H);

    H1:=SL2Project(H,N);
    genus:=SL2Genus(H1);
    index:=SL2Index(H1);
    assert genus le 24;  

    SL2:=SL2Ambient(N);        
    GL2:=GL2Ambient(N);  

    for r in cp_data do
        if r`index ne index or r`genus ne genus or r`level ne N then    
            continue r;
        end if;
    
        H2:=sub<SL2| r`matgens >;
        H2`Index:=index;
        H2`Genus:=genus;
        H2`Order:=SL2Size(N) div index;
        b,g:= IsConjugate(GL2,H1,H2);
        if b then
            _,red:=ChangeRing(GL2Ambient(#BaseRing(H)),Integers(N));
            return r`name, g @@ red;
        end if;
        
    end for;
    assert false;  // should have been found by completeness of Cummins-Pauli!
end function;

function GL2Conjugate(H, g)
    if not IsFinite(BaseRing(H)) then return H; end if;
    G:=Conjugate(H,g);
    if assigned H`Genus then G`Genus:=H`Genus; end if;
    if assigned H`Level then G`Level:=H`Level; end if;
    if assigned H`Index then G`Index:=H`Index; end if;
    if assigned H`Order then G`Order:=H`Order; end if;
    if assigned H`NegOne then G`NegOne:=H`NegOne; end if;
    if assigned H`SL then G`SL:=H`SL; end if;
    return G;
end function;