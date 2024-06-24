/*
    We compute all the agreeable subgroups of GL(2,Zhat) of genus at most 1, up to conjugacy, and save them to a file.

*/
//  nohup magma -t 32 "ComputeAgreeableGroupsOfGenusAtMost1.m" &

NewModularCurveRec := recformat<
    CPname: MonStgElt,    
    N, index, degree, genus, v2, v3, vinf, sl2level, level, k, dimMk, dimSk, prec, commutator_index :RngIntElt, 
    gens, cusps, widths, regular, F, F0, f, trdet, pts, key, exceptional_jinvariants, Gc_decomp, high_genus_model, 
        cyclic_invariants, cyclic_models, cyclic_generators, cover_with_same_commutator_subgroup, psi :SeqEnum,   
    has_point, has_infinitely_many_points, has_nonCM_point, is_agreeable, is_entangled, extraneous, is_serre_type_model: BoolElt, 
    G, H, Hc, Gc :GrpMat, 
    Hc_gen, ell_adic_labels : SeqEnum,
    C:Crv, 
    map_to_jline, pi :List, 
    sturm: FldRatElt,
    label, sup: MonStgElt,
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
 
load "../EarlierCode/GL2GroupTheory.m";
AttachSpec("../EarlierCode/magma.spec");


function InitializeModularCurve(X : level_known:=false)
    /*  This function computes some of the fields for a record X of type "NewModularCurveRec"
        assuming X`G and X`H have been given already.     We assume -I in H     
    */

    G:=X`G;
    H:=X`H; 
    H`SL:=true;
    N,G:=GL2Level(G);
    H:=SL2Project(H,N);
    
    X`N:=N;  X`level:=N;  
    X`sl2level:=SL2Level(H);    
    X`index:=GL2Index(G);
    X`degree:=SL2Index(H);   // assumes -I in H     
    X`det_index:=GL2DeterminantIndex(G);
    assert X`index eq X`degree * X`det_index;    

    X`G:=G;
    X`H:=H;

  
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
    G`SL:=true; 
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


/* We load the data of Cummins-Pauli on genus 0 and genus 1 congruence
    subgroups of SL(2,Z) that contain -I.
*/
filename:="../CPdata/CPdata.dat";  // genus 0 and 1 congruence subgroup data
I:=Open(filename, "r"); 
_,L:=ReadObjectCheck(I); 

comm_map:=AssociativeArray();
comm_level:=AssociativeArray();  

"Computing commutator subgroups of congruence subgroups of genus 0 and 1.";

/* We consider the congruence subgroups Gamma of genus 0 and 1, up to conjugacy in GL(2,Z), that contain -I.
   The group Gamma corresponds to an open subgroup H of SL(2,Zhat).   We compute a surjective homomorphism
   phi: H ->Q, with Q a finite group, so that the kernel of phi is the commutator subgroup [H,H].   
   We save this data to the array "comm_map". Our group H is given modulo the level of [H,H]; we record
   this level in the array "comm_level".
*/
for Gamma in L do  // run over Cummins-Pauli data

    Gamma`name;
    if Gamma`level ne 1 then 
        level:=Gamma`level;
        matgens:=Gamma`matgens;
    else
        level:=2;
        matgens:=[[1,1,0,1],[1,0,1,1]];
    end if;
    SL2:=SL2Ambient(level);
    H0:=sub<SL2|matgens>; H0`SL:=true;
    assert SL2![-1,0,0,-1] in H0;

    M1,gens1,index1:=FindCommutatorSubgroupSL(H0);
    H1:=SL2Lift(H0,M1); 
    Q1,iota1:=quo< H1 | sub<SL(2,Integers(M1))|gens1> >;

    M2:=1;
    if GCD(M1,2) eq 1 then M2:=M2*4; end if;
    if GCD(M1,3) eq 1 then M2:=M2*3; end if;
    if M2 ne 1 then
        Q2,iota2:=quo<SL2Ambient(M2) | CommutatorSubgroup(SL2Ambient(M2)) >;
    else
        M2:=2;
        Q2,iota2:=quo<SL(2,Integers(2)) | SL(2,Integers(2)) >; 
        // This is just the trivial group.  Really want M1=1, but magma doesn't like matrices in M_2(Z/(1)).
    end if;    

    Q,alpha:=DirectProduct(Q1,Q2);  // This group is isomorphic to H/[H,H]
    assert IsAbelian(Q);

    M:=LCM(M1,M2);
    H:=SL2Lift(H0,M);

    iota:=hom<H->Q | [ alpha[1](iota1(H.i)) * alpha[2](iota2(H.i)) : i in [1..Ngens(H)] ] >;

    assert #Q*SL2Index(H)/index1 eq #Q2;

    comm_map[Gamma`name]:=iota;
    comm_level[Gamma`name]:=M;  
end for;


"Computing groups that include all agreeable subgroups of GL(2,Zhat).";

Families:=AssociativeArray();

/* We will compute finitely many open subgroups G of GL(2,Zhat) that, up to conjugacy, 
   include those that satisfy the following:
    - G is agreeable,
    - X_G has genus at most 1.
*/

for r in L do
    label:=1; 
    r`name;

    // We vary over all the congruence subgroups of SL(2,Z) that contain -I, up to conjugacy in GL(2,Z), with genus 0 or 1;
    // it gives rise to an open subgroup H of SL(2,Zhat) containing -I.

    if r`level ne 1 then 
        level:=r`level;
        matgens:=r`matgens;
    else
        // j-line treated special since Magma does not like SL(2,Z/1)        
        level:=2;
        matgens:=[[1,1,0,1],[1,0,1,1]];
    end if;
    SL2:=SL2Ambient(level);   //SL(2,Integers(level));
    H:=sub<SL2|matgens>; H`SL:=true;
    assert SL2![-1,0,0,-1] in H;

    level:=LCM(12,level) * 2;
    H:=SL2Lift(H,level);
        
    // Adjoin scalars to H, to get a group G0 that we view as an open subgroup
    // of GL(2,Zhat) with level dividing "level".
    G0:=AdjoinScalars(H);

    // We want the intersection of G0 and SL(2,Zhat) to be H; 
    // if not, we go to the next congruence subgroup

    a:=SL2Order(SL2Intersection(G0))/SL2Order(H);
    if a gt 1 then continue r; end if;
    
    // We are looking for agreeable subgroups G of GL(2,Zhat) containing G0 whose intersection with
    // SL(2,Zhat) is H.  Such groups G will lie in the normalizer G0.  
    // Moreover, the level of G divides #BaseRing(G0) by our choices.

    N:=Normalizer(GL(2,BaseRing(G0)),G0);
    Q,iota:=quo<N|G0>;

    // Construct sequence "MM" of subgroups of Q corresponding to desired subgroups G
    S0:=SL2Intersection(N);  // todo: OK?? OLD: N meet SL(2,BaseRing(G0));
    S1:=iota(S0);
    MM:=[M`subgroup: M in Subgroups(Q)];
    MM:=[M: M in MM | #(M meet S1) eq 1];
    //assert true notin { IsConjugate(Q,MM[i],MM[j]) : i,j in [1..#MM] | i lt j };
  
    for M_ in MM do
        G:=M_ @@ iota;
        
        X:=rec<NewModularCurveRec | G:=G, H:=SL2Lift(H,#BaseRing(G)), CPname:=r`name, genus:=r`genus>;
        X:=InitializeModularCurve(X);

        if X`N eq 1 then 
            X`Hc:=CommutatorSubgroup(GL(2,Integers(2)));
            X`commutator_index:=2;
            X`is_agreeable:=true;

            label_:=IntegerToString(X`N) cat "." cat X`CPname cat "." cat IntegerToString(label);
            Families[label_]:=X;
            Families[label_]`label:=label_;
            label:=label+1;

            label_;
            continue M_;
        end if;

        CPname:=X`CPname;
        M:=comm_level[CPname];
        phi:=comm_map[CPname];
        Q:=Codomain(phi);

        G:= GL2Project(GL2Lift(X`G,LCM(X`N,M)), M);

        // Compute Hc=[G,G]
        found:=false;
        W:=sub<Q|{ phi(a*b*a^(-1)*b^(-1)): a,b in Generators(G)}>;
        Hc:=W @@ phi; 

        // Since we only used commutators of a set of generators of G, it is not clear that 
        // Hc is the correct thing.  We possibly increase it so that it stable under
        // conjugation by G (which will mean we have the right thing)
        while not found do
            Hc:=W @@ phi;
            found:=true;
            for g in Generators(G) do
                W_:=sub<Q|{phi(g*h*g^(-1)) : h in Generators(Hc)}>;
                if W_ ne W then
                    W:=sub<Q|Generators(W) join Generators(W_)>;
                    found:=false;
                    break g;
                end if;
            end for;
        end while;
        
        Hc`SL:=true;
        D:=SL2Level(Hc);

        Hc:=SL2Project(Hc,D);
        X`Hc:=Hc;
        X`commutator_index:=SL2Index(Hc);

        // We now check if we are dealing with an agreeable group.
        assert ContainsScalars(X`G);

        // Note that X`N is the level of X`G viewed as a subgroup of GL(2,Zhat).
        // Note that the group X`Hc is given modulo its level.
        X`is_agreeable:= Set(PrimeDivisors(X`N)) subset Set(PrimeDivisors(#BaseRing(X`Hc)));

        if X`is_agreeable then            
            label_:=IntegerToString(X`N) cat "." cat X`CPname cat "." cat IntegerToString(label);
            Families[label_]:=X;
            Families[label_]`label:=label_;
            label:=label+1;

            label_;
        end if;
    end for; 
end for;    


"Saving to file.";
// Write groups found to file.
I:=Open("../Data/agreeable_groups_genus_0_and_1.dat", "w");
for k in Keys(Families) do
    x:=Families[k];
    WriteObject(I, x);
end for;

"Done.";
