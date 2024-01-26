

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
    Hc_gen: SeqEnum, 
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
        sl2level:   the level of H
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


function InitializeModularCurve(X : level_minimal:=false)
    /*  This function computes some of the fields for a record X
        assuming X`G and X`H have been given already.
        If "level_minimal" is true, then we make G a subgroup of GL(Z/NZ) where N is
        the level of G.
    */

    if level_minimal then
        N:=#BaseRing(X`G);
    else
        N:=gl2Level(X`G);
    end if;
    X`N:=N;  X`level:=N;

    if N eq 1 then        
        X`index:=1;
        X`degree:=1;
        X`det_index:=1; 
        X`det_primary:=[]; 
        X`det_field:=[];
        X`sl2level:=1;
        return X;
    end if;
    
    if N ne #BaseRing(X`G) then
        X`G:=ChangeRing(X`G,Integers(N));
        X`H:=ChangeRing(X`H,Integers(N));
    end if;
    X`sl2level:=sl2Level(X`H);

    N:=X`N;
    G:=X`G;
    H:=X`H;
    
    X`index:=Index(GL(2,Integers(N)),G);
    X`degree:=Index(SL(2,Integers(N)),H);            
    X`det_index:=GL2DetIndex(G);
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
    N:=#BaseRing(G);
    P:=PrimeDivisors(N);

    // First consider the prime power case
    if #P eq 1 then
        p:=P[1];
        
        M:=sl2Level(G);
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

        G:=ChangeRing(G,Integers(M));
        if M eq 2 then M:=4; G:=sl2Lift(G,4); end if; 

        repeat
            G_M:=sl2Lift(G,M);     
            S:=CommutatorSubgroup(G_M);
       
            G_Mp:=sl2Lift(G,M*p);
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

        phi:=hom<G->SL(2,Integers(m))| [ChangeRing(G.i,Integers(m)): i in [1..Ngens(G)]]>;
        B:=ChangeRing(Kernel(phi),Integers(q));
        //  B x {I} is a subgroup of GL(2,Z/q) x GL(2,Z/m) = GL(2,Z/N)
        Mp,_,_:=FindCommutatorSubgroupSL(B);        
        M:=M*Mp;
    end for;
    // The level of [G,G] divides M.
    G_:=sl2Lift(G,LCM([M,N]));  
    G_:=ChangeRing(G_,Integers(M));  
    S:=CommutatorSubgroup(G_);  // have lifted group so that this will be the desired commutator subgroup

    M:=sl2Level(S);
    S:=ChangeRing(S,Integers(M));
    gens:= [Eltseq(g): g in Generators(S)];
    index:=Index(SL(2,Integers(M)),S);

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
    // Find group H0 in SL(2,Z/level) corresponding to Gamma
    Gamma`name;
    if Gamma`level ne 1 then 
        level:=Gamma`level;
        matgens:=Gamma`matgens;
    else
        level:=2;
        matgens:=[[1,1,0,1],[1,0,1,1]];
    end if;
    SL2:=SL(2,Integers(level));
    H0:=sub<SL2|matgens>;
    assert SL2![-1,0,0,-1] in H0;

    M1,gens1,index1:=FindCommutatorSubgroupSL(H0);
    H1:=sl2Lift(H0,M1);
    Q1,iota1:=quo< H1 | sub<SL(2,Integers(M1))|gens1> >;

    M2:=1;
    if GCD(M1,2) eq 1 then M2:=M2*4; end if;
    if GCD(M1,3) eq 1 then M2:=M2*3; end if;
    if M2 ne 1 then
        Q2,iota2:=quo<SL(2,Integers(M2)) | CommutatorSubgroup(SL(2,Integers(M2))) >;
    else
        M2:=2;
        Q2,iota2:=quo<SL(2,Integers(2)) | SL(2,Integers(2)) >;
        // This is just the trivial group.  Really want M1=1, but magma doesn't like matrices in M_2(Z/(1)).
    end if;    

    Q,alpha:=DirectProduct(Q1,Q2);  // This group is isomorphic to H/[H,H]
    assert IsAbelian(Q);

    M:=LCM(M1,M2);
    H:=sl2Lift(H0,M);

    iota:=hom<H->Q | [ alpha[1](iota1(H.i)) * alpha[2](iota2(H.i)) : i in [1..Ngens(H)] ] >;

    assert #Q*Index(SL(2,Integers(M)),H)/index1 eq #Q2;

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

label:=0;  // TODO(?): add a meaningful label!
for r in L do
    r`name;
    // We vary over all the congruence subgroups of SL(2,Z) that contain -I, up to conjugacy in GL(2,Z), with genus 0 or 1;
    // it gives rise to an open subgroup H of SL(2,Zhat) containing -I.

    if r`level ne 1 then 
        level:=r`level;
        matgens:=r`matgens;
    else
        // j-line treated special since magma does not like SL(2,Z/1)        
        level:=2;
        matgens:=[[1,1,0,1],[1,0,1,1]];
    end if;
    SL2:=SL(2,Integers(level));
    H:=sub<SL2|matgens>;
    assert SL2![-1,0,0,-1] in H;
    
    level:=LCM(12,level) * 2;
    H:=sl2Lift(H,level);
        
    // Add scalars to H, to get a group G0 that we view as an open subgroup
    // of GL(2,Zhat) with level dividing "level".
    G0:=AdjoinScalars(H);

    // We want the intersection of G0 and SL(2,Zhat) to be H; 
    // if not, we go to the next congruence subgroup
    a:=#(SL(2,BaseRing(G0)) meet G0)/#H;
    if a gt 1 then continue r; end if;
    
    // We are looking for agreeable subgroups G of GL(2,Zhat) containing G0 whose intersection with
    // SL(2,Zhat) is H.  Such groups G will lie in the normalizer G0.  
    // Moreover, the level of G divides #BaseRing(G0) by our choices.

    N:=Normalizer(GL(2,BaseRing(G0)),G0);
    Q,iota:=quo<N|G0>;

    // Construct sequence "MM" of subgroups of Q corresponding to desired subgroups G
    S0:=N meet SL(2,BaseRing(G0));
    S1:=iota(S0);
    MM:=[M`subgroup: M in Subgroups(Q)];
    MM:=[M: M in MM | #(M meet S1) eq 1];
    
    //assert true notin { IsConjugate(Q,MM[i],MM[j]) : i,j in [1..#MM] | i lt j };
    
    for M in MM do
        G:=M @@ iota;

        X:=rec<NewModularCurveRec | G:=G, H:=H, CPname:=r`name, genus:=r`genus>;
        X:=InitializeModularCurve(X);

        label_:=IntegerToString(label);
        Families[label_]:=X;
        Families[label_]`label:=label_;
        label:=label+1;

        label;
    end for;
 
end for;    


"Computing commutator subgroups of our groups.";
for k in Sort([k: k in Keys(Families)]) do
    k;

    N:=Families[k]`N;
    if N eq 1 then 
        Families[k]`Hc:=CommutatorSubgroup(GL(2,Integers(2)));
        Families[k]`commutator_index:=2;
        continue k;
    end if;

    CPname:=Families[k]`CPname;
    M:=comm_level[CPname];
    phi:=comm_map[CPname];
    H:=Domain(phi);
    Q:=Codomain(phi);

    G:= ChangeRing(gl2Lift(Families[k]`G,LCM(N,M)), Integers(M));

    // Compute Hc=[G,G]
    found:=false;
    W:=sub<Q|{ phi(a*b*a^(-1)*b^(-1)): a,b in Generators(G)}>;
    Hc:=W @@ phi;

    //Since we only used commutators of generators of G, it is not clear that 
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

    //We now compute the level D of Hc;  the code "D:=sl2Level(Hc);" is too slow here.
    D:=M;
    for d in Sort([d: d in Divisors(M) | d gt 1 and d mod Families[k]`sl2level eq 0]) do
        Hd,red:=ChangeRing(H,Integers(d));
        ker_red:=Kernel(red);
        if phi(ker_red) subset W then
            D:=d;
            break d;
        end if;
    end for;    

    Hc:=ChangeRing(Hc,Integers(D));
    Families[k]`Hc:=Hc;
    Families[k]`commutator_index:=Index(SL(2,BaseRing(Hc)),Hc);
end for;


"Removing groups that are not agreeable.";
//  Some of our groups Families[k]`G need not be agreeable; we remove these.
keys:=Keys(Families);
for k in keys do
    X:=Families[k];
    if X`N eq 1 then continue k; end if;
    assert ContainsScalars(X`G);

    // Note that X`N is the level of X`G viewed as a subgroup of GL(2,Zhat).
    // Note that the group X`Hc will be given modulo its level now.
    if Set(PrimeDivisors(X`N)) subset Set(PrimeDivisors(#BaseRing(X`Hc))) then continue k; end if;

    //  Group is not agreeable and needs to be removed! 
    Remove(~Families,k);
end for;

for k in Keys(Families) do
    Families[k]`is_agreeable:=true;  // all the remaining groups are agreeable
end for;



"Conjugating groups so we have small index inclusions.";

base:=Rep({k: k in Keys(Families) | Families[k]`N eq 1});
todo:={k: k in Keys(Families)} diff {base};

while todo ne {} do    
    "todo",#todo;
    min:=Minimum({ Families[k]`index: k in todo});
    k:=Rep({k: k in todo | Families[k]`index eq min});

    N:=Families[k]`N;
    assert N ne 1;
    
    G:=Families[k]`G;
    GL2:=GL(2,Integers(N));
    H:=Families[k]`H;

    // First look for quadratic covers
    NG:=Normalizer(GL2,G);
    T:=Transversal(NG,G);
    T:=[t: t in T | t^2 in G and t notin G ]; 
    if #T ne 0 then
        ind:=[ GL2DetIndex(sub<GL2|Generators(G) join {t}>) : t in T];
        d:=Minimum(ind);
        T:=[T[i]: i in [1..#T] | ind[i] eq d];
    end if;

    if #T eq 0 then
        T:=[t: t in Transversal(GL2,G) | t notin G];
        ind:=[Index( sub<GL2|Generators(G) join {t}> ,G) : t in T];
        d:=Minimum(ind);
        T:=[T[i]: i in [1..#T] | ind[i] eq d];
    end if;
        
    t:=T[1];

    G0:=sub<GL2| Generators(G) join {t}>;
    N0:=gl2Level(G0);
    if N0 eq 1 then
        Families[k]`sup:=base;
        todo:=todo diff {k};                
    else
        G0:=ChangeRing(G0,Integers(N0));
        GL2:=GL(2,BaseRing(G0));
        ind0:=Index(GL2,G0);
        ind1:=GL2DetIndex(G0);

        found:=false;
        for k0 in Keys(Families) do
            X:=Families[k0];
            if X`N ne N0 or X`index ne ind0 or X`det_index ne ind1 then
                continue k0;
            end if;        
            b,A:=IsConjugate(GL2,G0,X`G);
            if b then 
                found:=true; 
                Families[k]`sup:=k0;

                // lift A to GL(2,Z/N)
                GL2_,red:=ChangeRing(GL(2,Integers(N)),Integers(N0));
                A:=(GL2_!A) @@ red;
                
                //Conjugate our groups
                Families[k]`G:=Conjugate(Families[k]`G,A);
                Families[k]`H:=Conjugate(Families[k]`H,A);        

                Hc:=Families[k]`Hc;
                N1:=LCM(N,#BaseRing(Hc));
                GL2_,red:=ChangeRing(GL(2,Integers(N1)),Integers(N));
                A:=(GL2_!A) @@ red;
                A:=GL(2,BaseRing(Hc))!A;
                Families[k]`Hc:=Conjugate(Hc,A); 

                todo:=todo diff {k};
                break k0;
            end if;
        end for;
    
        if not found then
            // add a new group to our list
            H0:=G0 meet SL(2,BaseRing(G0));
            X:=rec<NewModularCurveRec | G:=G0, H:=H0>;
            X:=InitializeModularCurve(X : level_minimal:=true);

            M0,gens0,index0:=FindCommutatorSubgroup( gl2Lift(G0,LCM(#BaseRing(G0),6)) );
            Hc:=sub<SL(2,Integers(M0))|gens0>;
            
            X`Hc:=Hc;
            X`commutator_index:=Index(SL(2,Integers(M0)),Hc);
            X`added:=true;  // remember it was added

            assert X`commutator_index eq index0;

            label_:=IntegerToString(label);
            Families[label_]:=X;
            Families[label_]`label:=label_;
            label:=label+1;

            todo:=todo join {label_};
        end if;
    end if;
    
end while;


"Deal with recently added groups.";
// We have added new groups.  Assign a Cummins-Pauli label and add their genus.
keys0:={k: k in Keys(Families) | not assigned Families[k]`CPname};
for k in keys0 do
    H:=Families[k]`H;
    N:=sl2Level(H);
    if N eq 1 then 
        Families[k]`CPname:=[r: r in L | r`level eq 1][1]`name;
        continue k; 
    end if; 
    H:=ChangeRing(H,Integers(N));
    for r in L do
        if r`level eq N then
            b:=IsConjugate(GL(2,Integers(N)),H,sub<SL(2,Integers(N))|r`matgens>);
            if b then
                Families[k]`CPname:=r`name; 
                Families[k]`genus:=r`genus;                 
                continue k;
            end if;
        end if;
    end for;
    assert false; // shouldn't get to here!
end for;

// For the recently added groups, work out which are agreeable
for k in Keys(Families) do 
    if assigned Families[k]`is_agreeable then continue k; end if;
    G:=Families[k]`G;
    Hc:=Families[k]`Hc;
    assert ContainsScalars(G); 

    if Set(PrimeDivisors(#BaseRing(G))) subset Set(PrimeDivisors(#BaseRing(Hc))) then 
        assert false;  
        // We should not be in this case since this would mean we missed an agreeable group of genus at most 1.
    else
        Families[k]`is_agreeable:=false;
    end if;
end for;

"For the groups constructed, find a smaller set of generators.";
// We look for a relatively small list of generators of Hc; this is done in a rather dumb way
for k in Keys(Families) do
    Hc:=Families[k]`Hc;
    N0:=#BaseRing(Hc);
    gens1:={};
    B:=sub<SL(2,Integers(N0)) | gens1>;
    while B ne Hc do
        T:=[t: t in Transversal(Hc,B) | t notin B];
        m:=Maximum({#sub<SL(2,Integers(N0))|gens1 join {h}> : h in T});
        assert exists(a){h: h in T | #sub<SL(2,Integers(N0))|gens1 join {h}> eq m };
        gens1:=gens1 join {a};
        B:=sub<SL(2,Integers(N0)) | gens1>;
    end while;
    Hc:=B;
    Families[k]`Hc:=Hc;
end for;

// We look for a relatively small list of generators of H; this is done in a rather dumb way
for k in Keys(Families) do
    if Families[k]`N eq 1 then continue k; end if;
    H:=Families[k]`H;
    N0:=Families[k]`sl2level;
    N :=Families[k]`N;
    if N0 eq 1 then
        Families[k]`H:=SL(2,Integers(N));
        continue k; 
    end if;
    H:=ChangeRing(H,Integers(N0));

    gens1:={};
    B:=sub<SL(2,Integers(N0)) | gens1>;
    while B ne H do
        T:=[t: t in Transversal(H,B) | t notin B];
        m:=Maximum({#sub<SL(2,Integers(N0))|gens1 join {h}> : h in T});
        assert exists(a){h: h in T | #sub<SL(2,Integers(N0))|gens1 join {h}> eq m };
        gens1:=gens1 join {a};
        B:=sub<SL(2,Integers(N0)) | gens1>;
    end while;
    H:=sl2Lift(B,N);
    Families[k]`H:=H;
end for;

// We look for a relatively small list of generators of G; this is done in a rather dumb way 
// starting with generators of H.
for k in Keys(Families) do
    if Families[k]`N eq 1 then continue k; end if;
    H:=Families[k]`H;
    G:=Families[k]`G;
    N:=Families[k]`N;

    gens1:=[H.i: i in [1..Ngens(H)]];

    UN,iotaN:=UnitGroup(Integers(N));
    U:=sub<UN| [Determinant(g) @@ iotaN : g in Generators(G)]>;
    P,I:=PrimaryAbelianBasis(U);
    P:=[ iotaN(p) : p in P ];
    T:=Transversal(G,H);
    gens2:=[];
    for p in P do
        assert exists(t){t: t in T | Determinant(t) eq p};
        gens2:=gens2 cat [t];
    end for;

    B:=sub<GL(2,Integers(N))|gens1 cat gens2>;
    assert sub<UN| [Determinant(g) @@ iotaN : g in Generators(B)]> eq U;
    Families[k]`G:=B;
    
end for;


"Saving to file.";
// Write groups found to file.
I:=Open("../Data/agreeable_groups_genus_0_and_1.dat", "w");
for k in Keys(Families) do
    x:=Families[k];
    WriteObject(I, x);
end for;

"Done.";
