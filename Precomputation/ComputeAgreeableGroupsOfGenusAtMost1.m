/*
    We compute all the agreeable subgroups of GL(2,Zhat) of genus at most 1, up to conjugacy, and save them to a file.

*/
//  nohup magma -t 32 "ComputeAgreeableGroupsOfGenusAtMost1.m" &

load "Preamble.m";

"Computing commutator subgroups of congruence subgroups of genus 0 and 1.";

/*  We consider the open subgroups H of SL(2,Zhat), up to conjugacy in GL(2,Zhat), that contain -I and have 
    genus 0 or 1.  
    
    We compute a surjective homomorphism phi: H ->Q, with Q a finite group, so that the kernel of phi is the 
    commutator subgroup [H,H].   
   
    We save this data to the array "comm_map". We record the level of [H,H] in the array "comm_level".
*/

comm_map:=AssociativeArray();
comm_level:=AssociativeArray();  

for Gamma in cp_data do  // run over Cummins-Pauli data
    if Gamma`genus gt 1 then continue Gamma; end if;

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


"Computing agreeable subgroups of GL(2,Zhat) of genus at most 1.";

Families:=AssociativeArray();

/* We will compute finitely many open subgroups G of GL(2,Zhat) that, up to conjugacy, 
   include those that satisfy the following:
    - G is agreeable,
    - X_G has genus at most 1.
*/

for r in cp_data do
    if r`genus gt 1 then continue r; end if;

    label:=1; 
    r`name;
    
    // We vary over all the congruence subgroups of SL(2,Z) that contain -I, up to conjugacy in GL(2,Z), with genus 0 or 1;
    // it gives rise to an open subgroup H of SL(2,Zhat) containing -I.

    level:=r`level;
    matgens:=r`matgens;

    SL2:=SL2Ambient(level);   //SL(2,Integers(level));
    if level ne 1 then
        H:=sub<SL2|matgens>; 
    else
        H:=SL2;
    end if;
    H`SL:=true;
    assert SL2ContainsNegativeOne(H);

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
    S0:=SL2Intersection(N); 
    S1:=iota(S0);
    MM:=[M`subgroup: M in Subgroups(Q)];
    MM:=[M: M in MM | #(M meet S1) eq 1];
    //assert true notin { IsConjugate(Q,MM[i],MM[j]) : i,j in [1..#MM] | i lt j };
  
    for M_ in MM do
        G:=M_ @@ iota;
        
        H`Genus:=r`genus;
        G`Genus:=r`genus;

        X:=InitializeModularCurve(G,H);

        X`CPname:=r`name;


        if X`N eq 1 then 
            X`Hc:=CommutatorSubgroup(GL(2,Integers(2)));
            (X`Hc)`SL:=true;
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



"Performing computations to decrease the number of generators of our groups.";

// makes sure some attributes of our groups have been computed (can speed up calculations)
for k in Keys(Families) do
    
    G:=Families[k]`G;    
    H:=Families[k]`H;
    N:=Families[k]`N;

    H`SL:=true;
    if assigned G`SL then
        delete G`SL;
        H:=sub<SL2Ambient(N)|Generators(H)>;
        H`SL:=true;
        assert not assigned G`SL;
    end if;

    if not assigned G`Level then G`Level:=Families[k]`level; end if;
    if not assigned H`Level then H`Level:=Families[k]`sl2level; end if;
    if not assigned G`Index then G`Index:=Families[k]`index; end if;
    if not assigned H`Index then H`Index:=Families[k]`degree; end if; // assumes -I in H

    if not assigned G`Order then G`Order:=GL2Size(N) div G`Index; end if;
    if not assigned H`Order then H`Order:=SL2Size(N) div H`Index; end if;

    Families[k]`G:=G;
    Families[k]`H:=H;
end for;

// We look for a relatively small list of generators of H; this is done in a rather dumb way 
for k in Keys(Families) do
    N:=Families[k]`N;
    H:=Families[k]`H;
    H`SL:=true;
    level:=Families[k]`sl2level;

    H1:=SL2Project(H,level);
    SL2:=SL2Ambient(level);
    gens1:={};
    B:=sub<SL2 | gens1>; B`SL:=true;
    while B ne H1 do
        T:=[t: t in Transversal(H1,B) | t notin B];
        m:=Maximum({#sub<SL2 | gens1 join {h}> : h in T});
        assert exists(a){h: h in T | #sub<SL2 | gens1 join {h}> eq m };
        gens1:=gens1 join {a};
        B:=sub<SL2 | gens1>; B`SL:=true;
    end while;
    H1:=SL2Lift(B,N); 
    H1`Level:=Families[k]`sl2level;
    H1`Index:=Families[k]`degree; // assumes -I in H
    H1`Order:=SL2Size(N) div H1`Index;

    assert H eq H1;
   
    Families[k]`H:=H1;
end for;


// We look for a relatively small list of generators of Hc; this is done in a rather dumb way 
for k in Keys(Families) do
    Hc:=Families[k]`Hc;
    Hc`SL:=true;
    level:=#BaseRing(Hc); // should be level of Hc

    H1:=SL2Project(Hc,level);
    SL2:=SL2Ambient(level);
    gens1:={};
    B:=sub<SL2 | gens1>; B`SL:=true;
    while B ne H1 do
        T:=[t: t in Transversal(H1,B) | t notin B];
        m:=Maximum({#sub<SL2 | gens1 join {h}> : h in T});
        assert exists(a){h: h in T | #sub<SL2 | gens1 join {h}> eq m };
        gens1:=gens1 join {a};
        B:=sub<SL2 | gens1>; B`SL:=true;
    end while;
    H1:=SL2Lift(B,level); 
    H1`Level:=level;
    H1`Index:=Families[k]`commutator_index;
    H1`Order:=SL2Size(level) div H1`Index;

    assert Hc eq H1;

    Families[k]`Hc:=H1;
end for;


// We look for a relatively small list of generators of G (with generators of H =(G meet SL2) given first) 
for k in Keys(Families) do

    G:=Families[k]`G;
    H:=Families[k]`H;
    N:=Families[k]`N;
    if N eq 1 then continue k; end if; 
    
    U,iota:=UnitGroup(BaseRing(G));
    phi:=hom<G->U | [(Determinant(G.i)) @@ iota: i in [1..Ngens(G)]]>;
    gens:=[H.i: i in [1..Ngens(H)]] cat [(U!a) @@ phi : a in Generators(Image(phi))];

    Gnew:=sub<GL2Ambient(N)|gens>;
    Gnew`Order:=G`Order;
    Gnew`Index:=G`Index;
    Gnew`Level:=G`Level;
    assert G eq Gnew;
    
    Families[k]`G:=Gnew;
end for;


"Saving to file.";
// Write groups found to file.
I:=Open("../Data/agreeable_groups_genus_0_and_1.dat", "w");
for k in Keys(Families) do
    x:=Families[k];
    WriteObject(I, x);
end for;
