This folder contains data from Cummins and Pauli (https://mathstats.uncg.edu/sites/pauli/congruence/) whose classify low genus congruence subgroups.

Our data is obtained from theirs by running the following code in Magma:
    load "pre.m";
    load "csg.m";
    load "csg1-lev48.dat";
    filename:="CPdata.dat";
    I:=Open(filename,"w");
    WriteObject(I, L);