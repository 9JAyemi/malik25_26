module MUX4_2to1 (A, B, C, D, S1, S0, Z);
input A, B, C, D;
input S1, S0;
output Z;

wire X0, X1, X2;

// First 2-to-1 MUX
mux2to1 M1 (X0, A, B, S0);

// Second 2-to-1 MUX
mux2to1 M2 (X1, C, D, S0);

// Final 2-to-1 MUX
mux2to1 M3 (Z, X0, X1, S1);

endmodule

module mux2to1 (Z, A, B, S);
input A, B, S;
output Z;

wire notS, and1, and2;

not (notS, S);
and (and1, A, notS);
and (and2, B, S);
or (Z, and1, and2);

endmodule