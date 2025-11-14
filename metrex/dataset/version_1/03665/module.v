module my_module (
    X ,
    A1,
    A2,
    A3,
    B1
);

    output X ;
    input  A1;
    input  A2;
    input  A3;
    input  B1;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;

    wire a_and;
    wire b_not;

    // AND gate to check if A1, A2, and A3 are all high
    and gate_a(a_and, A1, A2, A3);

    // NOT gate to invert B1 signal
    not gate_b(b_not, B1);

    // AND gate to combine a_and and b_not signals
    and gate_x(X, a_and, b_not);

endmodule