module mux4to1 (
    input A, B, C, D,
    input S0, S1,
    output Y
);

    wire notS0, notS1, and1, and2, and3, and4;

    not (notS0, S0);
    not (notS1, S1);
    and (and1, A, notS1, notS0);
    and (and2, B, notS1, S0);
    and (and3, C, S1, notS0);
    and (and4, D, S1, S0);
    or (Y, and1, and2, and3, and4);

endmodule