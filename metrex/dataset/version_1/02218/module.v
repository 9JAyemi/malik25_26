
module mux4 (
    input A, B, C, D,
    input S0, S1,
    output X
);

    wire not_S0, not_S1, and0, and1, and2, and3, or0, or1;

    not (not_S0, S0);
    not (not_S1, S1);

    and (and0, A, not_S0, not_S1);
    and (and1, B, not_S0, S1);
    and (and2, C, S0, not_S1);
    and (and3, D, S0, S1);

    or (or0, and0, and1);
    or (or1, and2, and3);

    or (X, or0, or1);

endmodule