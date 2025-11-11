module mux4 (
    x,
    a0,
    a1,
    a2,
    a3,
    s0,
    s1
);

    output x;
    input a0;
    input a1;
    input a2;
    input a3;
    input s0;
    input s1;

    wire not_s0, not_s1;
    wire and1, and2, and3, and4;
    wire or1, or2;

    // Invert select signals
    not not_s0 (not_s0, s0);
    not not_s1 (not_s1, s1);

    // AND gates for each input and select signal combination
    and and1 (and1, a0, not_s1, not_s0);
    and and2 (and2, a1, not_s1, s0);
    and and3 (and3, a2, s1, not_s0);
    and and4 (and4, a3, s1, s0);

    // OR gates for the output
    or or1 (or1, and1, and2);
    or or2 (or2, and3, and4);
    or or3 (x, or1, or2);

endmodule