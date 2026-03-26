module and_gate (
    A,
    B,
    C,
    D,
    Y
);

    // Module ports
    input  A, B, C, D;
    output Y;

    // Local signals
    wire  not_A, not_B, not_C, not_D;
    wire  and1_out, and2_out, and3_out;

    //  Name  Output      Other arguments
    not not_A_gate (not_A, A);
    not not_B_gate (not_B, B);
    not not_C_gate (not_C, C);
    not not_D_gate (not_D, D);

    and and1_gate (and1_out, not_A, not_B);
    and and2_gate (and2_out, not_C, not_D);
    and and3_gate (Y, and1_out, and2_out);

endmodule