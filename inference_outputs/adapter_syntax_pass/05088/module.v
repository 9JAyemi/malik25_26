
module binary_adder (
    COUT,
    SUM,
    A,
    B,
    CIN,
    VDD,
    VSS
);

    // Module ports
    output COUT;
    output SUM;
    input  A;
    input  B;
    input  CIN;
    input  VDD;
    input  VSS;

    // Local signals
    wire ci;
    wire xor0_out_SUM;
    wire a_b;
    wire a_ci;
    wire b_ci;
    wire or0_out_COUT;

    // Instantiate the cells
    not (ci, CIN);
    xor (xor0_out_SUM, A, B, ci);
    and (a_b, A, B);
    and (a_ci, A, ci);
    and (b_ci, B, ci);
    or (or0_out_COUT, a_b, a_ci, b_ci);
    buf (SUM, xor0_out_SUM);
    buf (COUT, or0_out_COUT);

endmodule
