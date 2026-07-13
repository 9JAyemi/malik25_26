module majority_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);

    wire AB, AC, AD, BC, BD, CD;
    wire ABC, ABD, ACD, BCD;
    wire AB_CD, AC_BD, AD_BC;

    assign AB = A & B;
    assign AC = A & C;
    assign AD = A & D;
    assign BC = B & C;
    assign BD = B & D;
    assign CD = C & D;

    assign ABC = AB & C;
    assign ABD = AB & D;
    assign ACD = AC & D;
    assign BCD = BC & D;

    assign AB_CD = ABC | ABD | CD;
    assign AC_BD = ABC | ACD | BD;
    assign AD_BC = ABD | ACD | BC;

    // X must match the RTL's final structural expression.
    check_x_matches_structural_expression: assert property (
        @(posedge clk) X == (AB_CD & AC_BD & AD_BC)
    );

    // X must be high iff at least one 3-input product term is high.
    check_x_matches_three_high_function: assert property (
        @(posedge clk) X == (ABC | ABD | ACD | BCD)
    );

    // A, B, and C high must drive X high.
    check_abc_implies_x: assert property (
        @(posedge clk) ABC |-> X
    );

    // A, B, and D high must drive X high.
    check_abd_implies_x: assert property (
        @(posedge clk) ABD |-> X
    );

    // A, C, and D high must drive X high.
    check_acd_implies_x: assert property (
        @(posedge clk) ACD |-> X
    );

    // B, C, and D high must drive X high.
    check_bcd_implies_x: assert property (
        @(posedge clk) BCD |-> X
    );

    // Without any 3-input product term, X must be low.
    check_no_three_high_inputs_means_x_low: assert property (
        @(posedge clk) !(ABC | ABD | ACD | BCD) |-> !X
    );

endmodule