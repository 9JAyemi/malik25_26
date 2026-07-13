module my_and3_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X implements A & B & C.
    check_x_matches_and3: assert property (
        @(posedge clk) X == (A & B & C)
    );

    // A low forces X low.
    check_a_low_forces_x_low: assert property (
        @(posedge clk) !A |-> !X
    );

    // B low forces X low.
    check_b_low_forces_x_low: assert property (
        @(posedge clk) !B |-> !X
    );

    // C low forces X low.
    check_c_low_forces_x_low: assert property (
        @(posedge clk) !C |-> !X
    );

    // All three inputs high drive X high.
    check_all_inputs_high_drive_x_high: assert property (
        @(posedge clk) (A & B & C) |-> X
    );

    // X high requires all three inputs high.
    check_x_high_requires_all_inputs_high: assert property (
        @(posedge clk) X |-> (A & B & C)
    );

    // With B and C high, X follows A.
    check_x_follows_a_when_bc_high: assert property (
        @(posedge clk) (B & C) |-> (X == A)
    );

    // With A and C high, X follows B.
    check_x_follows_b_when_ac_high: assert property (
        @(posedge clk) (A & C) |-> (X == B)
    );

    // With A and B high, X follows C.
    check_x_follows_c_when_ab_high: assert property (
        @(posedge clk) (A & B) |-> (X == C)
    );

endmodule