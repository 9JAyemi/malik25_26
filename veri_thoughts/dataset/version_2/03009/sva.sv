module nand4_assertions (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y implements the 4-input AND of A, B, C, and D.
    check_output_matches_and: assert property (
        @(posedge clk) Y == (A && B && C && D)
    );

    // All four inputs high drives Y high.
    check_all_high_implies_y_high: assert property (
        @(posedge clk) (A && B && C && D) |-> Y
    );

    // Y can be high only when all four inputs are high.
    check_y_high_requires_all_high: assert property (
        @(posedge clk) Y |-> (A && B && C && D)
    );

    // Any low input forces Y low.
    check_any_low_implies_y_low: assert property (
        @(posedge clk) (!A || !B || !C || !D) |-> !Y
    );

    // A rising Y edge requires all four inputs to be high.
    check_y_rise_requires_all_high: assert property (
        @(posedge clk) $rose(Y) |-> (A && B && C && D)
    );

    // A falling Y edge requires at least one input to be low.
    check_y_fall_requires_low_input: assert property (
        @(posedge clk) $fell(Y) |-> (!A || !B || !C || !D)
    );

endmodule