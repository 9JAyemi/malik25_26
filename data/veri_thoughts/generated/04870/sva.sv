module logical_and_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

    // Y must equal the three-input AND of A, B, and C.
    check_y_matches_three_input_and: assert property (
        @(posedge clk) disable iff (1'b0)
        Y == (A & B & C)
    );

    // Y high requires all three inputs high.
    check_y_high_implies_all_inputs_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (Y == 1'b1) |-> ((A == 1'b1) && (B == 1'b1) && (C == 1'b1))
    );

    // All three inputs high must drive Y high.
    check_all_inputs_high_implies_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
        ((A == 1'b1) && (B == 1'b1) && (C == 1'b1)) |-> (Y == 1'b1)
    );

    // Any low input must drive Y low.
    check_any_low_input_implies_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        ((A == 1'b0) || (B == 1'b0) || (C == 1'b0)) |-> (Y == 1'b0)
    );

    // Y low means at least one input is low.
    check_y_low_implies_at_least_one_input_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (Y == 1'b0) |-> ((A == 1'b0) || (B == 1'b0) || (C == 1'b0))
    );

endmodule