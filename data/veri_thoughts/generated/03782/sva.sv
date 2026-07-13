module and_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Y
);

    // Y must always equal A AND B.
    check_output_matches_and: assert property (
        @(posedge clk) Y == (A & B)
    );

    // A LOW must force Y LOW.
    check_a_low_forces_y_low: assert property (
        @(posedge clk) (A == 1'b0) |-> (Y == 1'b0)
    );

    // B LOW must force Y LOW.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) (B == 1'b0) |-> (Y == 1'b0)
    );

    // Both inputs HIGH must drive Y HIGH.
    check_both_high_drive_y_high: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b1) |-> (Y == 1'b1)
    );

    // Y HIGH requires both inputs HIGH.
    check_y_high_requires_both_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> (A == 1'b1 && B == 1'b1)
    );

endmodule