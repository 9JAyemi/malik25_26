module sky130_fd_sc_lp__o31ai_sva (
    input logic clk,   // sampling clock from environment
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);
    // Pure combinational cell: Y = ~(B1 & (A1 | A2 | A3)). No reset in RTL.

    // Y equals NAND of B1 and OR(A1,A2,A3).
    check_function_equivalence: assert property (
        @(posedge clk) disable iff (1'b0)
            Y == !(B1 & (A1 | A2 | A3))
    );

    // If B1 is LOW, Y must be HIGH.
    b1_low_forces_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
            (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // If all A inputs are LOW, Y must be HIGH.
    no_a_high_forces_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
            ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0)) |-> (Y == 1'b1)
    );

    // If B1 is HIGH and any A is HIGH, Y must be LOW.
    b1_and_any_a_high_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
            (B1 && (A1 || A2 || A3)) |-> (Y == 1'b0)
    );

    // If B1 and A1 are HIGH, Y must be LOW.
    b1_and_a1_force_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
            (B1 && A1) |-> (Y == 1'b0)
    );

    // If B1 and A2 are HIGH, Y must be LOW.
    b1_and_a2_force_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
            (B1 && A2) |-> (Y == 1'b0)
    );

    // If B1 and A3 are HIGH, Y must be LOW.
    b1_and_a3_force_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
            (B1 && A3) |-> (Y == 1'b0)
    );

    // Y LOW implies B1 is HIGH and at least one A is HIGH.
    y_low_implies_b1_and_any_a_high: assert property (
        @(posedge clk) disable iff (1'b0)
            (Y == 1'b0) |-> (B1 && (A1 || A2 || A3))
    );

    // If all inputs are HIGH, Y must be LOW.
    all_ones_force_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
            (A1 && A2 && A3 && B1) |-> (Y == 1'b0)
    );

    // If all inputs are LOW, Y must be HIGH.
    all_zeros_force_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
            (!A1 && !A2 && !A3 && !B1) |-> (Y == 1'b1)
    );

endmodule