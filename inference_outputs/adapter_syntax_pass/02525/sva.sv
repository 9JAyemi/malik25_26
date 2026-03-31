module digital_circuit_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // Y matches the implemented NOT/AND/NOR/BUF function.
    check_y_function: assert property (
        @(posedge clk) Y == ~((~B1_N) | (A1 & A2))
    );

    // A low B1_N input forces Y high.
    check_b1n_low_forces_y_high: assert property (
        @(posedge clk) (B1_N == 1'b0) |-> (Y == 1'b1)
    );

    // A high A1 and A2 input force Y low.
    check_a1_a2_high_force_y_low: assert property (
        @(posedge clk) ((A1 == 1'b1) && (A2 == 1'b1)) |-> (Y == 1'b0)
    );

    // With B1_N high and A1 low, Y must be high.
    check_b1n_high_a1_low_y_high: assert property (
        @(posedge clk) ((B1_N == 1'b1) && (A1 == 1'b0)) |-> (Y == 1'b1)
    );

    // With B1_N high and A2 low, Y must be high.
    check_b1n_high_a2_low_y_high: assert property (
        @(posedge clk) ((B1_N == 1'b1) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // A low Y can only occur when B1_N is high and A1/A2 are both high.
    check_y_low_only_when_inputs_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((B1_N == 1'b1) && (A1 == 1'b1) && (A2 == 1'b1))
    );

endmodule