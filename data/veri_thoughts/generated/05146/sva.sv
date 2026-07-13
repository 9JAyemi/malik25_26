module nor_gate_sva(
    input logic clk,
    input logic A,
    input logic B,
    input logic Y
);

    // Output matches the implemented AND function.
    check_output_matches_and_function: assert property (
        @(posedge clk) Y == (A & B)
    );

    // Both inputs low drive the output low.
    check_inputs_00_drive_low: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b0)) |-> (Y == 1'b0)
    );

    // A low and B high drive the output low.
    check_inputs_01_drive_low: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b1)) |-> (Y == 1'b0)
    );

    // A high and B low drive the output low.
    check_inputs_10_drive_low: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b0)) |-> (Y == 1'b0)
    );

    // Both inputs high drive the output high.
    check_inputs_11_drive_high: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b1)) |-> (Y == 1'b1)
    );

    // A high output requires both inputs high.
    check_output_high_requires_both_inputs_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((A == 1'b1) && (B == 1'b1))
    );

endmodule