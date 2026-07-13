module and_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Y
);

    // Y matches the AND of A and B.
    check_and_function: assert property (
        @(posedge clk) Y == (A & B)
    );

    // Both high inputs drive Y high.
    check_both_inputs_high_drive_output_high: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b1)) |-> (Y == 1'b1)
    );

    // A low drives Y low.
    check_a_low_drives_output_low: assert property (
        @(posedge clk) (A == 1'b0) |-> (Y == 1'b0)
    );

    // B low drives Y low.
    check_b_low_drives_output_low: assert property (
        @(posedge clk) (B == 1'b0) |-> (Y == 1'b0)
    );

    // A high output requires both inputs high.
    check_output_high_requires_both_inputs_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((A == 1'b1) && (B == 1'b1))
    );

endmodule