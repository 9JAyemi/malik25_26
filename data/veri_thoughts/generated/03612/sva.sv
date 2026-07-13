module special_and_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic X
);

    // A high forces the selected AND result to zero.
    check_a_high_forces_zero: assert property (
        @(posedge clk)
        (A === 1'b1) |-> (X === 1'b0)
    );

    // With A low and B known, the output is the inverse of B.
    check_a_low_inverts_b: assert property (
        @(posedge clk)
        (A === 1'b0 && !$isunknown(B)) |-> (X === ~B)
    );

    // For known inputs, the implemented function is a NOR.
    check_known_inputs_match_nor: assert property (
        @(posedge clk)
        (!$isunknown({A, B})) |-> (X === ~(A | B))
    );

    // Known inputs must produce a known output.
    check_known_inputs_drive_known_output: assert property (
        @(posedge clk)
        (!$isunknown({A, B})) |-> (!$isunknown(X))
    );

    // A high output is only possible when both inputs are low.
    check_output_high_only_for_both_low: assert property (
        @(posedge clk)
        (X === 1'b1) |-> (A === 1'b0 && B === 1'b0)
    );

endmodule