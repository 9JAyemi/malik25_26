module xor_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic y
);

    // y must match the XOR of a and b.
    check_xor_function: assert property (
        @(posedge clk) y == (a ^ b)
    );

    // When a is low, y must follow b.
    check_a_low_passes_b: assert property (
        @(posedge clk) !a |-> (y == b)
    );

    // When a is high, y must be the inverse of b.
    check_a_high_inverts_b: assert property (
        @(posedge clk) a |-> (y == !b)
    );

    // When b is low, y must follow a.
    check_b_low_passes_a: assert property (
        @(posedge clk) !b |-> (y == a)
    );

    // When b is high, y must be the inverse of a.
    check_b_high_inverts_a: assert property (
        @(posedge clk) b |-> (y == !a)
    );

    // Equal inputs must produce a low output.
    check_equal_inputs_drive_low: assert property (
        @(posedge clk) (a == b) |-> !y
    );

    // Different inputs must produce a high output.
    check_different_inputs_drive_high: assert property (
        @(posedge clk) (a != b) |-> y
    );

endmodule