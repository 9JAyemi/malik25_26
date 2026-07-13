module xor3_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic y
);

    // No RTL clock or reset; clk is an external sampling clock.

    // Output matches the 3-input XOR of a, b, and c.
    check_xor3_function: assert property (
        @(posedge clk) y == (a ^ b ^ c)
    );

    // When a and b are equal, y follows c.
    check_output_equals_c_when_a_b_equal: assert property (
        @(posedge clk) (a == b) |-> (y == c)
    );

    // When a and b differ, y inverts c.
    check_output_inverts_c_when_a_b_differ: assert property (
        @(posedge clk) (a != b) |-> (y == ~c)
    );

    // When a and c are equal, y follows b.
    check_output_equals_b_when_a_c_equal: assert property (
        @(posedge clk) (a == c) |-> (y == b)
    );

    // When a and c differ, y inverts b.
    check_output_inverts_b_when_a_c_differ: assert property (
        @(posedge clk) (a != c) |-> (y == ~b)
    );

    // When b and c are equal, y follows a.
    check_output_equals_a_when_b_c_equal: assert property (
        @(posedge clk) (b == c) |-> (y == a)
    );

    // When b and c differ, y inverts a.
    check_output_inverts_a_when_b_c_differ: assert property (
        @(posedge clk) (b != c) |-> (y == ~a)
    );

endmodule