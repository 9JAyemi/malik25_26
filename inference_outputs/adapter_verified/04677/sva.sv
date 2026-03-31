module xor_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic y
);

// y must match the implemented XOR function.
    check_functional_equivalence: assert property (
        @(posedge clk) y == (a ^ b)
    );

// When a is 0, y must equal b.
    check_a_zero_pass_through: assert property (
        @(posedge clk) (a == 1'b0) |-> (y == b)
    );

// When a is 1, y must be the inverse of b.
    check_a_one_inverts_b: assert property (
        @(posedge clk) (a == 1'b1) |-> (y == ~b)
    );

// When b is 0, y must equal a.
    check_b_zero_pass_through: assert property (
        @(posedge clk) (b == 1'b0) |-> (y == a)
    );

// When b is 1, y must be the inverse of a.
    check_b_one_inverts_a: assert property (
        @(posedge clk) (b == 1'b1) |-> (y == ~a)
    );

// Equal inputs must drive y low.
    check_equal_inputs_low: assert property (
        @(posedge clk) (a == b) |-> (y == 1'b0)
    );

// Different inputs must drive y high.
    check_different_inputs_high: assert property (
        @(posedge clk) (a != b) |-> (y == 1'b1)
    );

endmodule
