module xor_32_refactored_sva (
    input  logic        clk,    // external sampling clock
    input  logic        rst_n,  // external active-low reset for disabling assertions
    input  logic [31:0] a,
    input  logic [31:0] b,
    input  logic [31:0] out
);
    // Output equals bitwise XOR of a and b.
    check_xor_definition: assert property (
        @(posedge clk) disable iff (!rst_n) out == (a ^ b)
    );

    // If a is zero, output passes through b.
    check_a_zero_passthrough: assert property (
        @(posedge clk) disable iff (!rst_n) (a == 32'h0) |-> (out == b)
    );

    // If b is zero, output passes through a.
    check_b_zero_passthrough: assert property (
        @(posedge clk) disable iff (!rst_n) (b == 32'h0) |-> (out == a)
    );

    // If inputs are equal, output is zero.
    check_equal_inputs_zero_out: assert property (
        @(posedge clk) disable iff (!rst_n) (a == b) |-> (out == 32'h0)
    );

    // If output is zero, inputs are equal.
    check_zero_out_implies_equal_inputs: assert property (
        @(posedge clk) disable iff (!rst_n) (out == 32'h0) |-> (a == b)
    );

    // Self-inverse: (a ^ b) ^ b == a.
    check_self_inverse_via_b: assert property (
        @(posedge clk) disable iff (!rst_n) ((out ^ b) == a)
    );

    // Self-inverse: (a ^ b) ^ a == b.
    check_self_inverse_via_a: assert property (
        @(posedge clk) disable iff (!rst_n) ((out ^ a) == b)
    );
endmodule