module xor_module_sva #(
    parameter [3:0] c = 4'b1011
) (
    input logic       clk,
    input logic [3:0] a,
    input logic [3:0] b
);

    // b must equal a XOR c on every sampled cycle.
    check_xor_function: assert property (
        @(posedge clk) b == (a ^ c)
    );

    // Bit 0 of b must be the inverse of bit 0 of a.
    check_b0_inverts_a0: assert property (
        @(posedge clk) b[0] == ~a[0]
    );

    // Bit 1 of b must match bit 1 of a.
    check_b1_matches_a1: assert property (
        @(posedge clk) b[1] == a[1]
    );

    // Bit 2 of b must be the inverse of bit 2 of a.
    check_b2_inverts_a2: assert property (
        @(posedge clk) b[2] == ~a[2]
    );

    // Bit 3 of b must be the inverse of bit 3 of a.
    check_b3_inverts_a3: assert property (
        @(posedge clk) b[3] == ~a[3]
    );

    // XOR with the same constant must recover the original input.
    check_inverse_mapping: assert property (
        @(posedge clk) a == (b ^ c)
    );

endmodule