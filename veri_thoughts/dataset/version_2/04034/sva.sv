module complement_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] C
);

    // RTL is combinational with no reset; assertions are sampled on clk.

    // C must equal the implemented two's complement of A.
    check_twos_complement_definition: assert property (
        @(posedge clk) C == (~A + 4'b0001)
    );

    // A and C must sum to zero modulo 16.
    check_additive_inverse_wrap: assert property (
        @(posedge clk) (A + C) == 4'h0
    );

    // Zero input must produce zero output.
    check_zero_maps_to_zero: assert property (
        @(posedge clk) (A == 4'h0) |-> (C == 4'h0)
    );

    // Input 1 must produce 4'hF.
    check_one_maps_to_all_ones: assert property (
        @(posedge clk) (A == 4'h1) |-> (C == 4'hF)
    );

    // Input 4'h8 is its own 4-bit two's complement.
    check_min_value_is_self_inverse: assert property (
        @(posedge clk) (A == 4'h8) |-> (C == 4'h8)
    );

    // Input 4'hF must produce 4'h1.
    check_all_ones_maps_to_one: assert property (
        @(posedge clk) (A == 4'hF) |-> (C == 4'h1)
    );

    // Two's complement preserves the least-significant bit.
    check_lsb_preserved: assert property (
        @(posedge clk) C[0] == A[0]
    );

endmodule