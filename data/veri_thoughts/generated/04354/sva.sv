module twos_comp_sva (
    input logic clk,
    input logic [3:0] X,
    input logic [3:0] A
);

    // Sampling clock only; the RTL itself has no clock or reset.

    // X must equal bitwise inversion of A plus 1.
    check_twos_comp_definition: assert property (
        @(posedge clk) X == ((~A) + 4'b0001)
    );

    // Taking two's complement of X must recover A.
    check_reverse_twos_comp_definition: assert property (
        @(posedge clk) A == ((~X) + 4'b0001)
    );

    // A and X must sum to zero modulo 16.
    check_additive_inverse: assert property (
        @(posedge clk) (A + X) == 4'b0000
    );

    // Zero must map to zero.
    check_zero_maps_to_zero: assert property (
        @(posedge clk) (A == 4'b0000) |-> (X == 4'b0000)
    );

    // 4'b1000 must map to itself.
    check_min_negative_self_inverse: assert property (
        @(posedge clk) (A == 4'b1000) |-> (X == 4'b1000)
    );

    // Only 0 and 8 may equal their own two's complement.
    check_only_self_inverse_values: assert property (
        @(posedge clk) (A == X) |-> ((A == 4'b0000) || (A == 4'b1000))
    );

endmodule