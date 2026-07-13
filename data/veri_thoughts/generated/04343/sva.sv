module twos_complement_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [3:0] out
);

    // RTL has no native clock or reset; clk is an external sampling clock.
    // The design is purely combinational: out is the 4-bit two's complement of in.

    // Output must equal bitwise inversion plus one.
    check_twos_complement_relation: assert property (
        @(posedge clk) out == ((~in) + 4'b0001)
    );

    // Input and output must sum to zero modulo 4 bits.
    check_additive_inverse: assert property (
        @(posedge clk) (in + out) == 4'b0000
    );

    // Zero must map to zero.
    check_zero_maps_to_zero: assert property (
        @(posedge clk) (in == 4'b0000) |-> (out == 4'b0000)
    );

    // The most negative 4-bit value must map to itself.
    check_most_negative_maps_to_self: assert property (
        @(posedge clk) (in == 4'b1000) |-> (out == 4'b1000)
    );

endmodule