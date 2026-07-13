module reverse_bit_order_sva (
    input logic [99:0] in,
    input logic        clk,
    input logic [99:0] out
);

    // The output vector updates as a shift register driven only by the previous in[0].
    check_output_vector_update: assert property (
        @(posedge clk) 1'b1 |=> out == { $past(in[0]), $past(out[99:1]) }
    );

    // The output MSB captures the previous cycle value of in[0].
    check_output_msb_from_input0: assert property (
        @(posedge clk) 1'b1 |=> out[99] == $past(in[0])
    );

    // The lower 99 output bits shift from the previous cycle's higher output bits.
    check_output_lower_bits_shift: assert property (
        @(posedge clk) 1'b1 |=> out[98:0] == $past(out[99:1])
    );

endmodule