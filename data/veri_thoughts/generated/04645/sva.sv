module top_module_assertions (
    input logic [1:0] a,
    input logic [49:0] in,
    input logic [5:0] out
);

    (* gclk *) logic clk;

    // out[1:0] are tied low.
    check_out_low_bits_zero: assert property (
        @(posedge clk) out[1:0] == 2'b00
    );

    // out[5] matches the XOR of a[0] and a[1].
    check_out_xor_bit: assert property (
        @(posedge clk) out[5] == (a[0] ^ a[1])
    );

    // out[4] matches the inverted AND-reduction of in.
    check_out_inverted_and_bit: assert property (
        @(posedge clk) out[4] == ~(&in)
    );

    // out[3] matches the inverted OR-reduction of in.
    check_out_inverted_or_bit: assert property (
        @(posedge clk) out[3] == ~(|in)
    );

    // out[2] matches the inverted XOR-reduction of in.
    check_out_inverted_xor_bit: assert property (
        @(posedge clk) out[2] == ~(^in)
    );

    // out matches the complete concatenated expression.
    check_out_full_mapping: assert property (
        @(posedge clk) out == {(a[0] ^ a[1]), ~(&in), ~(|in), ~(^in), 2'b00}
    );

endmodule