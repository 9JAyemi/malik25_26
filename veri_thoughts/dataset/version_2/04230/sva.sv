module byte_to_bit_converter_sva (
    input logic [7:0] byte_in,
    input logic       strobe,
    input logic       clk,
    input logic [7:0] bit_out
);

    // When strobe is high, the output byte captures the input byte.
    check_byte_capture_on_strobe: assert property (
        @(posedge clk) (strobe === 1'b1) |=> (bit_out === $past(byte_in))
    );

    // When strobe is not high, the output byte holds its previous value.
    check_byte_hold_without_strobe: assert property (
        @(posedge clk) (strobe !== 1'b1) |=> (bit_out === $past(bit_out))
    );

endmodule