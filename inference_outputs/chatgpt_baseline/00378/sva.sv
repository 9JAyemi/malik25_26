module decoder_4to16_sva (
    input logic clk,
    input logic [3:0] in,
    input logic ena,
    input logic [15:0] out
);

    // Sampling clock only; the DUT itself has no clock or reset.

    // When disabled, all outputs are HIGH.
    check_disabled_all_high: assert property (
        @(posedge clk) !ena |-> (out == 16'hFFFF)
    );

    // When enabled, the selected output bit is LOW.
    check_enabled_selected_bit_low: assert property (
        @(posedge clk) ena |-> (out[in] == 1'b0)
    );

    // When enabled, all non-selected output bits are HIGH.
    check_enabled_unselected_bits_high: assert property (
        @(posedge clk) ena |-> ((out | (16'h0001 << in)) == 16'hFFFF)
    );

    // When enabled, the full active-low decode matches the input value.
    check_enabled_decode_map: assert property (
        @(posedge clk) ena |-> (out == ~(16'h0001 << in))
    );

endmodule