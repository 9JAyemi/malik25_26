module signal_process_sva (
    input logic       clk,
    input logic [7:0] input_signal,
    input logic [7:0] output_signal
);

    // Output matches the implemented bit transformation.
    check_full_output_transform: assert property (
        @(posedge clk)
        output_signal == {~input_signal[3:0], input_signal[5:4], 2'b00}
    );

    // Upper output nibble is the inverse of the lower input nibble.
    check_upper_nibble_inversion: assert property (
        @(posedge clk)
        output_signal[7:4] == ~input_signal[3:0]
    );

    // Lower output nibble is the shifted upper input nibble.
    check_lower_nibble_shift: assert property (
        @(posedge clk)
        output_signal[3:0] == {input_signal[5:4], 2'b00}
    );

    // Output bits [3:2] map directly from input bits [5:4].
    check_shifted_bit_mapping: assert property (
        @(posedge clk)
        output_signal[3:2] == input_signal[5:4]
    );

    // Output bits [1:0] are always zero.
    check_low_bits_zero: assert property (
        @(posedge clk)
        output_signal[1:0] == 2'b00
    );

endmodule