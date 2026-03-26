module decoder_3to8_assertions (
    input logic [2:0] input_bits,
    input logic [7:0] output_bits
);

    // No explicit RTL clock or reset; sample combinational behavior on $global_clock.

    // Output bit 0 is high only for input 000.
    check_decode_bit0: assert property (
        @($global_clock) output_bits[0] == (input_bits == 3'b000)
    );

    // Output bit 1 is high only for input 001.
    check_decode_bit1: assert property (
        @($global_clock) output_bits[1] == (input_bits == 3'b001)
    );

    // Output bit 2 is high only for input 010.
    check_decode_bit2: assert property (
        @($global_clock) output_bits[2] == (input_bits == 3'b010)
    );

    // Output bit 3 is high only for input 011.
    check_decode_bit3: assert property (
        @($global_clock) output_bits[3] == (input_bits == 3'b011)
    );

    // Output bit 4 is high only for input 100.
    check_decode_bit4: assert property (
        @($global_clock) output_bits[4] == (input_bits == 3'b100)
    );

    // Output bit 5 is high only for input 101.
    check_decode_bit5: assert property (
        @($global_clock) output_bits[5] == (input_bits == 3'b101)
    );

    // Output bit 6 is high only for input 110.
    check_decode_bit6: assert property (
        @($global_clock) output_bits[6] == (input_bits == 3'b110)
    );

    // Output bit 7 is high only for input 111.
    check_decode_bit7: assert property (
        @($global_clock) output_bits[7] == (input_bits == 3'b111)
    );

    // The output bit selected by input_bits must be high.
    check_selected_output_bit_high: assert property (
        @($global_clock) output_bits[input_bits] == 1'b1
    );

    // All non-selected output bits must be low.
    check_unselected_output_bits_low: assert property (
        @($global_clock) (output_bits & ~(8'b00000001 << input_bits)) == 8'b00000000
    );

endmodule