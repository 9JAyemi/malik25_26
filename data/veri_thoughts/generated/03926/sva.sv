module decoder_sva (
    input logic [3:0] in,
    input logic enable,
    input logic [2:0] select,
    input logic [15:0] out
);

    // Output is zero when the decoder is disabled.
    check_disable_forces_zero: assert property (
        @($global_clock) (enable == 1'b0) |-> (out == 16'h0000)
    );

    // Upper output bits are always zero.
    check_upper_bits_zero: assert property (
        @($global_clock) (out[15:8] == 8'h00)
    );

    // Select 000 drives bit 0 when enabled.
    check_select_000_decodes_bit0: assert property (
        @($global_clock) (enable == 1'b1 && select == 3'b000) |-> (out == 16'h0001)
    );

    // Select 001 drives bit 1 when enabled.
    check_select_001_decodes_bit1: assert property (
        @($global_clock) (enable == 1'b1 && select == 3'b001) |-> (out == 16'h0002)
    );

    // Select 010 drives bit 2 when enabled.
    check_select_010_decodes_bit2: assert property (
        @($global_clock) (enable == 1'b1 && select == 3'b010) |-> (out == 16'h0004)
    );

    // Select 011 drives bit 3 when enabled.
    check_select_011_decodes_bit3: assert property (
        @($global_clock) (enable == 1'b1 && select == 3'b011) |-> (out == 16'h0008)
    );

    // Select 100 drives bit 4 when enabled.
    check_select_100_decodes_bit4: assert property (
        @($global_clock) (enable == 1'b1 && select == 3'b100) |-> (out == 16'h0010)
    );

    // Select 101 drives bit 5 when enabled.
    check_select_101_decodes_bit5: assert property (
        @($global_clock) (enable == 1'b1 && select == 3'b101) |-> (out == 16'h0020)
    );

    // Select 110 drives bit 6 when enabled.
    check_select_110_decodes_bit6: assert property (
        @($global_clock) (enable == 1'b1 && select == 3'b110) |-> (out == 16'h0040)
    );

    // Select 111 drives bit 7 when enabled.
    check_select_111_decodes_bit7: assert property (
        @($global_clock) (enable == 1'b1 && select == 3'b111) |-> (out == 16'h0080)
    );

endmodule