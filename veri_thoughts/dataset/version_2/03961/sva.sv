module decoder_assertions (
    input logic EN,
    input logic SEL,
    input logic [3:0] Y
);

    // Disabled decoder drives all outputs low.
    check_disabled_drives_zero: assert property (
        @($global_clock) (!EN) |-> (Y == 4'b0000)
    );

    // Enabled decoder with SEL low drives bit 0.
    check_sel0_decodes_to_bit0: assert property (
        @($global_clock) (EN && !SEL) |-> (Y == 4'b0001)
    );

    // Enabled decoder with SEL high drives bit 1.
    check_sel1_decodes_to_bit1: assert property (
        @($global_clock) (EN && SEL) |-> (Y == 4'b0010)
    );

    // Upper output bits are never asserted.
    check_upper_bits_always_zero: assert property (
        @($global_clock) (Y[3:2] == 2'b00)
    );

    // When enabled, exactly one low output bit is asserted.
    check_enabled_onehot_low_bits: assert property (
        @($global_clock) EN |-> ((Y[1:0] == 2'b01) || (Y[1:0] == 2'b10))
    );

    // Output only takes implemented decode values.
    check_output_legal_values_only: assert property (
        @($global_clock) ((Y == 4'b0000) || (Y == 4'b0001) || (Y == 4'b0010))
    );

endmodule