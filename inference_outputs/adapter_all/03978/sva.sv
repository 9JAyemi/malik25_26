module decoder_2to4_with_enable_sva (
    input logic A,
    input logic B,
    input logic EN,
    input logic [3:0] Y
);

    // When disabled, the output is forced low.
    check_disabled_forces_zero: assert property (
        @($global_clock) (!EN) |-> (Y == 4'b0000)
    );

    // When enabled and A=0, B=0, the output selects bit 0.
    check_decode_00: assert property (
        @($global_clock) (EN && !A && !B) |-> (Y == 4'b0001)
    );

    // When enabled and A=0, B=1, the output selects bit 1.
    check_decode_01: assert property (
        @($global_clock) (EN && !A && B) |-> (Y == 4'b0010)
    );

    // When enabled and A=1, B=0, the output selects bit 2.
    check_decode_10: assert property (
        @($global_clock) (EN && A && !B) |-> (Y == 4'b0100)
    );

    // When enabled and A=1, B=1, the output selects bit 3.
    check_decode_11: assert property (
        @($global_clock) (EN && A && B) |-> (Y == 4'b1000)
    );

    // The output is always one-hot or zero when enabled.
    check_enabled_onehot0: assert property (
        @($global_clock) EN |-> $onehot0(Y)
    );

    // The output is always within the implemented decode values.
    check_valid_output_values: assert property (
        @($global_clock) (Y == 4'b0000) || (Y == 4'b0001) || (Y == 4'b0010) || (Y == 4'b0100) || (Y == 4'b1000)
    );

endmodule