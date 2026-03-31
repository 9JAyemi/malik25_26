module decoder_2to4_with_enable_sva (
    input logic A,
    input logic B,
    input logic EN,
    input logic [3:0] Y
);

    // When disabled, the output must be zero.
    check_disabled_forces_zero: assert property (
        @($global_clock) (!EN) |-> (Y == 4'b0000)
    );

    // When enabled and A=0 and B=0, Y must be 0001.
    check_decode_00: assert property (
        @($global_clock) (EN && !A && !B) |-> (Y == 4'b0001)
    );

    // When enabled and A=0 and B=1, Y must be 0010.
    check_decode_01: assert property (
        @($global_clock) (EN && !A && B) |-> (Y == 4'b0010)
    );

    // When enabled and A=1 and B=0, Y must be 0100.
    check_decode_10: assert property (
        @($global_clock) (EN && A && !B) |-> (Y == 4'b0100)
    );

    // When enabled and A=1 and B=1, Y must be 1000.
    check_decode_11: assert property (
        @($global_clock) (EN && A && B) |-> (Y == 4'b1000)
    );

    // When enabled, Y must be one-hot.
    check_enabled_onehot: assert property (
        @($global_clock) EN |-> $onehot(Y)
    );

    // When enabled, Y must be one of the four valid decode values.
    check_enabled_valid_values: assert property (
        @($global_clock) EN |-> ((Y == 4'b0001) || (Y == 4'b0010) || (Y == 4'b0100) || (Y == 4'b1000))
    );

endmodule